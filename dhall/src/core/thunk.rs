use std::cell::{Ref, RefCell};
use std::rc::Rc;

use dhall_syntax::{ExprF, X};

use crate::core::context::NormalizationContext;
use crate::core::value::Value;
use crate::core::var::{AlphaVar, Shift, Subst};
use crate::phase::normalize::{
    apply_any, normalize_one_layer, normalize_whnf, InputSubExpr, OutputSubExpr,
};
use crate::phase::{Type, Typed};

#[derive(Debug, Clone, Copy)]
enum Marker {
    /// Weak Head Normal Form, i.e. subexpressions may not be normalized
    WHNF,
    /// Normal form, i.e. completely normalized
    NF,
}
use Marker::{NF, WHNF};

#[derive(Debug)]
enum ThunkInternal {
    /// Non-normalized value alongside a normalization context
    Unnormalized(NormalizationContext, InputSubExpr),
    /// Partially normalized value whose subexpressions have been thunked (this is returned from
    /// typechecking). Note that this is different from `Value::PartialExpr` because there is no
    /// requirement of WHNF here.
    PartialExpr(ExprF<Thunk, X>),
    /// Partially normalized value.
    /// Invariant: if the marker is `NF`, the value must be fully normalized
    Value(Marker, Value),
}

/// Stores a possibly unevaluated value. Gets (partially) normalized on-demand,
/// sharing computation automatically.
/// Uses a RefCell to share computation.
#[derive(Debug, Clone)]
pub struct Thunk(Rc<RefCell<ThunkInternal>>);

/// A thunk in type position. Can optionally store a Type from the typechecking phase to preserve
/// type information through the normalization phase.
#[derive(Debug, Clone)]
pub struct TypeThunk(Typed);

impl ThunkInternal {
    fn into_thunk(self) -> Thunk {
        Thunk(Rc::new(RefCell::new(self)))
    }

    fn normalize_whnf(&mut self) {
        match self {
            ThunkInternal::Unnormalized(ctx, e) => {
                *self = ThunkInternal::Value(
                    WHNF,
                    normalize_whnf(ctx.clone(), e.clone()),
                )
            }
            ThunkInternal::PartialExpr(e) => {
                *self =
                    ThunkInternal::Value(WHNF, normalize_one_layer(e.clone()))
            }
            // Already at least in WHNF
            ThunkInternal::Value(_, _) => {}
        }
    }

    fn normalize_nf(&mut self) {
        match self {
            ThunkInternal::Unnormalized(_, _)
            | ThunkInternal::PartialExpr(_) => {
                self.normalize_whnf();
                self.normalize_nf();
            }
            ThunkInternal::Value(m @ WHNF, v) => {
                v.normalize_mut();
                *m = NF;
            }
            // Already in NF
            ThunkInternal::Value(NF, _) => {}
        }
    }

    // Always use normalize_whnf before
    fn as_whnf(&self) -> &Value {
        match self {
            ThunkInternal::Unnormalized(_, _)
            | ThunkInternal::PartialExpr(_) => unreachable!(),
            ThunkInternal::Value(_, v) => v,
        }
    }

    // Always use normalize_nf before
    fn as_nf(&self) -> &Value {
        match self {
            ThunkInternal::Unnormalized(_, _)
            | ThunkInternal::PartialExpr(_)
            | ThunkInternal::Value(WHNF, _) => unreachable!(),
            ThunkInternal::Value(NF, v) => v,
        }
    }
}

impl Thunk {
    pub fn new(ctx: NormalizationContext, e: InputSubExpr) -> Thunk {
        ThunkInternal::Unnormalized(ctx, e).into_thunk()
    }

    pub fn from_value(v: Value) -> Thunk {
        ThunkInternal::Value(WHNF, v).into_thunk()
    }

    pub fn from_normalized_expr(e: OutputSubExpr) -> Thunk {
        Thunk::new(NormalizationContext::new(), e.absurd())
    }

    pub fn from_partial_expr(e: ExprF<Thunk, X>) -> Thunk {
        ThunkInternal::PartialExpr(e).into_thunk()
    }

    // Normalizes contents to normal form; faster than `normalize_nf` if
    // no one else shares this thunk
    pub fn normalize_mut(&mut self) {
        match Rc::get_mut(&mut self.0) {
            // Mutate directly if sole owner
            Some(refcell) => RefCell::get_mut(refcell).normalize_nf(),
            // Otherwise mutate through the refcell
            None => self.0.borrow_mut().normalize_nf(),
        }
    }

    fn do_normalize_whnf(&self) {
        let borrow = self.0.borrow();
        match &*borrow {
            ThunkInternal::Unnormalized(_, _)
            | ThunkInternal::PartialExpr(_) => {
                drop(borrow);
                self.0.borrow_mut().normalize_whnf();
            }
            // Already at least in WHNF
            ThunkInternal::Value(_, _) => {}
        }
    }

    fn do_normalize_nf(&self) {
        let borrow = self.0.borrow();
        match &*borrow {
            ThunkInternal::Unnormalized(_, _)
            | ThunkInternal::PartialExpr(_)
            | ThunkInternal::Value(WHNF, _) => {
                drop(borrow);
                self.0.borrow_mut().normalize_nf();
            }
            // Already in NF
            ThunkInternal::Value(NF, _) => {}
        }
    }

    // WARNING: avoid normalizing any thunk while holding on to this ref
    // or you could run into BorrowMut panics
    pub fn normalize_nf(&self) -> Ref<Value> {
        self.do_normalize_nf();
        Ref::map(self.0.borrow(), ThunkInternal::as_nf)
    }

    // WARNING: avoid normalizing any thunk while holding on to this ref
    // or you could run into BorrowMut panics
    pub fn as_value(&self) -> Ref<Value> {
        self.do_normalize_whnf();
        Ref::map(self.0.borrow(), ThunkInternal::as_whnf)
    }

    pub fn to_value(&self) -> Value {
        self.as_value().clone()
    }

    pub fn normalize_to_expr_maybe_alpha(&self, alpha: bool) -> OutputSubExpr {
        self.normalize_nf().normalize_to_expr_maybe_alpha(alpha)
    }

    pub fn app_val(&self, val: Value) -> Value {
        self.app_thunk(val.into_thunk())
    }

    pub fn app_thunk(&self, th: Thunk) -> Value {
        apply_any(self.clone(), th)
    }
}

impl TypeThunk {
    pub fn from_value(v: Value) -> TypeThunk {
        TypeThunk::from_thunk(Thunk::from_value(v))
    }

    pub fn from_thunk(th: Thunk) -> TypeThunk {
        TypeThunk(Typed::from_thunk_untyped(th))
    }

    pub fn from_type(t: Type) -> TypeThunk {
        TypeThunk(t.to_typed())
    }

    pub fn normalize_mut(&mut self) {
        self.0.normalize_mut()
    }

    pub fn normalize_nf(&self) -> Value {
        self.0.to_value().normalize()
    }

    pub fn to_value(&self) -> Value {
        self.0.to_value()
    }

    pub fn to_thunk(&self) -> Thunk {
        self.0.to_thunk()
    }

    pub fn to_type(&self) -> Type {
        self.0.to_type()
    }

    pub fn normalize_to_expr_maybe_alpha(&self, alpha: bool) -> OutputSubExpr {
        self.normalize_nf().normalize_to_expr_maybe_alpha(alpha)
    }
}

impl Shift for Thunk {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(self.0.borrow().shift(delta, var)?.into_thunk())
    }
}

impl Shift for ThunkInternal {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(match self {
            ThunkInternal::Unnormalized(ctx, e) => {
                ThunkInternal::Unnormalized(ctx.shift(delta, var)?, e.clone())
            }
            ThunkInternal::PartialExpr(e) => ThunkInternal::PartialExpr(
                e.traverse_ref_with_special_handling_of_binders(
                    |v| Ok(v.shift(delta, var)?),
                    |x, v| Ok(v.shift(delta, &var.under_binder(x))?),
                    |x| Ok(X::clone(x)),
                )?,
            ),
            ThunkInternal::Value(m, v) => {
                ThunkInternal::Value(*m, v.shift(delta, var)?)
            }
        })
    }
}

impl Shift for TypeThunk {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(TypeThunk(self.0.shift(delta, var)?))
    }
}

impl Subst<Typed> for Thunk {
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        self.0.borrow().subst_shift(var, val).into_thunk()
    }
}

impl Subst<Typed> for ThunkInternal {
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        match self {
            ThunkInternal::Unnormalized(ctx, e) => ThunkInternal::Unnormalized(
                ctx.subst_shift(var, val),
                e.clone(),
            ),
            ThunkInternal::PartialExpr(e) => ThunkInternal::PartialExpr(
                e.map_ref_with_special_handling_of_binders(
                    |v| v.subst_shift(var, val),
                    |x, v| {
                        v.subst_shift(
                            &var.under_binder(x),
                            &val.under_binder(x),
                        )
                    },
                    X::clone,
                ),
            ),
            ThunkInternal::Value(_, v) => {
                // The resulting value may not stay in normal form after substitution
                ThunkInternal::Value(WHNF, v.subst_shift(var, val))
            }
        }
    }
}

impl Subst<Typed> for TypeThunk {
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        TypeThunk(self.0.subst_shift(var, val))
    }
}

impl std::cmp::PartialEq for Thunk {
    fn eq(&self, other: &Self) -> bool {
        &*self.as_value() == &*other.as_value()
    }
}
impl std::cmp::Eq for Thunk {}

impl std::cmp::PartialEq for TypeThunk {
    fn eq(&self, other: &Self) -> bool {
        self.to_value() == other.to_value()
    }
}
impl std::cmp::Eq for TypeThunk {}
