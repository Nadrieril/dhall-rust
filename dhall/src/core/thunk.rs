use std::cell::{Ref, RefCell};
use std::rc::Rc;

use crate::core::context::NormalizationContext;
use crate::core::context::TypecheckContext;
use crate::core::value::{AlphaVar, Value};
use crate::error::TypeError;
use crate::phase::normalize::{
    apply_any, normalize_whnf, InputSubExpr, OutputSubExpr,
};
use crate::phase::typecheck::mktype;
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
pub(crate) enum TypeThunk {
    Thunk(Thunk),
    Type(Type),
}

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
            // Already at least in WHNF
            ThunkInternal::Value(_, _) => {}
        }
    }

    fn normalize_nf(&mut self) {
        match self {
            ThunkInternal::Unnormalized(_, _) => {
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
            ThunkInternal::Unnormalized(_, _) => unreachable!(),
            ThunkInternal::Value(_, v) => v,
        }
    }

    // Always use normalize_nf before
    fn as_nf(&self) -> &Value {
        match self {
            ThunkInternal::Unnormalized(_, _) => unreachable!(),
            ThunkInternal::Value(WHNF, _) => unreachable!(),
            ThunkInternal::Value(NF, v) => v,
        }
    }

    fn shift(&self, delta: isize, var: &AlphaVar) -> Self {
        match self {
            ThunkInternal::Unnormalized(ctx, e) => {
                ThunkInternal::Unnormalized(ctx.shift(delta, var), e.clone())
            }
            ThunkInternal::Value(m, v) => {
                ThunkInternal::Value(*m, v.shift(delta, var))
            }
        }
    }

    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        match self {
            ThunkInternal::Unnormalized(ctx, e) => ThunkInternal::Unnormalized(
                ctx.subst_shift(var, val),
                e.clone(),
            ),
            ThunkInternal::Value(_, v) => {
                // The resulting value may not stay in normal form after substitution
                ThunkInternal::Value(WHNF, v.subst_shift(var, val))
            }
        }
    }
}

impl Thunk {
    pub(crate) fn new(ctx: NormalizationContext, e: InputSubExpr) -> Thunk {
        ThunkInternal::Unnormalized(ctx, e).into_thunk()
    }

    pub(crate) fn from_value(v: Value) -> Thunk {
        ThunkInternal::Value(WHNF, v).into_thunk()
    }

    pub(crate) fn from_normalized_expr(e: OutputSubExpr) -> Thunk {
        Thunk::new(NormalizationContext::new(), e.absurd())
    }

    // Normalizes contents to normal form; faster than `normalize_nf` if
    // no one else shares this thunk
    pub(crate) fn normalize_mut(&mut self) {
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
            ThunkInternal::Unnormalized(_, _) => {
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
    pub(crate) fn normalize_nf(&self) -> Ref<Value> {
        self.do_normalize_nf();
        Ref::map(self.0.borrow(), ThunkInternal::as_nf)
    }

    // WARNING: avoid normalizing any thunk while holding on to this ref
    // or you could run into BorrowMut panics
    pub(crate) fn as_value(&self) -> Ref<Value> {
        self.do_normalize_whnf();
        Ref::map(self.0.borrow(), ThunkInternal::as_whnf)
    }

    pub(crate) fn to_value(&self) -> Value {
        self.as_value().clone()
    }

    pub(crate) fn normalize_to_expr(&self) -> OutputSubExpr {
        self.normalize_to_expr_maybe_alpha(false)
    }

    pub(crate) fn normalize_to_expr_maybe_alpha(
        &self,
        alpha: bool,
    ) -> OutputSubExpr {
        self.normalize_nf().normalize_to_expr_maybe_alpha(alpha)
    }

    pub(crate) fn app_val(&self, val: Value) -> Value {
        self.app_thunk(val.into_thunk())
    }

    pub(crate) fn app_thunk(&self, th: Thunk) -> Value {
        apply_any(self.clone(), th)
    }

    pub(crate) fn shift(&self, delta: isize, var: &AlphaVar) -> Self {
        self.0.borrow().shift(delta, var).into_thunk()
    }

    pub(crate) fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        self.0.borrow().subst_shift(var, val).into_thunk()
    }
}

impl TypeThunk {
    pub(crate) fn from_value(v: Value) -> TypeThunk {
        TypeThunk::from_thunk(Thunk::from_value(v))
    }

    pub(crate) fn from_thunk(th: Thunk) -> TypeThunk {
        TypeThunk::Thunk(th)
    }

    pub(crate) fn from_type(t: Type) -> TypeThunk {
        TypeThunk::Type(t)
    }

    pub(crate) fn normalize_mut(&mut self) {
        match self {
            TypeThunk::Thunk(th) => th.normalize_mut(),
            TypeThunk::Type(_) => {}
        }
    }

    pub(crate) fn normalize_nf(&self) -> Value {
        match self {
            TypeThunk::Thunk(th) => th.normalize_nf().clone(),
            TypeThunk::Type(t) => t.to_value().normalize(),
        }
    }

    pub(crate) fn to_value(&self) -> Value {
        match self {
            TypeThunk::Thunk(th) => th.to_value(),
            TypeThunk::Type(t) => t.to_value(),
        }
    }

    pub(crate) fn to_type(
        &self,
        ctx: &TypecheckContext,
    ) -> Result<Type, TypeError> {
        match self {
            TypeThunk::Type(t) => Ok(t.clone()),
            TypeThunk::Thunk(th) => {
                // TODO: rule out statically
                mktype(ctx, th.normalize_to_expr().absurd())
            }
        }
    }

    pub(crate) fn normalize_to_expr_maybe_alpha(
        &self,
        alpha: bool,
    ) -> OutputSubExpr {
        self.normalize_nf().normalize_to_expr_maybe_alpha(alpha)
    }

    pub(crate) fn shift(&self, delta: isize, var: &AlphaVar) -> Self {
        match self {
            TypeThunk::Thunk(th) => TypeThunk::Thunk(th.shift(delta, var)),
            TypeThunk::Type(t) => TypeThunk::Type(t.shift(delta, var)),
        }
    }

    pub(crate) fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        match self {
            TypeThunk::Thunk(th) => TypeThunk::Thunk(th.subst_shift(var, val)),
            TypeThunk::Type(t) => TypeThunk::Type(t.subst_shift(var, val)),
        }
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
