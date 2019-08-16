use std::borrow::Cow;
use std::cell::{Ref, RefCell};
use std::rc::Rc;

use dhall_syntax::{Const, ExprF};

use crate::core::context::TypecheckContext;
use crate::core::value::Value;
use crate::core::var::{AlphaVar, Shift, Subst};
use crate::error::{TypeError, TypeMessage};
use crate::phase::normalize::{apply_any, normalize_one_layer, OutputSubExpr};
use crate::phase::typecheck::type_of_const;
use crate::phase::{Normalized, NormalizedSubExpr, Type, Typed};

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
    /// Partially normalized value whose subexpressions have been thunked (this is returned from
    /// typechecking). Note that this is different from `Value::PartialExpr` because there is no
    /// requirement of WHNF here.
    PartialExpr(ExprF<Thunk, Normalized>),
    /// Partially normalized value.
    /// Invariant: if the marker is `NF`, the value must be fully normalized
    Value(Marker, Value),
}

/// Stores a possibly unevaluated value. Gets (partially) normalized on-demand,
/// sharing computation automatically.
/// Uses a RefCell to share computation.
#[derive(Clone)]
pub struct Thunk(Rc<RefCell<ThunkInternal>>);

/// A thunk in type position. Can optionally store a Type from the typechecking phase to preserve
/// type information through the normalization phase.
#[derive(Debug, Clone)]
pub enum TypedThunk {
    // Any value, along with (optionally) its type
    Untyped(Thunk),
    Typed(Thunk, Box<Type>),
    // One of the base higher-kinded types.
    // Used to avoid storing the same tower ot Type->Kind->Sort
    // over and over again. Also enables having Sort as a value
    // even though it doesn't itself have a type.
    Const(Const),
}

impl ThunkInternal {
    fn into_thunk(self) -> Thunk {
        Thunk(Rc::new(RefCell::new(self)))
    }

    fn normalize_whnf(&mut self) {
        match self {
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
            ThunkInternal::PartialExpr(_) => {
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
            ThunkInternal::PartialExpr(_) => unreachable!(),
            ThunkInternal::Value(_, v) => v,
        }
    }

    // Always use normalize_nf before
    fn as_nf(&self) -> &Value {
        match self {
            ThunkInternal::PartialExpr(_) | ThunkInternal::Value(WHNF, _) => {
                unreachable!()
            }
            ThunkInternal::Value(NF, v) => v,
        }
    }
}

impl Thunk {
    pub(crate) fn from_value(v: Value) -> Thunk {
        ThunkInternal::Value(WHNF, v).into_thunk()
    }

    pub(crate) fn from_partial_expr(e: ExprF<Thunk, Normalized>) -> Thunk {
        ThunkInternal::PartialExpr(e).into_thunk()
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
            ThunkInternal::PartialExpr(_) => {
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
            ThunkInternal::PartialExpr(_) | ThunkInternal::Value(WHNF, _) => {
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
}

impl TypedThunk {
    pub(crate) fn from_value(v: Value) -> TypedThunk {
        TypedThunk::from_thunk(Thunk::from_value(v))
    }

    pub fn from_thunk(th: Thunk) -> TypedThunk {
        TypedThunk::from_thunk_untyped(th)
    }

    pub(crate) fn from_type(t: Type) -> TypedThunk {
        t.into_typethunk()
    }

    pub(crate) fn normalize_nf(&self) -> Value {
        match self {
            TypedThunk::Const(c) => Value::Const(*c),
            TypedThunk::Untyped(thunk) | TypedThunk::Typed(thunk, _) => {
                thunk.normalize_nf().clone()
            }
        }
    }

    pub(crate) fn to_typed(&self) -> Typed {
        self.clone().into_typed()
    }

    pub(crate) fn normalize_to_expr_maybe_alpha(
        &self,
        alpha: bool,
    ) -> OutputSubExpr {
        self.normalize_nf().normalize_to_expr_maybe_alpha(alpha)
    }

    pub(crate) fn from_thunk_and_type(th: Thunk, t: Type) -> Self {
        TypedThunk::Typed(th, Box::new(t))
    }
    pub(crate) fn from_thunk_untyped(th: Thunk) -> Self {
        TypedThunk::Untyped(th)
    }
    pub(crate) fn from_const(c: Const) -> Self {
        TypedThunk::Const(c)
    }
    pub(crate) fn from_value_untyped(v: Value) -> Self {
        TypedThunk::from_thunk_untyped(Thunk::from_value(v))
    }

    // TODO: Avoid cloning if possible
    pub(crate) fn to_value(&self) -> Value {
        match self {
            TypedThunk::Untyped(th) | TypedThunk::Typed(th, _) => th.to_value(),
            TypedThunk::Const(c) => Value::Const(*c),
        }
    }
    pub(crate) fn to_expr(&self) -> NormalizedSubExpr {
        self.to_value().normalize_to_expr()
    }
    pub(crate) fn to_expr_alpha(&self) -> NormalizedSubExpr {
        self.to_value().normalize_to_expr_maybe_alpha(true)
    }
    pub(crate) fn to_thunk(&self) -> Thunk {
        match self {
            TypedThunk::Untyped(th) | TypedThunk::Typed(th, _) => th.clone(),
            TypedThunk::Const(c) => Thunk::from_value(Value::Const(*c)),
        }
    }
    pub(crate) fn to_type(&self) -> Type {
        self.clone().into_typed().into_type()
    }
    pub(crate) fn into_typed(self) -> Typed {
        Typed::from_typethunk(self)
    }
    pub(crate) fn as_const(&self) -> Option<Const> {
        // TODO: avoid clone
        match &self.to_value() {
            Value::Const(c) => Some(*c),
            _ => None,
        }
    }

    pub(crate) fn normalize_mut(&mut self) {
        match self {
            TypedThunk::Untyped(th) | TypedThunk::Typed(th, _) => {
                th.normalize_mut()
            }
            TypedThunk::Const(_) => {}
        }
    }

    pub(crate) fn get_type(&self) -> Result<Cow<'_, Type>, TypeError> {
        match self {
            TypedThunk::Untyped(_) => Err(TypeError::new(
                &TypecheckContext::new(),
                TypeMessage::Untyped,
            )),
            TypedThunk::Typed(_, t) => Ok(Cow::Borrowed(t)),
            TypedThunk::Const(c) => Ok(Cow::Owned(type_of_const(*c)?)),
        }
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
            ThunkInternal::PartialExpr(e) => ThunkInternal::PartialExpr(
                e.traverse_ref_with_special_handling_of_binders(
                    |v| Ok(v.shift(delta, var)?),
                    |x, v| Ok(v.shift(delta, &var.under_binder(x))?),
                )?,
            ),
            ThunkInternal::Value(m, v) => {
                ThunkInternal::Value(*m, v.shift(delta, var)?)
            }
        })
    }
}

impl Shift for TypedThunk {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(match self {
            TypedThunk::Untyped(th) => {
                TypedThunk::Untyped(th.shift(delta, var)?)
            }
            TypedThunk::Typed(th, t) => TypedThunk::Typed(
                th.shift(delta, var)?,
                Box::new(t.shift(delta, var)?),
            ),
            TypedThunk::Const(c) => TypedThunk::Const(*c),
        })
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
            ThunkInternal::PartialExpr(e) => ThunkInternal::PartialExpr(
                e.map_ref_with_special_handling_of_binders(
                    |v| v.subst_shift(var, val),
                    |x, v| {
                        v.subst_shift(
                            &var.under_binder(x),
                            &val.under_binder(x),
                        )
                    },
                ),
            ),
            ThunkInternal::Value(_, v) => {
                // The resulting value may not stay in normal form after substitution
                ThunkInternal::Value(WHNF, v.subst_shift(var, val))
            }
        }
    }
}

impl Subst<Typed> for TypedThunk {
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        match self {
            TypedThunk::Untyped(th) => {
                TypedThunk::Untyped(th.subst_shift(var, val))
            }
            TypedThunk::Typed(th, t) => TypedThunk::Typed(
                th.subst_shift(var, val),
                Box::new(t.subst_shift(var, val)),
            ),
            TypedThunk::Const(c) => TypedThunk::Const(*c),
        }
    }
}

impl std::cmp::PartialEq for Thunk {
    fn eq(&self, other: &Self) -> bool {
        *self.as_value() == *other.as_value()
    }
}
impl std::cmp::Eq for Thunk {}

impl std::cmp::PartialEq for TypedThunk {
    fn eq(&self, other: &Self) -> bool {
        self.to_value() == other.to_value()
    }
}
impl std::cmp::Eq for TypedThunk {}

impl std::fmt::Debug for Thunk {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let b: &ThunkInternal = &self.0.borrow();
        match b {
            ThunkInternal::Value(m, v) => {
                f.debug_tuple(&format!("Thunk@{:?}", m)).field(v).finish()
            }
            ThunkInternal::PartialExpr(e) => {
                f.debug_tuple("Thunk@PartialExpr").field(e).finish()
            }
        }
    }
}
