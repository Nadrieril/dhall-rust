use std::borrow::Cow;
use std::cell::{Ref, RefCell, RefMut};
use std::rc::Rc;

use dhall_syntax::{Const, ExprF};

use crate::core::context::TypecheckContext;
use crate::core::valuef::ValueF;
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

#[derive(Debug, Clone)]
enum ValueInternal {
    /// Partially normalized value whose subexpressions have been thunked (this is returned from
    /// typechecking). Note that this is different from `ValueF::PartialExpr` because there is no
    /// requirement of WHNF here.
    PartialExpr(ExprF<Value, Normalized>),
    /// Partially normalized value.
    /// Invariant: if the marker is `NF`, the value must be fully normalized
    ValueF(Marker, ValueF),
}

#[derive(Debug)]
struct TypedValueInternal {
    internal: ValueInternal,
    typ: Option<Type>,
}

/// Stores a possibly unevaluated value. Gets (partially) normalized on-demand,
/// sharing computation automatically. Uses a RefCell to share computation.
/// Can optionally store a Type from typechecking to preserve type information through
/// normalization.
#[derive(Clone)]
pub struct Value(Rc<RefCell<TypedValueInternal>>);

#[derive(Debug, Clone)]
pub struct TypedValue(Value);

impl ValueInternal {
    fn into_value(self, t: Option<Type>) -> Value {
        TypedValueInternal {
            internal: self,
            typ: t,
        }
        .into_value()
    }

    fn normalize_whnf(&mut self) {
        match self {
            ValueInternal::PartialExpr(e) => {
                *self =
                    ValueInternal::ValueF(WHNF, normalize_one_layer(e.clone()))
            }
            // Already at least in WHNF
            ValueInternal::ValueF(_, _) => {}
        }
    }

    fn normalize_nf(&mut self) {
        match self {
            ValueInternal::PartialExpr(_) => {
                self.normalize_whnf();
                self.normalize_nf();
            }
            ValueInternal::ValueF(m @ WHNF, v) => {
                v.normalize_mut();
                *m = NF;
            }
            // Already in NF
            ValueInternal::ValueF(NF, _) => {}
        }
    }

    // Always use normalize_whnf before
    fn as_whnf(&self) -> &ValueF {
        match self {
            ValueInternal::PartialExpr(_) => unreachable!(),
            ValueInternal::ValueF(_, v) => v,
        }
    }

    // Always use normalize_nf before
    fn as_nf(&self) -> &ValueF {
        match self {
            ValueInternal::PartialExpr(_) | ValueInternal::ValueF(WHNF, _) => {
                unreachable!()
            }
            ValueInternal::ValueF(NF, v) => v,
        }
    }
}

impl TypedValueInternal {
    fn into_value(self) -> Value {
        Value(Rc::new(RefCell::new(self)))
    }
    fn as_internal(&self) -> &ValueInternal {
        &self.internal
    }
    fn as_internal_mut(&mut self) -> &mut ValueInternal {
        &mut self.internal
    }

    fn get_type(&self) -> Result<Type, TypeError> {
        match &self.typ {
            Some(t) => Ok(t.clone()),
            None => Err(TypeError::new(
                &TypecheckContext::new(),
                TypeMessage::Untyped,
            )),
        }
    }
}

impl Value {
    pub(crate) fn from_valuef(v: ValueF) -> Value {
        ValueInternal::ValueF(WHNF, v).into_value(None)
    }
    pub(crate) fn from_valuef_and_type(v: ValueF, t: Type) -> Value {
        ValueInternal::ValueF(WHNF, v).into_value(Some(t))
    }
    pub(crate) fn from_partial_expr(e: ExprF<Value, Normalized>) -> Value {
        ValueInternal::PartialExpr(e).into_value(None)
    }
    pub(crate) fn with_type(self, t: Type) -> Value {
        self.as_internal().clone().into_value(Some(t))
    }

    /// Mutates the contents. If no one else shares this thunk,
    /// mutates directly, thus avoiding a RefCell lock.
    fn mutate_internal(&mut self, f: impl FnOnce(&mut TypedValueInternal)) {
        match Rc::get_mut(&mut self.0) {
            // Mutate directly if sole owner
            Some(refcell) => f(RefCell::get_mut(refcell)),
            // Otherwise mutate through the refcell
            None => f(&mut self.as_tinternal_mut()),
        }
    }

    /// Normalizes contents to normal form; faster than `normalize_nf` if
    /// no one else shares this thunk
    pub(crate) fn normalize_mut(&mut self) {
        self.mutate_internal(|i| i.as_internal_mut().normalize_nf())
    }

    fn as_tinternal(&self) -> Ref<TypedValueInternal> {
        self.0.borrow()
    }
    fn as_tinternal_mut(&mut self) -> RefMut<TypedValueInternal> {
        self.0.borrow_mut()
    }
    fn as_internal(&self) -> Ref<ValueInternal> {
        Ref::map(self.as_tinternal(), TypedValueInternal::as_internal)
    }
    fn as_internal_mut(&self) -> RefMut<ValueInternal> {
        RefMut::map(self.0.borrow_mut(), TypedValueInternal::as_internal_mut)
    }

    fn do_normalize_whnf(&self) {
        let borrow = self.as_internal();
        match &*borrow {
            ValueInternal::PartialExpr(_) => {
                drop(borrow);
                self.as_internal_mut().normalize_whnf();
            }
            // Already at least in WHNF
            ValueInternal::ValueF(_, _) => {}
        }
    }

    fn do_normalize_nf(&self) {
        let borrow = self.as_internal();
        match &*borrow {
            ValueInternal::PartialExpr(_) | ValueInternal::ValueF(WHNF, _) => {
                drop(borrow);
                self.as_internal_mut().normalize_nf();
            }
            // Already in NF
            ValueInternal::ValueF(NF, _) => {}
        }
    }

    // WARNING: avoid normalizing any thunk while holding on to this ref
    // or you could run into BorrowMut panics
    pub(crate) fn normalize_nf(&self) -> Ref<ValueF> {
        self.do_normalize_nf();
        Ref::map(self.as_internal(), ValueInternal::as_nf)
    }

    // WARNING: avoid normalizing any thunk while holding on to this ref
    // or you could run into BorrowMut panics
    pub(crate) fn as_valuef(&self) -> Ref<ValueF> {
        self.do_normalize_whnf();
        Ref::map(self.as_internal(), ValueInternal::as_whnf)
    }

    pub(crate) fn to_valuef(&self) -> ValueF {
        self.as_valuef().clone()
    }

    pub(crate) fn normalize_to_expr_maybe_alpha(
        &self,
        alpha: bool,
    ) -> OutputSubExpr {
        self.normalize_nf().normalize_to_expr_maybe_alpha(alpha)
    }

    pub(crate) fn app_valuef(&self, val: ValueF) -> ValueF {
        self.app_value(val.into_value())
    }

    pub(crate) fn app_value(&self, th: Value) -> ValueF {
        apply_any(self.clone(), th)
    }

    pub(crate) fn get_type(&self) -> Result<Cow<'_, Type>, TypeError> {
        Ok(Cow::Owned(self.as_tinternal().get_type()?))
    }
}

impl TypedValue {
    pub(crate) fn from_valuef(v: ValueF) -> TypedValue {
        TypedValue::from_value_untyped(Value::from_valuef(v))
    }

    pub(crate) fn from_type(t: Type) -> TypedValue {
        t.into_typedvalue()
    }

    pub(crate) fn normalize_nf(&self) -> ValueF {
        self.0.normalize_nf().clone()
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

    pub(crate) fn from_value_and_type(th: Value, t: Type) -> Self {
        TypedValue(th.with_type(t))
    }
    pub fn from_value_simple_type(th: Value) -> Self {
        TypedValue::from_value_and_type(th, Type::const_type())
    }
    pub(crate) fn from_value_untyped(th: Value) -> Self {
        TypedValue(th)
    }
    pub(crate) fn from_const(c: Const) -> Self {
        match type_of_const(c) {
            Ok(t) => TypedValue::from_valuef_and_type(ValueF::Const(c), t),
            Err(_) => TypedValue::from_valuef(ValueF::Const(c)),
        }
    }
    pub(crate) fn from_valuef_and_type(v: ValueF, t: Type) -> Self {
        TypedValue(Value::from_valuef_and_type(v, t))
    }

    pub(crate) fn to_valuef(&self) -> ValueF {
        self.0.to_valuef()
    }
    pub(crate) fn to_expr(&self) -> NormalizedSubExpr {
        self.to_valuef().normalize_to_expr()
    }
    pub(crate) fn to_expr_alpha(&self) -> NormalizedSubExpr {
        self.to_valuef().normalize_to_expr_maybe_alpha(true)
    }
    pub(crate) fn to_value(&self) -> Value {
        self.0.clone()
    }
    pub(crate) fn to_type(&self) -> Type {
        self.clone().into_typed().into_type()
    }
    pub(crate) fn into_typed(self) -> Typed {
        Typed::from_typedvalue(self)
    }
    pub(crate) fn as_const(&self) -> Option<Const> {
        // TODO: avoid clone
        match &self.to_valuef() {
            ValueF::Const(c) => Some(*c),
            _ => None,
        }
    }

    pub(crate) fn normalize_mut(&mut self) {
        self.0.normalize_mut()
    }

    pub(crate) fn get_type(&self) -> Result<Cow<'_, Type>, TypeError> {
        self.0.get_type()
    }
}

impl Shift for Value {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(Value(self.0.shift(delta, var)?))
    }
}

impl Shift for ValueInternal {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(match self {
            ValueInternal::PartialExpr(e) => {
                ValueInternal::PartialExpr(e.shift(delta, var)?)
            }
            ValueInternal::ValueF(m, v) => {
                ValueInternal::ValueF(*m, v.shift(delta, var)?)
            }
        })
    }
}

impl Shift for TypedValue {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(TypedValue(self.0.shift(delta, var)?))
    }
}

impl Shift for TypedValueInternal {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(TypedValueInternal {
            internal: self.internal.shift(delta, var)?,
            typ: self.typ.shift(delta, var)?,
        })
    }
}

impl Subst<Typed> for Value {
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        Value(self.0.subst_shift(var, val))
    }
}

impl Subst<Typed> for ValueInternal {
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        match self {
            ValueInternal::PartialExpr(e) => {
                ValueInternal::PartialExpr(e.subst_shift(var, val))
            }
            ValueInternal::ValueF(_, v) => {
                // The resulting value may not stay in normal form after substitution
                ValueInternal::ValueF(WHNF, v.subst_shift(var, val))
            }
        }
    }
}

impl Subst<Typed> for TypedValueInternal {
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        TypedValueInternal {
            internal: self.internal.subst_shift(var, val),
            typ: self.typ.subst_shift(var, val),
        }
    }
}

impl Subst<Typed> for TypedValue {
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        TypedValue(self.0.subst_shift(var, val))
    }
}

impl std::cmp::PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        *self.as_valuef() == *other.as_valuef()
    }
}
impl std::cmp::Eq for Value {}

impl std::cmp::PartialEq for TypedValue {
    fn eq(&self, other: &Self) -> bool {
        self.to_valuef() == other.to_valuef()
    }
}
impl std::cmp::Eq for TypedValue {}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let b: &ValueInternal = &self.as_internal();
        match b {
            ValueInternal::ValueF(m, v) => {
                f.debug_tuple(&format!("Value@{:?}", m)).field(v).finish()
            }
            ValueInternal::PartialExpr(e) => {
                f.debug_tuple("Value@PartialExpr").field(e).finish()
            }
        }
    }
}
