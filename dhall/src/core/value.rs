use std::borrow::Cow;
use std::cell::{Ref, RefCell, RefMut};
use std::rc::Rc;

use dhall_syntax::{Const, ExprF};

use crate::core::context::TypecheckContext;
use crate::core::valuef::ValueF;
use crate::core::var::{AlphaVar, Shift, Subst};
use crate::error::{TypeError, TypeMessage};
use crate::phase::normalize::{apply_any, normalize_whnf, OutputSubExpr};
use crate::phase::typecheck::type_of_const;
use crate::phase::{Normalized, NormalizedSubExpr, Type, Typed};

#[derive(Debug, Clone, Copy)]
enum Form {
    /// No constraints; expression may not be normalized at all.
    Unevaled,
    /// Weak Head Normal Form, i.e. normalized up to the first constructor, but subexpressions may
    /// not be normalized. This means that the first constructor of the contained ValueF is the first
    /// constructor of the final Normal Form (NF).
    WHNF,
    /// Normal Form, i.e. completely normalized.
    /// When all the Values in a ValueF are at least in WHNF, and recursively so, then the
    /// ValueF is in NF. This is because WHNF ensures that we have the first constructor of the NF; so
    /// if we have the first constructor of the NF at all levels, we actually have the NF.
    NF,
}
use Form::{Unevaled, NF, WHNF};

#[derive(Debug, Clone)]
/// Partially normalized value.
/// Invariant: if `form` is `WHNF`, `value` must be in Weak Head Normal Form
/// Invariant: if `form` is `NF`, `value` must be fully normalized
struct ValueInternal {
    form: Form,
    value: ValueF,
    ty: Option<Type>,
}

/// Stores a possibly unevaluated value. Gets (partially) normalized on-demand,
/// sharing computation automatically. Uses a RefCell to share computation.
/// Can optionally store a Type from typechecking to preserve type information through
/// normalization.
#[derive(Clone)]
pub struct Value(Rc<RefCell<ValueInternal>>);

/// A value that needs to carry a type for typechecking to work.
/// TODO: actually enforce this.
#[derive(Debug, Clone)]
pub struct TypedValue(Value);

impl ValueInternal {
    fn into_value(self) -> Value {
        Value(Rc::new(RefCell::new(self)))
    }

    fn normalize_whnf(&mut self) {
        take_mut::take(self, |vint| match &vint.form {
            Unevaled => ValueInternal {
                form: WHNF,
                value: normalize_whnf(vint.value),
                ty: vint.ty,
            },
            // Already in WHNF
            WHNF | NF => vint,
        })
    }
    fn normalize_nf(&mut self) {
        match self.form {
            Unevaled => {
                self.normalize_whnf();
                self.normalize_nf();
            }
            WHNF => {
                self.value.normalize_mut();
                self.form = NF;
            }
            // Already in NF
            NF => {}
        }
    }

    /// Always use normalize_whnf before
    fn as_whnf(&self) -> &ValueF {
        match self.form {
            Unevaled => unreachable!(),
            _ => &self.value,
        }
    }
    /// Always use normalize_nf before
    fn as_nf(&self) -> &ValueF {
        match self.form {
            Unevaled | WHNF => unreachable!(),
            NF => &self.value,
        }
    }

    fn get_type(&self) -> Result<&Type, TypeError> {
        match &self.ty {
            Some(t) => Ok(t),
            None => Err(TypeError::new(
                &TypecheckContext::new(),
                TypeMessage::Untyped,
            )),
        }
    }
}

impl Value {
    pub(crate) fn from_valuef(v: ValueF) -> Value {
        ValueInternal {
            form: Unevaled,
            value: v,
            ty: None,
        }
        .into_value()
    }
    pub(crate) fn from_valuef_and_type(v: ValueF, t: Type) -> Value {
        ValueInternal {
            form: Unevaled,
            value: v,
            ty: Some(t),
        }
        .into_value()
    }
    pub(crate) fn from_partial_expr(e: ExprF<Value, Normalized>) -> Value {
        Value::from_valuef(ValueF::PartialExpr(e))
    }
    // TODO: avoid using this function
    pub(crate) fn with_type(self, t: Type) -> Value {
        let vint = self.as_internal();
        ValueInternal {
            form: vint.form,
            value: vint.value.clone(),
            ty: Some(t),
        }
        .into_value()
    }

    /// Mutates the contents. If no one else shares this thunk,
    /// mutates directly, thus avoiding a RefCell lock.
    fn mutate_internal(&mut self, f: impl FnOnce(&mut ValueInternal)) {
        match Rc::get_mut(&mut self.0) {
            // Mutate directly if sole owner
            Some(refcell) => f(RefCell::get_mut(refcell)),
            // Otherwise mutate through the refcell
            None => f(&mut self.as_internal_mut()),
        }
    }

    /// Normalizes contents to normal form; faster than `normalize_nf` if
    /// no one else shares this thunk.
    pub(crate) fn normalize_mut(&mut self) {
        self.mutate_internal(|vint| vint.normalize_nf())
    }

    fn as_internal(&self) -> Ref<ValueInternal> {
        self.0.borrow()
    }
    fn as_internal_mut(&self) -> RefMut<ValueInternal> {
        self.0.borrow_mut()
    }

    fn do_normalize_whnf(&self) {
        let borrow = self.as_internal();
        match borrow.form {
            Unevaled => {
                drop(borrow);
                self.as_internal_mut().normalize_whnf();
            }
            // Already at least in WHNF
            WHNF | NF => {}
        }
    }

    fn do_normalize_nf(&self) {
        let borrow = self.as_internal();
        match borrow.form {
            Unevaled | WHNF => {
                drop(borrow);
                self.as_internal_mut().normalize_nf();
            }
            // Already in NF
            NF => {}
        }
    }

    // WARNING: avoid normalizing any thunk while holding on to this ref
    // or you could run into BorrowMut panics
    pub(crate) fn normalize_nf(&self) -> Ref<ValueF> {
        self.do_normalize_nf();
        Ref::map(self.as_internal(), ValueInternal::as_nf)
    }

    /// WARNING: avoid normalizing any thunk while holding on to this ref
    /// or you could run into BorrowMut panics
    /// TODO: deprecated because of misleading name
    pub(crate) fn as_valuef(&self) -> Ref<ValueF> {
        self.as_whnf()
    }

    /// WARNING: avoid normalizing any thunk while holding on to this ref
    /// or you could run into BorrowMut panics
    pub(crate) fn as_whnf(&self) -> Ref<ValueF> {
        self.do_normalize_whnf();
        Ref::map(self.as_internal(), ValueInternal::as_whnf)
    }

    /// TODO: deprecated because of misleading name
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
        Ok(Cow::Owned(self.as_internal().get_type()?.clone()))
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
        Some(ValueInternal {
            form: self.form,
            value: self.value.shift(delta, var)?,
            ty: self.ty.shift(delta, var)?,
        })
    }
}

impl Shift for TypedValue {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(TypedValue(self.0.shift(delta, var)?))
    }
}

impl Subst<Typed> for Value {
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        Value(self.0.subst_shift(var, val))
    }
}

impl Subst<Typed> for ValueInternal {
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        ValueInternal {
            // The resulting value may not stay in wnhf after substitution
            form: Unevaled,
            value: self.value.subst_shift(var, val),
            ty: self.ty.subst_shift(var, val),
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
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let vint: &ValueInternal = &self.as_internal();
        fmt.debug_tuple(&format!("Value@{:?}", &vint.form))
            .field(&vint.value)
            .finish()
    }
}
