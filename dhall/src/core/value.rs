use std::borrow::Cow;
use std::cell::{Ref, RefCell, RefMut};
use std::rc::Rc;

use dhall_syntax::Const;

use crate::core::context::TypecheckContext;
use crate::core::valuef::ValueF;
use crate::core::var::{AlphaVar, Shift, Subst};
use crate::error::{TypeError, TypeMessage};
use crate::phase::normalize::{apply_any, normalize_whnf, OutputSubExpr};
use crate::phase::typecheck::const_to_value;
use crate::phase::{NormalizedSubExpr, Typed};

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

#[derive(Debug)]
/// Partially normalized value.
/// Invariant: if `form` is `WHNF`, `value` must be in Weak Head Normal Form
/// Invariant: if `form` is `NF`, `value` must be fully normalized
struct ValueInternal {
    form: Form,
    value: ValueF,
    ty: Option<Value>,
}

/// Stores a possibly unevaluated value. Gets (partially) normalized on-demand,
/// sharing computation automatically. Uses a RefCell to share computation.
/// Can optionally store a type from typechecking to preserve type information.
#[derive(Clone)]
pub struct Value(Rc<RefCell<ValueInternal>>);

impl ValueInternal {
    fn into_value(self) -> Value {
        Value(Rc::new(RefCell::new(self)))
    }
    fn as_valuef(&self) -> &ValueF {
        &self.value
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

    fn get_type(&self) -> Result<&Value, TypeError> {
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
    pub(crate) fn from_valuef_untyped(v: ValueF) -> Value {
        ValueInternal {
            form: Unevaled,
            value: v,
            ty: None,
        }
        .into_value()
    }
    pub(crate) fn from_valuef_and_type(v: ValueF, t: Value) -> Value {
        ValueInternal {
            form: Unevaled,
            value: v,
            ty: Some(t),
        }
        .into_value()
    }
    pub(crate) fn from_valuef_simple_type(v: ValueF) -> Value {
        Value::from_valuef_and_type(v, Value::from_const(Const::Type))
    }
    pub(crate) fn from_const(c: Const) -> Self {
        const_to_value(c)
    }
    pub fn const_type() -> Self {
        Value::from_const(Const::Type)
    }

    pub(crate) fn as_const(&self) -> Option<Const> {
        match &*self.as_whnf() {
            ValueF::Const(c) => Some(*c),
            _ => None,
        }
    }

    fn as_internal(&self) -> Ref<ValueInternal> {
        self.0.borrow()
    }
    fn as_internal_mut(&self) -> RefMut<ValueInternal> {
        self.0.borrow_mut()
    }
    /// WARNING: The returned ValueF may be entirely unnormalized, in aprticular it may just be an
    /// unevaled PartialExpr. You probably want to use `as_whnf`.
    fn as_valuef(&self) -> Ref<ValueF> {
        Ref::map(self.as_internal(), ValueInternal::as_valuef)
    }
    /// This is what you want if you want to pattern-match on the value.
    /// WARNING: drop this ref before normalizing the same value or you will run into BorrowMut
    /// panics.
    pub(crate) fn as_whnf(&self) -> Ref<ValueF> {
        self.normalize_whnf();
        self.as_valuef()
    }
    /// WARNING: drop this ref before normalizing the same value or you will run into BorrowMut
    /// panics.
    pub(crate) fn as_nf(&self) -> Ref<ValueF> {
        self.normalize_nf();
        self.as_valuef()
    }

    // TODO: rename `normalize_to_expr`
    pub(crate) fn to_expr(&self) -> NormalizedSubExpr {
        self.as_whnf().normalize_to_expr()
    }
    // TODO: rename `normalize_to_expr_maybe_alpha`
    pub(crate) fn to_expr_alpha(&self) -> NormalizedSubExpr {
        self.as_whnf().normalize_to_expr_maybe_alpha(true)
    }
    /// TODO: cloning a valuef can often be avoided
    pub(crate) fn to_whnf(&self) -> ValueF {
        self.as_whnf().clone()
    }
    pub(crate) fn into_typed(self) -> Typed {
        Typed::from_value(self)
    }

    /// Mutates the contents. If no one else shares this, this avoids a RefCell lock.
    fn mutate_internal(&mut self, f: impl FnOnce(&mut ValueInternal)) {
        match Rc::get_mut(&mut self.0) {
            // Mutate directly if sole owner
            Some(refcell) => f(RefCell::get_mut(refcell)),
            // Otherwise mutate through the refcell
            None => f(&mut self.as_internal_mut()),
        }
    }
    /// Normalizes contents to normal form; faster than `normalize_nf` if
    /// no one else shares this.
    pub(crate) fn normalize_mut(&mut self) {
        self.mutate_internal(|vint| vint.normalize_nf())
    }

    pub(crate) fn normalize_whnf(&self) {
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
    pub(crate) fn normalize_nf(&self) {
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

    pub(crate) fn normalize_to_expr_maybe_alpha(
        &self,
        alpha: bool,
    ) -> OutputSubExpr {
        self.as_nf().normalize_to_expr_maybe_alpha(alpha)
    }

    pub(crate) fn app_value(&self, th: Value) -> ValueF {
        apply_any(self.clone(), th)
    }

    pub(crate) fn get_type(&self) -> Result<Cow<'_, Value>, TypeError> {
        Ok(Cow::Owned(self.as_internal().get_type()?.clone()))
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

impl Subst<Value> for Value {
    fn subst_shift(&self, var: &AlphaVar, val: &Value) -> Self {
        Value(self.0.subst_shift(var, val))
    }
}

impl Subst<Value> for ValueInternal {
    fn subst_shift(&self, var: &AlphaVar, val: &Value) -> Self {
        ValueInternal {
            // The resulting value may not stay in wnhf after substitution
            form: Unevaled,
            value: self.value.subst_shift(var, val),
            ty: self.ty.subst_shift(var, val),
        }
    }
}

// TODO: use Rc comparison to shortcut on identical pointers
impl std::cmp::PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        *self.as_whnf() == *other.as_whnf()
    }
}
impl std::cmp::Eq for Value {}

impl std::fmt::Debug for Value {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let vint: &ValueInternal = &self.as_internal();
        fmt.debug_tuple(&format!("Value@{:?}", &vint.form))
            .field(&vint.value)
            .finish()
    }
}
