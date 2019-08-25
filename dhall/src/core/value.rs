use std::cell::{Ref, RefCell, RefMut};
use std::rc::Rc;

use dhall_syntax::{Builtin, Const};

use crate::core::context::TypecheckContext;
use crate::core::valuef::ValueF;
use crate::core::var::{AlphaVar, Shift, Subst};
use crate::error::{TypeError, TypeMessage};
use crate::phase::normalize::{apply_any, normalize_whnf};
use crate::phase::typecheck::{builtin_to_value, const_to_value};
use crate::phase::{NormalizedSubExpr, Typed};

#[derive(Debug, Clone, Copy)]
pub(crate) enum Form {
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

/// Partially normalized value.
/// Invariant: if `form` is `WHNF`, `value` must be in Weak Head Normal Form
/// Invariant: if `form` is `NF`, `value` must be fully normalized
#[derive(Debug)]
struct ValueInternal {
    form: Form,
    value: ValueF,
    /// This is None if and only if `value` is `Sort` (which doesn't have a type)
    ty: Option<Value>,
}

/// Stores a possibly unevaluated value. Gets (partially) normalized on-demand,
/// sharing computation automatically. Uses a RefCell to share computation.
/// Can optionally store a type from typechecking to preserve type information.
#[derive(Clone)]
pub(crate) struct Value(Rc<RefCell<ValueInternal>>);

/// When a function needs to return either a freshly created ValueF or an existing Value, but
/// doesn't want to convert both to the same thing, either to avoid unnecessary allocations or to
/// avoid loss of typ information.
#[derive(Debug, Clone)]
pub(crate) enum VoVF {
    Value(Value),
    ValueF { val: ValueF, form: Form },
}

impl ValueInternal {
    fn into_value(self) -> Value {
        Value(Rc::new(RefCell::new(self)))
    }
    fn as_valuef(&self) -> &ValueF {
        &self.value
    }

    fn normalize_whnf(&mut self) {
        take_mut::take_or_recover(
            self,
            // Dummy value in case the other closure panics
            || ValueInternal {
                form: Unevaled,
                value: ValueF::Const(Const::Type),
                ty: None,
            },
            |vint| match (&vint.form, &vint.ty) {
                (Unevaled, None) => ValueInternal {
                    form: NF,
                    value: ValueF::Const(Const::Sort),
                    ty: None,
                },
                (Unevaled, Some(ty)) => {
                    let new_value =
                        normalize_whnf(vint.value, &ty).into_whnf(&ty);
                    ValueInternal {
                        form: WHNF,
                        value: new_value,
                        ty: vint.ty,
                    }
                }
                // Already in WHNF
                (WHNF, _) | (NF, _) => vint,
            },
        )
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
            None => {
                Err(TypeError::new(&TypecheckContext::new(), TypeMessage::Sort))
            }
        }
    }
}

impl Value {
    pub(crate) fn new(value: ValueF, form: Form, ty: Option<Value>) -> Value {
        ValueInternal { form, value, ty }.into_value()
    }
    // TODO: this is very wrong
    pub(crate) fn from_valuef_untyped(v: ValueF) -> Value {
        Value::new(v, Unevaled, None)
    }
    pub(crate) fn const_sort() -> Value {
        Value::new(ValueF::Const(Const::Sort), NF, None)
    }
    pub(crate) fn from_valuef_and_type(v: ValueF, t: Value) -> Value {
        Value::new(v, Unevaled, Some(t))
    }
    pub(crate) fn from_const(c: Const) -> Self {
        const_to_value(c)
    }
    pub(crate) fn from_builtin(b: Builtin) -> Self {
        builtin_to_value(b)
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
    pub(crate) fn into_vovf(self) -> VoVF {
        VoVF::Value(self)
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
    ) -> NormalizedSubExpr {
        self.as_nf().normalize_to_expr_maybe_alpha(alpha)
    }

    pub(crate) fn app(&self, v: Value) -> Value {
        let t = self.get_type_not_sort();
        let vovf = apply_any(self.clone(), v.clone(), &t);
        let t_borrow = t.as_whnf();
        match &*t_borrow {
            ValueF::Pi(x, _, e) => {
                let t = e.subst_shift(&x.into(), &v);
                vovf.into_value_with_type(t)
            }
            _ => unreachable!("Internal type error"),
        }
    }

    pub(crate) fn get_type(&self) -> Result<Value, TypeError> {
        Ok(self.as_internal().get_type()?.clone())
    }
    /// When we know the value isn't `Sort`, this gets the type directly
    pub(crate) fn get_type_not_sort(&self) -> Value {
        self.get_type()
            .expect("Internal type error: value is `Sort` but shouldn't be")
    }
}

impl VoVF {
    pub(crate) fn into_whnf(self, ty: &Value) -> ValueF {
        match self {
            VoVF::ValueF {
                val,
                form: Unevaled,
            } => normalize_whnf(val, ty).into_whnf(ty),
            // Already at lest in WHNF
            VoVF::ValueF { val, .. } => val,
            VoVF::Value(v) => {
                let v_ty = v.get_type().ok();
                debug_assert_eq!(
                    Some(ty),
                    v_ty.as_ref(),
                    "The type recovered from normalization doesn't match the stored type."
                );
                v.to_whnf()
            }
        }
    }
    pub(crate) fn into_value_with_type(self, ty: Value) -> Value {
        match self {
            VoVF::Value(v) => {
                let v_ty = v.get_type().ok();
                debug_assert_eq!(
                    Some(&ty),
                    v_ty.as_ref(),
                    "The type recovered from normalization doesn't match the stored type."
                );
                v
            }
            VoVF::ValueF { val, form } => Value::new(val, form, Some(ty)),
        }
    }

    pub(crate) fn app(self, x: Value) -> VoVF {
        VoVF::Value(match self {
            VoVF::Value(v) => v.app(x),
            // TODO: this is very wrong
            VoVF::ValueF { val, .. } => Value::from_valuef_untyped(val).app(x),
        })
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
