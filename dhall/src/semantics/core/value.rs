use std::cell::{Ref, RefCell, RefMut};
use std::rc::Rc;

use crate::semantics::core::context::TypecheckContext;
use crate::semantics::core::value_kind::ValueKind;
use crate::semantics::core::var::{AlphaVar, Shift, Subst};
use crate::semantics::error::{TypeError, TypeMessage};
use crate::semantics::phase::normalize::{apply_any, normalize_whnf};
use crate::semantics::phase::typecheck::{builtin_to_value, const_to_value};
use crate::semantics::phase::{NormalizedExpr, Typed};
use crate::syntax::{Builtin, Const, Span};

#[derive(Debug, Clone, Copy)]
pub(crate) enum Form {
    /// No constraints; expression may not be normalized at all.
    Unevaled,
    /// Weak Head Normal Form, i.e. normalized up to the first constructor, but subexpressions may
    /// not be normalized. This means that the first constructor of the contained ValueKind is the first
    /// constructor of the final Normal Form (NF).
    WHNF,
    /// Normal Form, i.e. completely normalized.
    /// When all the Values in a ValueKind are at least in WHNF, and recursively so, then the
    /// ValueKind is in NF. This is because WHNF ensures that we have the first constructor of the NF; so
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
    kind: ValueKind,
    /// This is None if and only if `value` is `Sort` (which doesn't have a type)
    ty: Option<Value>,
    span: Span,
}

/// Stores a possibly unevaluated value. Gets (partially) normalized on-demand,
/// sharing computation automatically. Uses a RefCell to share computation.
/// Can optionally store a type from typechecking to preserve type information.
#[derive(Clone)]
pub(crate) struct Value(Rc<RefCell<ValueInternal>>);

#[derive(Copy, Clone)]
/// Controls conversion from `Value` to `Expr`
pub(crate) struct ToExprOptions {
    /// Whether to convert all variables to `_`
    pub(crate) alpha: bool,
    /// Whether to normalize before converting
    pub(crate) normalize: bool,
}

impl ValueInternal {
    fn into_value(self) -> Value {
        Value(Rc::new(RefCell::new(self)))
    }
    fn as_kind(&self) -> &ValueKind {
        &self.kind
    }

    fn normalize_whnf(&mut self) {
        take_mut::take_or_recover(
            self,
            // Dummy value in case the other closure panics
            || ValueInternal {
                form: Unevaled,
                kind: ValueKind::Const(Const::Type),
                ty: None,
                span: Span::Artificial,
            },
            |vint| match (&vint.form, &vint.ty) {
                (Unevaled, Some(ty)) => ValueInternal {
                    form: WHNF,
                    kind: normalize_whnf(vint.kind, &ty),
                    ty: vint.ty,
                    span: vint.span,
                },
                // `value` is `Sort`
                (Unevaled, None) => ValueInternal {
                    form: NF,
                    kind: ValueKind::Const(Const::Sort),
                    ty: None,
                    span: vint.span,
                },
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
                self.kind.normalize_mut();
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
    fn new(kind: ValueKind, form: Form, ty: Value, span: Span) -> Value {
        ValueInternal {
            form,
            kind,
            ty: Some(ty),
            span,
        }
        .into_value()
    }
    pub(crate) fn const_sort() -> Value {
        ValueInternal {
            form: NF,
            kind: ValueKind::Const(Const::Sort),
            ty: None,
            span: Span::Artificial,
        }
        .into_value()
    }
    pub(crate) fn from_kind_and_type(v: ValueKind, t: Value) -> Value {
        Value::new(v, Unevaled, t, Span::Artificial)
    }
    pub(crate) fn from_kind_and_type_and_span(
        v: ValueKind,
        t: Value,
        span: Span,
    ) -> Value {
        Value::new(v, Unevaled, t, span)
    }
    pub(crate) fn from_kind_and_type_whnf(v: ValueKind, t: Value) -> Value {
        Value::new(v, WHNF, t, Span::Artificial)
    }
    pub(crate) fn from_const(c: Const) -> Self {
        const_to_value(c)
    }
    pub(crate) fn from_builtin(b: Builtin) -> Self {
        builtin_to_value(b)
    }
    pub(crate) fn with_span(self, span: Span) -> Self {
        self.as_internal_mut().span = span;
        self
    }

    pub(crate) fn as_const(&self) -> Option<Const> {
        match &*self.as_whnf() {
            ValueKind::Const(c) => Some(*c),
            _ => None,
        }
    }
    pub(crate) fn span(&self) -> Span {
        self.as_internal().span.clone()
    }

    fn as_internal(&self) -> Ref<ValueInternal> {
        self.0.borrow()
    }
    fn as_internal_mut(&self) -> RefMut<ValueInternal> {
        self.0.borrow_mut()
    }
    /// WARNING: The returned ValueKind may be entirely unnormalized, in aprticular it may just be an
    /// unevaled PartialExpr. You probably want to use `as_whnf`.
    fn as_kind(&self) -> Ref<ValueKind> {
        Ref::map(self.as_internal(), ValueInternal::as_kind)
    }
    /// This is what you want if you want to pattern-match on the value.
    /// WARNING: drop this ref before normalizing the same value or you will run into BorrowMut
    /// panics.
    pub(crate) fn as_whnf(&self) -> Ref<ValueKind> {
        self.normalize_whnf();
        self.as_kind()
    }

    pub(crate) fn to_expr(&self, opts: ToExprOptions) -> NormalizedExpr {
        if opts.normalize {
            self.normalize_whnf();
        }
        self.as_kind().to_expr(opts)
    }
    pub(crate) fn to_whnf_ignore_type(&self) -> ValueKind {
        self.as_whnf().clone()
    }
    /// Before discarding type information, check that it matches the expected return type.
    pub(crate) fn to_whnf_check_type(&self, ty: &Value) -> ValueKind {
        self.check_type(ty);
        self.to_whnf_ignore_type()
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

    pub(crate) fn app(&self, v: Value) -> Value {
        let body_t = match &*self.get_type_not_sort().as_whnf() {
            ValueKind::Pi(x, t, e) => {
                v.check_type(t);
                e.subst_shift(&x.into(), &v)
            }
            _ => unreachable!("Internal type error"),
        };
        Value::from_kind_and_type_whnf(
            apply_any(self.clone(), v, &body_t),
            body_t,
        )
    }

    /// In debug mode, panic if the provided type doesn't match the value's type.
    /// Otherwise does nothing.
    pub(crate) fn check_type(&self, ty: &Value) {
        debug_assert_eq!(
            Some(ty),
            self.get_type().ok().as_ref(),
            "Internal type error"
        );
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

impl Shift for Value {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(Value(self.0.shift(delta, var)?))
    }
}

impl Shift for ValueInternal {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(ValueInternal {
            form: self.form,
            kind: self.kind.shift(delta, var)?,
            ty: self.ty.shift(delta, var)?,
            span: self.span.clone(),
        })
    }
}

impl Subst<Value> for Value {
    fn subst_shift(&self, var: &AlphaVar, val: &Value) -> Self {
        match &*self.as_kind() {
            // If the var matches, we can just reuse the provided value instead of copying it.
            // We also check that the types match, if in debug mode.
            ValueKind::Var(v) if v == var => {
                if let Ok(self_ty) = self.get_type() {
                    val.check_type(&self_ty.subst_shift(var, val));
                }
                val.clone()
            }
            _ => Value(self.0.subst_shift(var, val)),
        }
    }
}

impl Subst<Value> for ValueInternal {
    fn subst_shift(&self, var: &AlphaVar, val: &Value) -> Self {
        ValueInternal {
            // The resulting value may not stay in wnhf after substitution
            form: Unevaled,
            kind: self.kind.subst_shift(var, val),
            ty: self.ty.subst_shift(var, val),
            span: self.span.clone(),
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
        if let ValueKind::Const(c) = &vint.kind {
            write!(fmt, "{:?}", c)
        } else {
            let mut x = fmt.debug_struct(&format!("Value@{:?}", &vint.form));
            x.field("value", &vint.kind);
            if let Some(ty) = vint.ty.as_ref() {
                x.field("type", &ty);
            } else {
                x.field("type", &None::<()>);
            }
            x.finish()
        }
    }
}
