use std::cell::{Ref, RefCell, RefMut};
use std::collections::HashMap;
use std::rc::Rc;

use crate::error::{TypeError, TypeMessage};
use crate::semantics::core::context::TyCtx;
use crate::semantics::core::var::{AlphaVar, Binder};
use crate::semantics::phase::normalize::{apply_any, normalize_whnf};
use crate::semantics::phase::typecheck::{builtin_to_value, const_to_value};
use crate::semantics::phase::{Normalized, NormalizedExpr, Typed};
use crate::semantics::to_expr;
use crate::syntax::{
    Builtin, Const, ExprKind, Integer, InterpolatedTextContents, Label,
    NaiveDouble, Natural, Span,
};

use self::Form::{Unevaled, NF, WHNF};

/// Stores a possibly unevaluated value. Gets (partially) normalized on-demand, sharing computation
/// automatically. Uses a RefCell to share computation.
/// Can optionally store a type from typechecking to preserve type information.
/// If you compare for equality two `Value`s in WHNF, then equality will be up to alpha-equivalence
/// (renaming of bound variables) and beta-equivalence (normalization). It will recursively
/// normalize as needed.
#[derive(Clone)]
pub(crate) struct Value(Rc<RefCell<ValueInternal>>);

/// Invariant: if `form` is `WHNF`, `value` must be in Weak Head Normal Form
/// Invariant: if `form` is `NF`, `value` must be fully normalized
#[derive(Debug)]
struct ValueInternal {
    form: Form,
    kind: ValueKind<Value>,
    /// This is None if and only if `value` is `Sort` (which doesn't have a type)
    ty: Option<Value>,
    span: Span,
}

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ValueKind<Value> {
    /// Closures
    Lam(Binder, Value, Value),
    Pi(Binder, Value, Value),
    // Invariant: in whnf, the evaluation must not be able to progress further.
    AppliedBuiltin(Builtin, Vec<Value>),

    Var(AlphaVar),
    Const(Const),
    BoolLit(bool),
    NaturalLit(Natural),
    IntegerLit(Integer),
    DoubleLit(NaiveDouble),
    EmptyOptionalLit(Value),
    NEOptionalLit(Value),
    // EmptyListLit(t) means `[] : List t`, not `[] : t`
    EmptyListLit(Value),
    NEListLit(Vec<Value>),
    RecordType(HashMap<Label, Value>),
    RecordLit(HashMap<Label, Value>),
    UnionType(HashMap<Label, Option<Value>>),
    UnionConstructor(Label, HashMap<Label, Option<Value>>),
    UnionLit(Label, Value, HashMap<Label, Option<Value>>),
    // Invariant: in whnf, this must not contain interpolations that are themselves TextLits, and
    // contiguous text values must be merged.
    TextLit(Vec<InterpolatedTextContents<Value>>),
    Equivalence(Value, Value),
    // Invariant: in whnf, this must not contain a value captured by one of the variants above.
    PartialExpr(ExprKind<Value, Normalized>),
}

impl Value {
    fn new(kind: ValueKind<Value>, form: Form, ty: Value, span: Span) -> Value {
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
    pub(crate) fn from_kind_and_type(v: ValueKind<Value>, t: Value) -> Value {
        Value::new(v, Unevaled, t, Span::Artificial)
    }
    pub(crate) fn from_kind_and_type_and_span(
        v: ValueKind<Value>,
        t: Value,
        span: Span,
    ) -> Value {
        Value::new(v, Unevaled, t, span)
    }
    pub(crate) fn from_kind_and_type_whnf(
        v: ValueKind<Value>,
        t: Value,
    ) -> Value {
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
    /// WARNING: The returned ValueKind may be entirely unnormalized, in particular it may just be an
    /// unevaled PartialExpr. You probably want to use `as_whnf`.
    pub(crate) fn as_kind(&self) -> Ref<ValueKind<Value>> {
        Ref::map(self.as_internal(), ValueInternal::as_kind)
    }
    /// This is what you want if you want to pattern-match on the value.
    /// WARNING: drop this ref before normalizing the same value or you will run into BorrowMut
    /// panics.
    pub(crate) fn as_whnf(&self) -> Ref<ValueKind<Value>> {
        self.normalize_whnf();
        self.as_kind()
    }

    /// Converts a value back to the corresponding AST expression.
    pub(crate) fn to_expr(
        &self,
        opts: to_expr::ToExprOptions,
    ) -> NormalizedExpr {
        to_expr::value_to_expr(self, opts, &vec![])
    }
    pub(crate) fn to_whnf_ignore_type(&self) -> ValueKind<Value> {
        self.as_whnf().clone()
    }
    /// Before discarding type information, check that it matches the expected return type.
    pub(crate) fn to_whnf_check_type(&self, ty: &Value) -> ValueKind<Value> {
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
    pub(crate) fn normalize_nf(&self) {
        self.as_internal_mut().normalize_nf();
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

    pub(crate) fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(self.as_internal().shift(delta, var)?.into_value())
    }
    pub(crate) fn over_binder<T>(&self, x: T) -> Option<Self>
    where
        T: Into<AlphaVar>,
    {
        self.shift(-1, &x.into())
    }
    pub(crate) fn under_binder<T>(&self, x: T) -> Self
    where
        T: Into<AlphaVar>,
    {
        // Can't fail since delta is positive
        self.shift(1, &x.into()).unwrap()
    }
    pub(crate) fn subst_shift(&self, var: &AlphaVar, val: &Value) -> Self {
        match &*self.as_kind() {
            // If the var matches, we can just reuse the provided value instead of copying it.
            // We also check that the types match, if in debug mode.
            ValueKind::Var(v) if v == var => {
                if let Ok(self_ty) = self.get_type() {
                    val.check_type(&self_ty.subst_shift(var, val));
                }
                val.clone()
            }
            _ => self.as_internal().subst_shift(var, val).into_value(),
        }
    }
    // pub(crate) fn subst_ctx(&self, ctx: &TyCtx) -> Self {
    //     match &*self.as_kind() {
    //         ValueKind::Var(var) => match ctx.lookup_alpha(var) {
    //             Some(val) => val,
    //             None => unreachable!("Internal type error"),
    //         },
    //         kind => {
    //             let kind = kind.map_ref_with_special_handling_of_binders(
    //                 |x| x.subst_ctx(ctx),
    //                 |b, t, x| x.subst_ctx(&ctx.insert_type(b, t.clone())),
    //             );
    //             ValueInternal {
    //                 form: Unevaled,
    //                 kind,
    //                 ty: self.as_internal().ty.clone(),
    //                 span: self.as_internal().span.clone(),
    //             }
    //             .into_value()
    //         }
    //     }
    // }
}

impl ValueInternal {
    fn into_value(self) -> Value {
        Value(Rc::new(RefCell::new(self)))
    }
    fn as_kind(&self) -> &ValueKind<Value> {
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
            None => Err(TypeError::new(&TyCtx::new(), TypeMessage::Sort)),
        }
    }

    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(ValueInternal {
            form: self.form,
            kind: self.kind.shift(delta, var)?,
            ty: match &self.ty {
                None => None,
                Some(ty) => Some(ty.shift(delta, var)?),
            },
            span: self.span.clone(),
        })
    }
    fn subst_shift(&self, var: &AlphaVar, val: &Value) -> Self {
        ValueInternal {
            // The resulting value may not stay in wnhf after substitution
            form: Unevaled,
            kind: self.kind.subst_shift(var, val),
            ty: self.ty.as_ref().map(|x| x.subst_shift(var, val)),
            span: self.span.clone(),
        }
    }
}

impl ValueKind<Value> {
    pub(crate) fn into_value_with_type(self, t: Value) -> Value {
        Value::from_kind_and_type(self, t)
    }

    pub(crate) fn normalize_mut(&mut self) {
        match self {
            ValueKind::Var(_)
            | ValueKind::Const(_)
            | ValueKind::BoolLit(_)
            | ValueKind::NaturalLit(_)
            | ValueKind::IntegerLit(_)
            | ValueKind::DoubleLit(_) => {}

            ValueKind::EmptyOptionalLit(tth) | ValueKind::EmptyListLit(tth) => {
                tth.normalize_mut();
            }

            ValueKind::NEOptionalLit(th) => {
                th.normalize_mut();
            }
            ValueKind::Lam(_, t, e) => {
                t.normalize_mut();
                e.normalize_mut();
            }
            ValueKind::Pi(_, t, e) => {
                t.normalize_mut();
                e.normalize_mut();
            }
            ValueKind::AppliedBuiltin(_, args) => {
                for x in args.iter_mut() {
                    x.normalize_mut();
                }
            }
            ValueKind::NEListLit(elts) => {
                for x in elts.iter_mut() {
                    x.normalize_mut();
                }
            }
            ValueKind::RecordLit(kvs) => {
                for x in kvs.values_mut() {
                    x.normalize_mut();
                }
            }
            ValueKind::RecordType(kvs) => {
                for x in kvs.values_mut() {
                    x.normalize_mut();
                }
            }
            ValueKind::UnionType(kts) | ValueKind::UnionConstructor(_, kts) => {
                for x in kts.values_mut().flat_map(|opt| opt) {
                    x.normalize_mut();
                }
            }
            ValueKind::UnionLit(_, v, kts) => {
                v.normalize_mut();
                for x in kts.values_mut().flat_map(|opt| opt) {
                    x.normalize_mut();
                }
            }
            ValueKind::TextLit(elts) => {
                for x in elts.iter_mut() {
                    x.map_mut(Value::normalize_mut);
                }
            }
            ValueKind::Equivalence(x, y) => {
                x.normalize_mut();
                y.normalize_mut();
            }
            ValueKind::PartialExpr(e) => {
                e.map_mut(Value::normalize_mut);
            }
        }
    }

    pub(crate) fn from_builtin(b: Builtin) -> ValueKind<Value> {
        ValueKind::AppliedBuiltin(b, vec![])
    }

    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(match self {
            ValueKind::Var(v) => ValueKind::Var(v.shift(delta, var)?),
            _ => self.traverse_ref_with_special_handling_of_binders(
                |x| Ok(x.shift(delta, var)?),
                |b, _, x| Ok(x.shift(delta, &var.under_binder(b))?),
            )?,
        })
    }
    fn subst_shift(&self, var: &AlphaVar, val: &Value) -> Self {
        match self {
            ValueKind::Var(v) if v == var => val.to_whnf_ignore_type(),
            ValueKind::Var(v) => ValueKind::Var(v.over_binder(var).unwrap()),
            _ => self.map_ref_with_special_handling_of_binders(
                |x| x.subst_shift(var, val),
                |b, _, x| {
                    x.subst_shift(&var.under_binder(b), &val.under_binder(b))
                },
            ),
        }
    }
}

impl<V> ValueKind<V> {
    pub(crate) fn traverse_ref_with_special_handling_of_binders<'a, V2, E>(
        &'a self,
        visit_val: impl FnMut(&'a V) -> Result<V2, E>,
        visit_under_binder: impl for<'b> FnMut(
            &'a Binder,
            &'b V,
            &'a V,
        ) -> Result<V2, E>,
    ) -> Result<ValueKind<V2>, E> {
        use crate::semantics::visitor;
        use visitor::ValueKindVisitor;
        visitor::TraverseRefWithBindersVisitor {
            visit_val,
            visit_under_binder,
        }
        .visit(self)
    }

    pub(crate) fn map_ref_with_special_handling_of_binders<'a, V2>(
        &'a self,
        mut map_val: impl FnMut(&'a V) -> V2,
        mut map_under_binder: impl for<'b> FnMut(&'a Binder, &'b V, &'a V) -> V2,
    ) -> ValueKind<V2> {
        use crate::syntax::trivial_result;
        trivial_result(self.traverse_ref_with_special_handling_of_binders(
            |x| Ok(map_val(x)),
            |l, t, x| Ok(map_under_binder(l, t, x)),
        ))
    }

    #[allow(dead_code)]
    pub(crate) fn map_ref<'a, V2>(
        &'a self,
        map_val: impl Fn(&'a V) -> V2,
    ) -> ValueKind<V2> {
        self.map_ref_with_special_handling_of_binders(&map_val, |_, _, x| {
            map_val(x)
        })
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
