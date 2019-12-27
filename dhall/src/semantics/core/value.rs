use std::borrow::Cow;
use std::cell::{Ref, RefCell, RefMut};
use std::collections::HashMap;
use std::rc::Rc;

use crate::error::{TypeError, TypeMessage};
use crate::semantics::core::context::TyCtx;
use crate::semantics::core::var::{AlphaVar, Binder, Shift, Subst};
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
        to_expr::value_to_expr(self, opts)
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
}

impl<V> ValueKind<V> {
    pub(crate) fn map_ref_with_special_handling_of_binders<'a, V2>(
        &'a self,
        mut map_val: impl FnMut(&'a V) -> V2,
        mut map_under_binder: impl FnMut(&'a Binder, &'a V) -> V2,
    ) -> ValueKind<V2> {
        use crate::semantics::visitor;
        use crate::syntax::trivial_result;
        use visitor::ValueKindVisitor;
        trivial_result(
            visitor::TraverseRefWithBindersVisitor {
                visit_val: |x| Ok(map_val(x)),
                visit_under_binder: |l, x| Ok(map_under_binder(l, x)),
            }
            .visit(self),
        )
    }

    pub(crate) fn map_ref<'a, V2>(
        &'a self,
        map_val: impl Fn(&'a V) -> V2,
    ) -> ValueKind<V2> {
        self.map_ref_with_special_handling_of_binders(&map_val, |_, x| {
            map_val(x)
        })
    }
}

/// Compare two values for equality modulo alpha/beta-equivalence.
// TODO: use Rc comparison to shortcut on identical pointers
fn equiv(val1: &Value, val2: &Value) -> bool {
    struct ValueWithCtx<'v, 'c> {
        val: &'v Value,
        ctx: Cow<'c, Vec<&'v Binder>>,
    }
    impl<'v, 'c> PartialEq for ValueWithCtx<'v, 'c> {
        fn eq(&self, other: &ValueWithCtx<'v, 'c>) -> bool {
            equiv_with_ctx(&*self.ctx, self.val, &*other.ctx, other.val)
        }
    }
    // Push the given context into every subnode of the ValueKind. That way, normal equality of the
    // resulting value will take into account the context.
    fn push_context<'v, 'c>(
        ctx: &'c Vec<&'v Binder>,
        kind: &'v ValueKind<Value>,
    ) -> ValueKind<ValueWithCtx<'v, 'c>> {
        kind.map_ref_with_special_handling_of_binders(
            |val| ValueWithCtx {
                val,
                ctx: Cow::Borrowed(ctx),
            },
            |binder, val| ValueWithCtx {
                val,
                ctx: Cow::Owned(
                    ctx.iter().cloned().chain(Some(binder)).collect(),
                ),
            },
        )
    }

    fn lookup(ctx: &Vec<&Binder>, binder: &Binder) -> Option<usize> {
        ctx.iter()
            .rev()
            .enumerate()
            .find(|(_, other)| binder.same_binder(other))
            .map(|(i, _)| i)
    }

    fn equiv_with_ctx<'v, 'c>(
        ctx1: &'c Vec<&'v Binder>,
        val1: &'v Value,
        ctx2: &'c Vec<&'v Binder>,
        val2: &'v Value,
    ) -> bool {
        use ValueKind::Var;
        let kind1 = val1.as_whnf();
        let kind2 = val2.as_whnf();

        if let (Var(v1), Var(v2)) = (&*kind1, &*kind2) {
            let b1 = v1.binder();
            let b2 = v2.binder();
            if b1.same_binder(&b2) {
                return true;
            }
            match (lookup(ctx1, &b1), lookup(ctx2, &b2)) {
                (Some(i), Some(j)) => i == j,
                _ => false,
            }
        } else {
            push_context(ctx1, &*kind1) == push_context(ctx2, &*kind2)
        }
    }

    equiv_with_ctx(&Vec::new(), val1, &Vec::new(), val2)
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

impl Shift for ValueKind<Value> {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(match self {
            ValueKind::Lam(x, t, e) => ValueKind::Lam(
                x.clone(),
                t.shift(delta, var)?,
                e.shift(delta, &var.under_binder(x))?,
            ),
            ValueKind::AppliedBuiltin(b, args) => {
                ValueKind::AppliedBuiltin(*b, args.shift(delta, var)?)
            }
            ValueKind::Pi(x, t, e) => ValueKind::Pi(
                x.clone(),
                t.shift(delta, var)?,
                e.shift(delta, &var.under_binder(x))?,
            ),
            ValueKind::Var(v) => ValueKind::Var(v.shift(delta, var)?),
            ValueKind::Const(c) => ValueKind::Const(*c),
            ValueKind::BoolLit(b) => ValueKind::BoolLit(*b),
            ValueKind::NaturalLit(n) => ValueKind::NaturalLit(*n),
            ValueKind::IntegerLit(n) => ValueKind::IntegerLit(*n),
            ValueKind::DoubleLit(n) => ValueKind::DoubleLit(*n),
            ValueKind::EmptyOptionalLit(tth) => {
                ValueKind::EmptyOptionalLit(tth.shift(delta, var)?)
            }
            ValueKind::NEOptionalLit(th) => {
                ValueKind::NEOptionalLit(th.shift(delta, var)?)
            }
            ValueKind::EmptyListLit(tth) => {
                ValueKind::EmptyListLit(tth.shift(delta, var)?)
            }
            ValueKind::NEListLit(elts) => {
                ValueKind::NEListLit(elts.shift(delta, var)?)
            }
            ValueKind::RecordLit(kvs) => {
                ValueKind::RecordLit(kvs.shift(delta, var)?)
            }
            ValueKind::RecordType(kvs) => {
                ValueKind::RecordType(kvs.shift(delta, var)?)
            }
            ValueKind::UnionType(kts) => {
                ValueKind::UnionType(kts.shift(delta, var)?)
            }
            ValueKind::UnionConstructor(x, kts) => {
                ValueKind::UnionConstructor(x.clone(), kts.shift(delta, var)?)
            }
            ValueKind::UnionLit(x, v, kts) => ValueKind::UnionLit(
                x.clone(),
                v.shift(delta, var)?,
                kts.shift(delta, var)?,
            ),
            ValueKind::TextLit(elts) => {
                ValueKind::TextLit(elts.shift(delta, var)?)
            }
            ValueKind::Equivalence(x, y) => ValueKind::Equivalence(
                x.shift(delta, var)?,
                y.shift(delta, var)?,
            ),
            ValueKind::PartialExpr(e) => {
                ValueKind::PartialExpr(e.shift(delta, var)?)
            }
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

impl Subst<Value> for ValueKind<Value> {
    fn subst_shift(&self, var: &AlphaVar, val: &Value) -> Self {
        match self {
            ValueKind::AppliedBuiltin(b, args) => {
                ValueKind::AppliedBuiltin(*b, args.subst_shift(var, val))
            }
            ValueKind::PartialExpr(e) => {
                ValueKind::PartialExpr(e.subst_shift(var, val))
            }
            ValueKind::TextLit(elts) => {
                ValueKind::TextLit(elts.subst_shift(var, val))
            }
            ValueKind::Lam(x, t, e) => ValueKind::Lam(
                x.clone(),
                t.subst_shift(var, val),
                e.subst_shift(&var.under_binder(x), &val.under_binder(x)),
            ),
            ValueKind::Pi(x, t, e) => ValueKind::Pi(
                x.clone(),
                t.subst_shift(var, val),
                e.subst_shift(&var.under_binder(x), &val.under_binder(x)),
            ),
            ValueKind::Var(v) if v == var => val.to_whnf_ignore_type(),
            ValueKind::Var(v) => ValueKind::Var(v.shift(-1, var).unwrap()),
            ValueKind::Const(c) => ValueKind::Const(*c),
            ValueKind::BoolLit(b) => ValueKind::BoolLit(*b),
            ValueKind::NaturalLit(n) => ValueKind::NaturalLit(*n),
            ValueKind::IntegerLit(n) => ValueKind::IntegerLit(*n),
            ValueKind::DoubleLit(n) => ValueKind::DoubleLit(*n),
            ValueKind::EmptyOptionalLit(tth) => {
                ValueKind::EmptyOptionalLit(tth.subst_shift(var, val))
            }
            ValueKind::NEOptionalLit(th) => {
                ValueKind::NEOptionalLit(th.subst_shift(var, val))
            }
            ValueKind::EmptyListLit(tth) => {
                ValueKind::EmptyListLit(tth.subst_shift(var, val))
            }
            ValueKind::NEListLit(elts) => {
                ValueKind::NEListLit(elts.subst_shift(var, val))
            }
            ValueKind::RecordLit(kvs) => {
                ValueKind::RecordLit(kvs.subst_shift(var, val))
            }
            ValueKind::RecordType(kvs) => {
                ValueKind::RecordType(kvs.subst_shift(var, val))
            }
            ValueKind::UnionType(kts) => {
                ValueKind::UnionType(kts.subst_shift(var, val))
            }
            ValueKind::UnionConstructor(x, kts) => ValueKind::UnionConstructor(
                x.clone(),
                kts.subst_shift(var, val),
            ),
            ValueKind::UnionLit(x, v, kts) => ValueKind::UnionLit(
                x.clone(),
                v.subst_shift(var, val),
                kts.subst_shift(var, val),
            ),
            ValueKind::Equivalence(x, y) => ValueKind::Equivalence(
                x.subst_shift(var, val),
                y.subst_shift(var, val),
            ),
        }
    }
}

impl std::cmp::PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        equiv(self, other)
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
