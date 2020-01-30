use std::cell::{Ref, RefCell, RefMut};
use std::collections::HashMap;
use std::rc::Rc;

use crate::error::{TypeError, TypeMessage};
use crate::semantics::core::var::Binder;
use crate::semantics::phase::normalize::{apply_any, normalize_whnf};
use crate::semantics::phase::{Normalized, NormalizedExpr, ToExprOptions};
use crate::semantics::{type_of_builtin, TyExpr, TyExprKind};
use crate::semantics::{BuiltinClosure, NzEnv, NzVar, VarEnv};
use crate::syntax::{
    BinOp, Builtin, Const, ExprKind, Integer, InterpolatedTextContents, Label,
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

#[derive(Debug, Clone)]
pub(crate) enum Closure {
    /// Normal closure
    Closure {
        arg_ty: Value,
        env: NzEnv,
        body: TyExpr,
    },
    /// Closure that ignores the argument passed
    ConstantClosure { env: NzEnv, body: TyExpr },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ValueKind<Value> {
    /// Closures
    LamClosure {
        binder: Binder,
        annot: Value,
        closure: Closure,
    },
    PiClosure {
        binder: Binder,
        annot: Value,
        closure: Closure,
    },
    // Invariant: in whnf, the evaluation must not be able to progress further.
    AppliedBuiltin(BuiltinClosure<Value>),

    Var(NzVar),
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
    // Also keep the type of the uniontype around
    UnionConstructor(Label, HashMap<Label, Option<Value>>, Value),
    // Also keep the type of the uniontype and the constructor around
    UnionLit(Label, Value, HashMap<Label, Option<Value>>, Value, Value),
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
    pub(crate) fn from_kind_and_type_whnf(
        v: ValueKind<Value>,
        t: Value,
    ) -> Value {
        Value::new(v, WHNF, t, Span::Artificial)
    }
    pub(crate) fn from_const(c: Const) -> Self {
        let v = ValueKind::Const(c);
        match c {
            Const::Type => {
                Value::from_kind_and_type(v, Value::from_const(Const::Kind))
            }
            Const::Kind => {
                Value::from_kind_and_type(v, Value::from_const(Const::Sort))
            }
            Const::Sort => Value::const_sort(),
        }
    }
    pub(crate) fn from_builtin(b: Builtin) -> Self {
        Self::from_builtin_env(b, &NzEnv::new())
    }
    pub(crate) fn from_builtin_env(b: Builtin, env: &NzEnv) -> Self {
        Value::from_kind_and_type(
            ValueKind::from_builtin_env(b, env.clone()),
            crate::semantics::tck::typecheck::typecheck(&type_of_builtin(b))
                .unwrap()
                .normalize_whnf_noenv(),
        )
    }

    pub(crate) fn as_const(&self) -> Option<Const> {
        match &*self.kind() {
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
    pub(crate) fn kind(&self) -> Ref<ValueKind<Value>> {
        self.normalize_whnf();
        self.as_kind()
    }

    /// Converts a value back to the corresponding AST expression.
    pub(crate) fn to_expr(&self, opts: ToExprOptions) -> NormalizedExpr {
        if opts.normalize {
            self.normalize_nf();
        }

        self.to_tyexpr_noenv().to_expr(opts)
    }
    pub(crate) fn to_whnf_ignore_type(&self) -> ValueKind<Value> {
        self.kind().clone()
    }
    /// Before discarding type information, check that it matches the expected return type.
    pub(crate) fn to_whnf_check_type(&self, ty: &Value) -> ValueKind<Value> {
        self.check_type(ty);
        self.to_whnf_ignore_type()
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
        let body_t = match &*self.get_type_not_sort().kind() {
            ValueKind::PiClosure { annot, closure, .. } => {
                v.check_type(annot);
                closure.apply(v.clone())
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
    pub(crate) fn check_type(&self, _ty: &Value) {
        // TODO: reenable
        // debug_assert_eq!(
        //     Some(ty),
        //     self.get_type().ok().as_ref(),
        //     "Internal type error"
        // );
    }
    pub(crate) fn get_type(&self) -> Result<Value, TypeError> {
        Ok(self.as_internal().get_type()?.clone())
    }
    /// When we know the value isn't `Sort`, this gets the type directly
    pub(crate) fn get_type_not_sort(&self) -> Value {
        self.get_type()
            .expect("Internal type error: value is `Sort` but shouldn't be")
    }

    pub fn to_tyexpr(&self, venv: VarEnv) -> TyExpr {
        let tye = match &*self.as_kind() {
            ValueKind::Var(v) => TyExprKind::Var(venv.lookup(v)),
            ValueKind::LamClosure {
                binder,
                annot,
                closure,
            } => TyExprKind::Expr(ExprKind::Lam(
                binder.to_label(),
                annot.to_tyexpr(venv),
                closure
                    .apply_var(NzVar::new(venv.size()))
                    .to_tyexpr(venv.insert()),
            )),
            ValueKind::PiClosure {
                binder,
                annot,
                closure,
            } => TyExprKind::Expr(ExprKind::Pi(
                binder.to_label(),
                annot.to_tyexpr(venv),
                closure
                    .apply_var(NzVar::new(venv.size()))
                    .to_tyexpr(venv.insert()),
            )),
            ValueKind::AppliedBuiltin(closure) => closure.to_tyexprkind(venv),
            ValueKind::UnionConstructor(l, kts, t) => {
                TyExprKind::Expr(ExprKind::Field(
                    TyExpr::new(
                        TyExprKind::Expr(ExprKind::UnionType(
                            kts.into_iter()
                                .map(|(k, v)| {
                                    (
                                        k.clone(),
                                        v.as_ref().map(|v| v.to_tyexpr(venv)),
                                    )
                                })
                                .collect(),
                        )),
                        Some(t.clone()),
                        Span::Artificial,
                    ),
                    l.clone(),
                ))
            }
            ValueKind::UnionLit(l, v, kts, uniont, ctort) => {
                TyExprKind::Expr(ExprKind::App(
                    TyExpr::new(
                        TyExprKind::Expr(ExprKind::Field(
                            TyExpr::new(
                                TyExprKind::Expr(ExprKind::UnionType(
                                    kts.into_iter()
                                        .map(|(k, v)| {
                                            (
                                                k.clone(),
                                                v.as_ref()
                                                    .map(|v| v.to_tyexpr(venv)),
                                            )
                                        })
                                        .collect(),
                                )),
                                Some(uniont.clone()),
                                Span::Artificial,
                            ),
                            l.clone(),
                        )),
                        Some(ctort.clone()),
                        Span::Artificial,
                    ),
                    v.to_tyexpr(venv),
                ))
            }
            self_kind => {
                let self_kind = self_kind.map_ref(|v| v.to_tyexpr(venv));
                let expr = match self_kind {
                    ValueKind::Var(..)
                    | ValueKind::LamClosure { .. }
                    | ValueKind::PiClosure { .. }
                    | ValueKind::AppliedBuiltin(..)
                    | ValueKind::UnionConstructor(..)
                    | ValueKind::UnionLit(..) => unreachable!(),
                    ValueKind::Const(c) => ExprKind::Const(c),
                    ValueKind::BoolLit(b) => ExprKind::BoolLit(b),
                    ValueKind::NaturalLit(n) => ExprKind::NaturalLit(n),
                    ValueKind::IntegerLit(n) => ExprKind::IntegerLit(n),
                    ValueKind::DoubleLit(n) => ExprKind::DoubleLit(n),
                    ValueKind::EmptyOptionalLit(n) => ExprKind::App(
                        Value::from_builtin(Builtin::OptionalNone)
                            .to_tyexpr(venv),
                        n,
                    ),
                    ValueKind::NEOptionalLit(n) => ExprKind::SomeLit(n),
                    ValueKind::EmptyListLit(n) => {
                        ExprKind::EmptyListLit(TyExpr::new(
                            TyExprKind::Expr(ExprKind::App(
                                Value::from_builtin(Builtin::List)
                                    .to_tyexpr(venv),
                                n,
                            )),
                            Some(Value::from_const(Const::Type)),
                            Span::Artificial,
                        ))
                    }
                    ValueKind::NEListLit(elts) => ExprKind::NEListLit(elts),
                    ValueKind::RecordLit(kvs) => {
                        ExprKind::RecordLit(kvs.into_iter().collect())
                    }
                    ValueKind::RecordType(kts) => {
                        ExprKind::RecordType(kts.into_iter().collect())
                    }
                    ValueKind::UnionType(kts) => {
                        ExprKind::UnionType(kts.into_iter().collect())
                    }
                    ValueKind::TextLit(elts) => {
                        ExprKind::TextLit(elts.into_iter().collect())
                    }
                    ValueKind::Equivalence(x, y) => {
                        ExprKind::BinOp(BinOp::Equivalence, x, y)
                    }
                    ValueKind::PartialExpr(e) => e,
                };
                TyExprKind::Expr(expr)
            }
        };

        let self_ty = self.as_internal().ty.clone();
        let self_span = self.as_internal().span.clone();
        TyExpr::new(tye, self_ty, self_span)
    }
    pub fn to_tyexpr_noenv(&self) -> TyExpr {
        self.to_tyexpr(VarEnv::new())
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
        let dummy = ValueInternal {
            form: Unevaled,
            kind: ValueKind::Const(Const::Type),
            ty: None,
            span: Span::Artificial,
        };
        let vint = std::mem::replace(self, dummy);
        *self = match (&vint.form, &vint.ty) {
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
        }
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
            None => Err(TypeError::new(TypeMessage::Sort)),
        }
    }
}

impl ValueKind<Value> {
    pub(crate) fn into_value_with_type(self, t: Value) -> Value {
        Value::from_kind_and_type(self, t)
    }

    pub(crate) fn normalize_mut(&mut self) {
        match self {
            ValueKind::Var(..)
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
            ValueKind::LamClosure { annot, .. }
            | ValueKind::PiClosure { annot, .. } => {
                annot.normalize_mut();
            }
            ValueKind::AppliedBuiltin(closure) => closure.normalize_mut(),
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
            ValueKind::UnionType(kts)
            | ValueKind::UnionConstructor(_, kts, _) => {
                for x in kts.values_mut().flat_map(|opt| opt) {
                    x.normalize_mut();
                }
            }
            ValueKind::UnionLit(_, v, kts, _, _) => {
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
        ValueKind::from_builtin_env(b, NzEnv::new())
    }
    pub(crate) fn from_builtin_env(b: Builtin, env: NzEnv) -> ValueKind<Value> {
        ValueKind::AppliedBuiltin(BuiltinClosure::new(b, env))
    }
}

impl<V> ValueKind<V> {
    fn traverse_ref_with_special_handling_of_binders<'a, V2, E>(
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

    fn map_ref_with_special_handling_of_binders<'a, V2>(
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

    fn map_ref<'a, V2>(
        &'a self,
        map_val: impl Fn(&'a V) -> V2,
    ) -> ValueKind<V2> {
        self.map_ref_with_special_handling_of_binders(&map_val, |_, _, x| {
            map_val(x)
        })
    }
}

impl Closure {
    pub fn new(arg_ty: Value, env: &NzEnv, body: TyExpr) -> Self {
        Closure::Closure {
            arg_ty,
            env: env.clone(),
            body,
        }
    }
    pub fn new_constant(env: &NzEnv, body: TyExpr) -> Self {
        Closure::ConstantClosure {
            env: env.clone(),
            body,
        }
    }
    pub fn apply(&self, val: Value) -> Value {
        match self {
            Closure::Closure { env, body, .. } => {
                body.normalize_whnf(&env.insert_value(val))
            }
            Closure::ConstantClosure { env, body, .. } => {
                body.normalize_whnf(env)
            }
        }
    }
    pub fn apply_var(&self, var: NzVar) -> Value {
        match self {
            Closure::Closure { arg_ty, .. } => {
                let val = Value::from_kind_and_type(
                    ValueKind::Var(var),
                    arg_ty.clone(),
                );
                self.apply(val)
            }
            Closure::ConstantClosure { env, body, .. } => {
                body.normalize_whnf(env)
            }
        }
    }
}

/// Compare two values for equality modulo alpha/beta-equivalence.
// TODO: use Rc comparison to shortcut on identical pointers
impl std::cmp::PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        *self.kind() == *other.kind()
    }
}
impl std::cmp::Eq for Value {}

impl std::cmp::PartialEq for Closure {
    fn eq(&self, other: &Self) -> bool {
        let v = NzVar::fresh();
        self.apply_var(v) == other.apply_var(v)
    }
}
impl std::cmp::Eq for Closure {}

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
