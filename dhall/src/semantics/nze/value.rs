use std::collections::HashMap;
use std::rc::Rc;

use crate::semantics::nze::lazy;
use crate::semantics::{
    apply_any, normalize_hir_whnf, normalize_one_layer, squash_textlit, Binder,
    BuiltinClosure, Hir, HirKind, NzEnv, NzVar, TyEnv, VarEnv,
};
use crate::syntax::{
    BinOp, Builtin, Const, ExprKind, InterpolatedTextContents, Label, LitKind,
    Span,
};
use crate::{NormalizedExpr, ToExprOptions};

/// Stores a possibly unevaluated value. Gets (partially) normalized on-demand, sharing computation
/// automatically. Uses a Rc<RefCell> to share computation.
/// If you compare for equality two `Value`s, then equality will be up to alpha-equivalence
/// (renaming of bound variables) and beta-equivalence (normalization). It will recursively
/// normalize as needed.
#[derive(Clone)]
pub(crate) struct Value(Rc<ValueInternal>);

#[derive(Debug)]
struct ValueInternal {
    kind: lazy::Lazy<Thunk, ValueKind>,
    span: Span,
}

/// An unevaluated subexpression
#[derive(Debug, Clone)]
pub(crate) enum Thunk {
    /// A completely unnormalized expression.
    Thunk { env: NzEnv, body: Hir },
    /// A partially normalized expression that may need to go through `normalize_one_layer`.
    PartialExpr { env: NzEnv, expr: ExprKind<Value> },
}

/// An unevaluated subexpression that takes an argument.
#[derive(Debug, Clone)]
pub(crate) enum Closure {
    /// Normal closure
    Closure { env: NzEnv, body: Hir },
    /// Closure that ignores the argument passed
    ConstantClosure { body: Value },
}

/// A text literal with interpolations.
// Invariant: this must not contain interpolations that are themselves TextLits, and contiguous
// text values must be merged.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TextLit(Vec<InterpolatedTextContents<Value>>);

/// This represents a value in Weak Head Normal Form (WHNF). This means that the value is
/// normalized up to the first constructor, but subexpressions may not be fully normalized.
/// When all the Values in a ValueKind are in WHNF, and recursively so, then the ValueKind is in
/// Normal Form (NF). This is because WHNF ensures that we have the first constructor of the NF; so
/// if we have the first constructor of the NF at all levels, we actually have the NF.
/// In particular, this means that once we get a `ValueKind`, it can be considered immutable, and
/// we only need to recursively normalize its sub-`Value`s to get to the NF.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ValueKind {
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
    AppliedBuiltin(BuiltinClosure<Value>),

    Var(NzVar),
    Const(Const),
    Lit(LitKind),
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
    TextLit(TextLit),
    Equivalence(Value, Value),
    /// Invariant: evaluation must not be able to progress with `normalize_one_layer`?
    PartialExpr(ExprKind<Value>),
}

impl Value {
    /// Construct a Value from a completely unnormalized expression.
    pub(crate) fn new_thunk(env: NzEnv, hir: Hir) -> Value {
        let span = hir.span();
        ValueInternal::from_thunk(Thunk::new(env, hir), span).into_value()
    }
    /// Construct a Value from a partially normalized expression that's not in WHNF.
    pub(crate) fn from_partial_expr(e: ExprKind<Value>) -> Value {
        // TODO: env
        let env = NzEnv::new();
        ValueInternal::from_thunk(
            Thunk::from_partial_expr(env, e),
            Span::Artificial,
        )
        .into_value()
    }
    /// Make a Value from a ValueKind
    pub(crate) fn from_kind(v: ValueKind) -> Value {
        ValueInternal::from_whnf(v, Span::Artificial).into_value()
    }
    pub(crate) fn from_const(c: Const) -> Self {
        let v = ValueKind::Const(c);
        ValueInternal::from_whnf(v, Span::Artificial).into_value()
    }
    pub(crate) fn from_builtin(b: Builtin) -> Self {
        Self::from_builtin_env(b, &NzEnv::new())
    }
    pub(crate) fn from_builtin_env(b: Builtin, env: &NzEnv) -> Self {
        Value::from_kind(ValueKind::from_builtin_env(b, env.clone()))
    }
    pub(crate) fn from_text(txt: impl ToString) -> Self {
        Value::from_kind(ValueKind::TextLit(TextLit::from_text(
            txt.to_string(),
        )))
    }

    pub(crate) fn as_const(&self) -> Option<Const> {
        match &*self.kind() {
            ValueKind::Const(c) => Some(*c),
            _ => None,
        }
    }

    /// This is what you want if you want to pattern-match on the value.
    pub(crate) fn kind(&self) -> &ValueKind {
        self.0.kind()
    }

    /// Converts a value back to the corresponding AST expression.
    pub(crate) fn to_expr(&self, opts: ToExprOptions) -> NormalizedExpr {
        if opts.normalize {
            self.normalize();
        }
        self.to_hir_noenv().to_expr(opts)
    }
    pub(crate) fn to_expr_tyenv(&self, tyenv: &TyEnv) -> NormalizedExpr {
        self.to_hir(tyenv.as_varenv()).to_expr_tyenv(tyenv)
    }

    pub(crate) fn normalize(&self) {
        self.0.normalize()
    }

    pub(crate) fn app(&self, v: Value) -> Value {
        Value::from_kind(apply_any(self.clone(), v))
    }

    pub fn to_hir(&self, venv: VarEnv) -> Hir {
        let map_uniontype = |kts: &HashMap<Label, Option<Value>>| {
            ExprKind::UnionType(
                kts.iter()
                    .map(|(k, v)| {
                        (k.clone(), v.as_ref().map(|v| v.to_hir(venv)))
                    })
                    .collect(),
            )
        };

        let hir = match &*self.kind() {
            ValueKind::Var(v) => HirKind::Var(venv.lookup(v)),
            ValueKind::AppliedBuiltin(closure) => closure.to_hirkind(venv),
            self_kind => HirKind::Expr(match self_kind {
                ValueKind::Var(..) | ValueKind::AppliedBuiltin(..) => {
                    unreachable!()
                }
                ValueKind::LamClosure {
                    binder,
                    annot,
                    closure,
                } => ExprKind::Lam(
                    binder.to_label(),
                    annot.to_hir(venv),
                    closure.to_hir(venv),
                ),
                ValueKind::PiClosure {
                    binder,
                    annot,
                    closure,
                } => ExprKind::Pi(
                    binder.to_label(),
                    annot.to_hir(venv),
                    closure.to_hir(venv),
                ),
                ValueKind::Const(c) => ExprKind::Const(*c),
                ValueKind::Lit(l) => ExprKind::Lit(l.clone()),
                ValueKind::EmptyOptionalLit(n) => ExprKind::App(
                    Value::from_builtin(Builtin::OptionalNone).to_hir(venv),
                    n.to_hir(venv),
                ),
                ValueKind::NEOptionalLit(n) => {
                    ExprKind::SomeLit(n.to_hir(venv))
                }
                ValueKind::EmptyListLit(n) => ExprKind::EmptyListLit(Hir::new(
                    HirKind::Expr(ExprKind::App(
                        Value::from_builtin(Builtin::List).to_hir(venv),
                        n.to_hir(venv),
                    )),
                    Span::Artificial,
                )),
                ValueKind::NEListLit(elts) => ExprKind::NEListLit(
                    elts.iter().map(|v| v.to_hir(venv)).collect(),
                ),
                ValueKind::TextLit(elts) => ExprKind::TextLit(
                    elts.iter()
                        .map(|t| t.map_ref(|v| v.to_hir(venv)))
                        .collect(),
                ),
                ValueKind::RecordLit(kvs) => ExprKind::RecordLit(
                    kvs.iter()
                        .map(|(k, v)| (k.clone(), v.to_hir(venv)))
                        .collect(),
                ),
                ValueKind::RecordType(kts) => ExprKind::RecordType(
                    kts.iter()
                        .map(|(k, v)| (k.clone(), v.to_hir(venv)))
                        .collect(),
                ),
                ValueKind::UnionType(kts) => map_uniontype(kts),
                ValueKind::UnionConstructor(l, kts) => ExprKind::Field(
                    Hir::new(
                        HirKind::Expr(map_uniontype(kts)),
                        Span::Artificial,
                    ),
                    l.clone(),
                ),
                ValueKind::UnionLit(l, v, kts) => ExprKind::App(
                    Hir::new(
                        HirKind::Expr(ExprKind::Field(
                            Hir::new(
                                HirKind::Expr(map_uniontype(kts)),
                                Span::Artificial,
                            ),
                            l.clone(),
                        )),
                        Span::Artificial,
                    ),
                    v.to_hir(venv),
                ),
                ValueKind::Equivalence(x, y) => ExprKind::BinOp(
                    BinOp::Equivalence,
                    x.to_hir(venv),
                    y.to_hir(venv),
                ),
                ValueKind::PartialExpr(e) => e.map_ref(|v| v.to_hir(venv)),
            }),
        };

        Hir::new(hir, self.0.span.clone())
    }
    pub fn to_hir_noenv(&self) -> Hir {
        self.to_hir(VarEnv::new())
    }
}

impl ValueInternal {
    fn from_whnf(k: ValueKind, span: Span) -> Self {
        ValueInternal {
            kind: lazy::Lazy::new_completed(k),
            span,
        }
    }
    fn from_thunk(th: Thunk, span: Span) -> Self {
        ValueInternal {
            kind: lazy::Lazy::new(th),
            span,
        }
    }
    fn into_value(self) -> Value {
        Value(Rc::new(self))
    }

    fn kind(&self) -> &ValueKind {
        &self.kind
    }
    fn normalize(&self) {
        self.kind().normalize();
    }
}

impl ValueKind {
    pub(crate) fn into_value(self) -> Value {
        Value::from_kind(self)
    }

    pub(crate) fn normalize(&self) {
        match self {
            ValueKind::Var(..) | ValueKind::Const(_) | ValueKind::Lit(_) => {}

            ValueKind::EmptyOptionalLit(tth) | ValueKind::EmptyListLit(tth) => {
                tth.normalize();
            }

            ValueKind::NEOptionalLit(th) => {
                th.normalize();
            }
            ValueKind::LamClosure { annot, closure, .. }
            | ValueKind::PiClosure { annot, closure, .. } => {
                annot.normalize();
                closure.normalize();
            }
            ValueKind::AppliedBuiltin(closure) => closure.normalize(),
            ValueKind::NEListLit(elts) => {
                for x in elts.iter() {
                    x.normalize();
                }
            }
            ValueKind::RecordLit(kvs) => {
                for x in kvs.values() {
                    x.normalize();
                }
            }
            ValueKind::RecordType(kvs) => {
                for x in kvs.values() {
                    x.normalize();
                }
            }
            ValueKind::UnionType(kts) | ValueKind::UnionConstructor(_, kts) => {
                for x in kts.values().flat_map(|opt| opt) {
                    x.normalize();
                }
            }
            ValueKind::UnionLit(_, v, kts) => {
                v.normalize();
                for x in kts.values().flat_map(|opt| opt) {
                    x.normalize();
                }
            }
            ValueKind::TextLit(tlit) => tlit.normalize(),
            ValueKind::Equivalence(x, y) => {
                x.normalize();
                y.normalize();
            }
            ValueKind::PartialExpr(e) => {
                e.map_ref(Value::normalize);
            }
        }
    }

    pub(crate) fn from_builtin(b: Builtin) -> ValueKind {
        ValueKind::from_builtin_env(b, NzEnv::new())
    }
    pub(crate) fn from_builtin_env(b: Builtin, env: NzEnv) -> ValueKind {
        ValueKind::AppliedBuiltin(BuiltinClosure::new(b, env))
    }
}

impl Thunk {
    fn new(env: NzEnv, body: Hir) -> Self {
        Thunk::Thunk { env, body }
    }
    fn from_partial_expr(env: NzEnv, expr: ExprKind<Value>) -> Self {
        Thunk::PartialExpr { env, expr }
    }
    fn eval(self) -> ValueKind {
        match self {
            Thunk::Thunk { env, body } => normalize_hir_whnf(&env, &body),
            Thunk::PartialExpr { env, expr } => normalize_one_layer(expr, &env),
        }
    }
}

impl Closure {
    pub fn new(env: &NzEnv, body: Hir) -> Self {
        Closure::Closure {
            env: env.clone(),
            body,
        }
    }
    /// New closure that ignores its argument
    pub fn new_constant(body: Value) -> Self {
        Closure::ConstantClosure { body }
    }

    pub fn apply(&self, val: Value) -> Value {
        match self {
            Closure::Closure { env, body, .. } => {
                body.eval(&env.insert_value(val, ()))
            }
            Closure::ConstantClosure { body, .. } => body.clone(),
        }
    }
    fn apply_var(&self, var: NzVar) -> Value {
        match self {
            Closure::Closure { .. } => {
                self.apply(Value::from_kind(ValueKind::Var(var)))
            }
            Closure::ConstantClosure { body, .. } => body.clone(),
        }
    }

    // TODO: somehow normalize the body. Might require to pass an env.
    pub fn normalize(&self) {}

    /// Convert this closure to a Hir expression
    pub fn to_hir(&self, venv: VarEnv) -> Hir {
        self.apply_var(NzVar::new(venv.size()))
            .to_hir(venv.insert())
    }
    /// If the closure variable is free in the closure, return Err. Otherwise, return the value
    /// with that free variable remove.
    pub fn remove_binder(&self) -> Result<Value, ()> {
        match self {
            Closure::Closure { .. } => {
                let v = NzVar::fresh();
                // TODO: handle case where variable is used in closure
                // TODO: return information about where the variable is used
                Ok(self.apply_var(v))
            }
            Closure::ConstantClosure { body, .. } => Ok(body.clone()),
        }
    }
}

impl TextLit {
    pub fn new(
        elts: impl Iterator<Item = InterpolatedTextContents<Value>>,
    ) -> Self {
        TextLit(squash_textlit(elts))
    }
    pub fn interpolate(v: Value) -> TextLit {
        TextLit(vec![InterpolatedTextContents::Expr(v)])
    }
    pub fn from_text(s: String) -> TextLit {
        TextLit(vec![InterpolatedTextContents::Text(s)])
    }

    pub fn concat(&self, other: &TextLit) -> TextLit {
        TextLit::new(self.iter().chain(other.iter()).cloned())
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// If the literal consists of only one interpolation and not text, return the interpolated
    /// value.
    pub fn as_single_expr(&self) -> Option<&Value> {
        use InterpolatedTextContents::Expr;
        if let [Expr(v)] = self.0.as_slice() {
            Some(v)
        } else {
            None
        }
    }
    /// If there are no interpolations, return the corresponding text value.
    pub fn as_text(&self) -> Option<String> {
        use InterpolatedTextContents::Text;
        if self.is_empty() {
            Some(String::new())
        } else if let [Text(s)] = self.0.as_slice() {
            Some(s.clone())
        } else {
            None
        }
    }
    pub fn iter(
        &self,
    ) -> impl Iterator<Item = &InterpolatedTextContents<Value>> {
        self.0.iter()
    }
    /// Normalize the contained values. This does not break the invariant because we have already
    /// ensured that no contained values normalize to a TextLit.
    pub fn normalize(&self) {
        for x in self.0.iter() {
            x.map_ref(Value::normalize);
        }
    }
}

impl lazy::Eval<ValueKind> for Thunk {
    fn eval(self) -> ValueKind {
        self.eval()
    }
}

/// Compare two values for equality modulo alpha/beta-equivalence.
impl std::cmp::PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0) || self.kind() == other.kind()
    }
}
impl std::cmp::Eq for Value {}

impl std::cmp::PartialEq for Thunk {
    fn eq(&self, _other: &Self) -> bool {
        unreachable!(
            "Trying to compare thunks but we should only compare WHNFs"
        )
    }
}
impl std::cmp::Eq for Thunk {}

impl std::cmp::PartialEq for Closure {
    fn eq(&self, other: &Self) -> bool {
        let v = NzVar::fresh();
        self.apply_var(v) == other.apply_var(v)
    }
}
impl std::cmp::Eq for Closure {}

impl std::fmt::Debug for Value {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let vint: &ValueInternal = &self.0;
        let kind = vint.kind();
        if let ValueKind::Const(c) = kind {
            return write!(fmt, "{:?}", c);
        }
        let mut x = fmt.debug_struct(&format!("Value@WHNF"));
        x.field("kind", kind);
        x.finish()
    }
}
