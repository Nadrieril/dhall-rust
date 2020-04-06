use std::collections::HashMap;
use std::rc::Rc;

use crate::operations::OpKind;
use crate::semantics::nze::lazy;
use crate::semantics::{
    apply_any, normalize_hir, normalize_one_layer, squash_textlit, Binder,
    BuiltinClosure, Hir, HirKind, NzEnv, NzVar, TyEnv, Type, Universe, VarEnv,
};
use crate::syntax::{
    BinOp, Builtin, Const, Expr, ExprKind, InterpolatedTextContents, Label,
    NumKind, Span,
};
use crate::ToExprOptions;

/// Stores a possibly unevaluated value. Gets (partially) normalized on-demand, sharing computation
/// automatically. Uses a Rc<RefCell> to share computation.
/// If you compare for equality two `Nir`s, then equality will be up to alpha-equivalence
/// (renaming of bound variables) and beta-equivalence (normalization). It will recursively
/// normalize as needed.
/// Stands for "Normalized intermediate representation"
#[derive(Clone)]
pub struct Nir(Rc<NirInternal>);

#[derive(Debug)]
struct NirInternal {
    kind: lazy::Lazy<Thunk, NirKind>,
}

/// An unevaluated subexpression
#[derive(Debug, Clone)]
pub enum Thunk {
    /// A completely unnormalized expression.
    Thunk { env: NzEnv, body: Hir },
    /// A partially normalized expression that may need to go through `normalize_one_layer`.
    PartialExpr { env: NzEnv, expr: ExprKind<Nir> },
}

/// An unevaluated subexpression that takes an argument.
#[derive(Debug, Clone)]
pub enum Closure {
    /// Normal closure
    Closure { env: NzEnv, body: Hir },
    /// Closure that ignores the argument passed
    ConstantClosure { body: Nir },
}

/// A text literal with interpolations.
// Invariant: this must not contain interpolations that are themselves TextLits, and contiguous
// text values must be merged.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextLit(Vec<InterpolatedTextContents<Nir>>);

/// This represents a value in Weak Head Normal Form (WHNF). This means that the value is
/// normalized up to the first constructor, but subexpressions may not be fully normalized.
/// When all the Nirs in a NirKind are in WHNF, and recursively so, then the NirKind is in
/// Normal Form (NF). This is because WHNF ensures that we have the first constructor of the NF; so
/// if we have the first constructor of the NF at all levels, we actually have the NF.
/// In particular, this means that once we get a `NirKind`, it can be considered immutable, and
/// we only need to recursively normalize its sub-`Nir`s to get to the NF.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NirKind {
    /// Closures
    LamClosure {
        binder: Binder,
        annot: Nir,
        closure: Closure,
    },
    PiClosure {
        binder: Binder,
        annot: Nir,
        closure: Closure,
    },
    AppliedBuiltin(BuiltinClosure),

    Var(NzVar),
    Const(Const),
    Num(NumKind),
    // Must be a number type, Bool or Text
    BuiltinType(Builtin),
    TextLit(TextLit),
    EmptyOptionalLit(Nir),
    NEOptionalLit(Nir),
    OptionalType(Nir),
    // EmptyListLit(t) means `[] : List t`, not `[] : t`
    EmptyListLit(Nir),
    NEListLit(Vec<Nir>),
    ListType(Nir),
    RecordLit(HashMap<Label, Nir>),
    RecordType(HashMap<Label, Nir>),
    UnionConstructor(Label, HashMap<Label, Option<Nir>>),
    UnionLit(Label, Nir, HashMap<Label, Option<Nir>>),
    UnionType(HashMap<Label, Option<Nir>>),
    Equivalence(Nir, Nir),
    Assert(Nir),
    /// Invariant: evaluation must not be able to progress with `normalize_operation`.
    /// This is used when an operation couldn't proceed further, for example because of variables.
    Op(OpKind<Nir>),
}

impl Nir {
    /// Construct a Nir from a completely unnormalized expression.
    pub fn new_thunk(env: NzEnv, hir: Hir) -> Nir {
        NirInternal::from_thunk(Thunk::new(env, hir)).into_nir()
    }
    /// Construct a Nir from a partially normalized expression that's not in WHNF.
    pub fn from_partial_expr(e: ExprKind<Nir>) -> Nir {
        // TODO: env
        let env = NzEnv::new();
        NirInternal::from_thunk(Thunk::from_partial_expr(env, e)).into_nir()
    }
    /// Make a Nir from a NirKind
    pub fn from_kind(v: NirKind) -> Nir {
        NirInternal::from_whnf(v).into_nir()
    }
    pub fn from_const(c: Const) -> Self {
        Self::from_kind(NirKind::Const(c))
    }
    pub fn from_builtin(b: Builtin) -> Self {
        Self::from_builtin_env(b, &NzEnv::new())
    }
    pub fn from_builtin_env(b: Builtin, env: &NzEnv) -> Self {
        Nir::from_kind(NirKind::from_builtin_env(b, env.clone()))
    }
    pub fn from_text(txt: impl ToString) -> Self {
        Nir::from_kind(NirKind::TextLit(TextLit::from_text(txt.to_string())))
    }

    pub fn as_const(&self) -> Option<Const> {
        match &*self.kind() {
            NirKind::Const(c) => Some(*c),
            _ => None,
        }
    }

    /// This is what you want if you want to pattern-match on the value.
    pub fn kind(&self) -> &NirKind {
        self.0.kind()
    }

    pub fn to_type(&self, u: impl Into<Universe>) -> Type {
        Type::new(self.clone(), u.into())
    }
    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self, opts: ToExprOptions) -> Expr {
        self.to_hir_noenv().to_expr(opts)
    }
    pub fn to_expr_tyenv(&self, tyenv: &TyEnv) -> Expr {
        self.to_hir(tyenv.as_varenv()).to_expr_tyenv(tyenv)
    }

    pub fn app(&self, v: Nir) -> Nir {
        Nir::from_kind(self.app_to_kind(v))
    }
    pub fn app_to_kind(&self, v: Nir) -> NirKind {
        apply_any(self, v)
    }

    pub fn to_hir(&self, venv: VarEnv) -> Hir {
        let map_uniontype = |kts: &HashMap<Label, Option<Nir>>| {
            ExprKind::UnionType(
                kts.iter()
                    .map(|(k, v)| {
                        (k.clone(), v.as_ref().map(|v| v.to_hir(venv)))
                    })
                    .collect(),
            )
        };

        let hir = match self.kind() {
            NirKind::Var(v) => HirKind::Var(venv.lookup(*v)),
            NirKind::AppliedBuiltin(closure) => closure.to_hirkind(venv),
            self_kind => HirKind::Expr(match self_kind {
                NirKind::Var(..) | NirKind::AppliedBuiltin(..) => {
                    unreachable!()
                }
                NirKind::LamClosure {
                    binder,
                    annot,
                    closure,
                } => ExprKind::Lam(
                    binder.to_label(),
                    annot.to_hir(venv),
                    closure.to_hir(venv),
                ),
                NirKind::PiClosure {
                    binder,
                    annot,
                    closure,
                } => ExprKind::Pi(
                    binder.to_label(),
                    annot.to_hir(venv),
                    closure.to_hir(venv),
                ),
                NirKind::Const(c) => ExprKind::Const(*c),
                NirKind::BuiltinType(b) => ExprKind::Builtin(*b),
                NirKind::Num(l) => ExprKind::Num(l.clone()),
                NirKind::OptionalType(t) => ExprKind::Op(OpKind::App(
                    Nir::from_builtin(Builtin::Optional).to_hir(venv),
                    t.to_hir(venv),
                )),
                NirKind::EmptyOptionalLit(n) => ExprKind::Op(OpKind::App(
                    Nir::from_builtin(Builtin::OptionalNone).to_hir(venv),
                    n.to_hir(venv),
                )),
                NirKind::NEOptionalLit(n) => ExprKind::SomeLit(n.to_hir(venv)),
                NirKind::ListType(t) => ExprKind::Op(OpKind::App(
                    Nir::from_builtin(Builtin::List).to_hir(venv),
                    t.to_hir(venv),
                )),
                NirKind::EmptyListLit(n) => ExprKind::EmptyListLit(Hir::new(
                    HirKind::Expr(ExprKind::Op(OpKind::App(
                        Nir::from_builtin(Builtin::List).to_hir(venv),
                        n.to_hir(venv),
                    ))),
                    Span::Artificial,
                )),
                NirKind::NEListLit(elts) => ExprKind::NEListLit(
                    elts.iter().map(|v| v.to_hir(venv)).collect(),
                ),
                NirKind::TextLit(elts) => ExprKind::TextLit(
                    elts.iter()
                        .map(|t| t.map_ref(|v| v.to_hir(venv)))
                        .collect(),
                ),
                NirKind::RecordLit(kvs) => ExprKind::RecordLit(
                    kvs.iter()
                        .map(|(k, v)| (k.clone(), v.to_hir(venv)))
                        .collect(),
                ),
                NirKind::RecordType(kts) => ExprKind::RecordType(
                    kts.iter()
                        .map(|(k, v)| (k.clone(), v.to_hir(venv)))
                        .collect(),
                ),
                NirKind::UnionType(kts) => map_uniontype(kts),
                NirKind::UnionConstructor(l, kts) => {
                    ExprKind::Op(OpKind::Field(
                        Hir::new(
                            HirKind::Expr(map_uniontype(kts)),
                            Span::Artificial,
                        ),
                        l.clone(),
                    ))
                }
                NirKind::UnionLit(l, v, kts) => ExprKind::Op(OpKind::App(
                    Hir::new(
                        HirKind::Expr(ExprKind::Op(OpKind::Field(
                            Hir::new(
                                HirKind::Expr(map_uniontype(kts)),
                                Span::Artificial,
                            ),
                            l.clone(),
                        ))),
                        Span::Artificial,
                    ),
                    v.to_hir(venv),
                )),
                NirKind::Equivalence(x, y) => ExprKind::Op(OpKind::BinOp(
                    BinOp::Equivalence,
                    x.to_hir(venv),
                    y.to_hir(venv),
                )),
                NirKind::Assert(x) => ExprKind::Assert(x.to_hir(venv)),
                NirKind::Op(e) => ExprKind::Op(e.map_ref(|v| v.to_hir(venv))),
            }),
        };

        Hir::new(hir, Span::Artificial)
    }
    pub fn to_hir_noenv(&self) -> Hir {
        self.to_hir(VarEnv::new())
    }
}

impl NirInternal {
    fn from_whnf(k: NirKind) -> Self {
        NirInternal {
            kind: lazy::Lazy::new_completed(k),
        }
    }
    fn from_thunk(th: Thunk) -> Self {
        NirInternal {
            kind: lazy::Lazy::new(th),
        }
    }
    fn into_nir(self) -> Nir {
        Nir(Rc::new(self))
    }

    fn kind(&self) -> &NirKind {
        &self.kind
    }
}

impl NirKind {
    pub fn into_nir(self) -> Nir {
        Nir::from_kind(self)
    }

    pub fn from_builtin(b: Builtin) -> NirKind {
        NirKind::from_builtin_env(b, NzEnv::new())
    }
    pub fn from_builtin_env(b: Builtin, env: NzEnv) -> NirKind {
        BuiltinClosure::new(b, env)
    }
}

impl Thunk {
    fn new(env: NzEnv, body: Hir) -> Self {
        Thunk::Thunk { env, body }
    }
    fn from_partial_expr(env: NzEnv, expr: ExprKind<Nir>) -> Self {
        Thunk::PartialExpr { env, expr }
    }
    fn eval(self) -> NirKind {
        match self {
            Thunk::Thunk { env, body } => normalize_hir(&env, &body),
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
    pub fn new_constant(body: Nir) -> Self {
        Closure::ConstantClosure { body }
    }

    pub fn apply(&self, val: Nir) -> Nir {
        match self {
            Closure::Closure { env, body, .. } => {
                body.eval(env.insert_value(val, ()))
            }
            Closure::ConstantClosure { body, .. } => body.clone(),
        }
    }
    fn apply_var(&self, var: NzVar) -> Nir {
        match self {
            Closure::Closure { .. } => {
                self.apply(Nir::from_kind(NirKind::Var(var)))
            }
            Closure::ConstantClosure { body, .. } => body.clone(),
        }
    }

    /// Convert this closure to a Hir expression
    pub fn to_hir(&self, venv: VarEnv) -> Hir {
        self.apply_var(NzVar::new(venv.size()))
            .to_hir(venv.insert())
    }
    /// If the closure variable is free in the closure, return Err. Otherwise, return the value
    /// with that free variable remove.
    pub fn remove_binder(&self) -> Result<Nir, ()> {
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
        elts: impl Iterator<Item = InterpolatedTextContents<Nir>>,
    ) -> Self {
        TextLit(squash_textlit(elts))
    }
    pub fn interpolate(v: Nir) -> TextLit {
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
    pub fn as_single_expr(&self) -> Option<&Nir> {
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
    pub fn iter(&self) -> impl Iterator<Item = &InterpolatedTextContents<Nir>> {
        self.0.iter()
    }
}

impl lazy::Eval<NirKind> for Thunk {
    fn eval(self) -> NirKind {
        self.eval()
    }
}

/// Compare two values for equality modulo alpha/beta-equivalence.
impl std::cmp::PartialEq for Nir {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0) || self.kind() == other.kind()
    }
}
impl std::cmp::Eq for Nir {}

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

impl std::fmt::Debug for Nir {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let vint: &NirInternal = &self.0;
        let kind = vint.kind();
        if let NirKind::Const(c) = kind {
            return write!(fmt, "{:?}", c);
        }
        let mut x = fmt.debug_struct("Nir");
        x.field("kind", kind);
        x.finish()
    }
}
