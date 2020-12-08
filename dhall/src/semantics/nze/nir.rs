use std::collections::HashMap;
use std::rc::Rc;

use crate::builtins::{Builtin, BuiltinClosure};
use crate::operations::{BinOp, OpKind};
use crate::semantics::nze::lazy;
use crate::semantics::{
    apply_any, normalize_hir, normalize_one_layer, squash_textlit, Binder, Hir,
    HirKind, NzEnv, NzVar, TyEnv, Type, Universe, VarEnv,
};
use crate::syntax::{
    Const, Expr, ExprKind, InterpolatedTextContents, Label, NumKind, Span,
};
use crate::{Ctxt, ToExprOptions};

/// Stores a possibly unevaluated value. Gets (partially) normalized on-demand, sharing computation
/// automatically. Uses a Rc<OnceCell> to share computation.
/// If you compare for equality two `Nir`s, then equality will be up to alpha-equivalence
/// (renaming of bound variables) and beta-equivalence (normalization). It will recursively
/// normalize as needed.
/// Stands for "Normalized Intermediate Representation"
#[derive(Clone)]
pub struct Nir<'cx>(Rc<lazy::Lazy<Thunk<'cx>, NirKind<'cx>>>);

/// An unevaluated subexpression
#[derive(Debug, Clone)]
pub enum Thunk<'cx> {
    /// A completely unnormalized expression.
    Thunk { env: NzEnv<'cx>, body: Hir<'cx> },
    /// A partially normalized expression that may need to go through `normalize_one_layer`.
    PartialExpr { expr: ExprKind<Nir<'cx>> },
}

/// An unevaluated subexpression that takes an argument.
#[derive(Debug, Clone)]
pub enum Closure<'cx> {
    /// Normal closure
    Closure { env: NzEnv<'cx>, body: Hir<'cx> },
    /// Closure that ignores the argument passed
    ConstantClosure { body: Nir<'cx> },
}

/// A text literal with interpolations.
// Invariant: this must not contain interpolations that are themselves TextLits, and contiguous
// text values must be merged.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextLit<'cx>(Vec<InterpolatedTextContents<Nir<'cx>>>);

/// This represents a value in Weak Head Normal Form (WHNF). This means that the value is
/// normalized up to the first constructor, but subexpressions may not be fully normalized.
/// When all the Nirs in a NirKind are in WHNF, and recursively so, then the NirKind is in
/// Normal Form (NF). This is because WHNF ensures that we have the first constructor of the NF; so
/// if we have the first constructor of the NF at all levels, we actually have the NF.
/// In particular, this means that once we get a `NirKind`, it can be considered immutable, and
/// we only need to recursively normalize its sub-`Nir`s to get to the NF.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NirKind<'cx> {
    /// Closures
    LamClosure {
        binder: Binder,
        annot: Nir<'cx>,
        closure: Closure<'cx>,
    },
    PiClosure {
        binder: Binder,
        annot: Nir<'cx>,
        closure: Closure<'cx>,
    },
    AppliedBuiltin(BuiltinClosure<'cx>),

    Var(NzVar),
    Const(Const),
    Num(NumKind),
    // Must be a number type, Bool or Text
    BuiltinType(Builtin),
    TextLit(TextLit<'cx>),
    EmptyOptionalLit(Nir<'cx>),
    NEOptionalLit(Nir<'cx>),
    OptionalType(Nir<'cx>),
    // EmptyListLit(t) means `[] : List t`, not `[] : t`
    EmptyListLit(Nir<'cx>),
    NEListLit(Vec<Nir<'cx>>),
    ListType(Nir<'cx>),
    RecordLit(HashMap<Label, Nir<'cx>>),
    RecordType(HashMap<Label, Nir<'cx>>),
    UnionConstructor(Label, HashMap<Label, Option<Nir<'cx>>>),
    UnionLit(Label, Nir<'cx>, HashMap<Label, Option<Nir<'cx>>>),
    UnionType(HashMap<Label, Option<Nir<'cx>>>),
    Equivalence(Nir<'cx>, Nir<'cx>),
    Assert(Nir<'cx>),
    /// Invariant: evaluation must not be able to progress with `normalize_operation`.
    /// This is used when an operation couldn't proceed further, for example because of variables.
    Op(OpKind<Nir<'cx>>),
}

impl<'cx> Nir<'cx> {
    /// Construct a Nir from a completely unnormalized expression.
    pub fn new_thunk(env: NzEnv<'cx>, hir: Hir<'cx>) -> Self {
        Nir(Rc::new(lazy::Lazy::new(Thunk::new(env, hir))))
    }
    /// Construct a Nir from a partially normalized expression that's not in WHNF.
    pub fn from_partial_expr(e: ExprKind<Self>) -> Self {
        Nir(Rc::new(lazy::Lazy::new(Thunk::from_partial_expr(e))))
    }
    /// Make a Nir from a NirKind
    pub fn from_kind(v: NirKind<'cx>) -> Self {
        Nir(Rc::new(lazy::Lazy::new_completed(v)))
    }
    pub fn from_const(c: Const) -> Self {
        Self::from_kind(NirKind::Const(c))
    }
    pub fn from_builtin(cx: Ctxt<'cx>, b: Builtin) -> Self {
        Self::from_builtin_env(b, &NzEnv::new(cx))
    }
    pub fn from_builtin_env(b: Builtin, env: &NzEnv<'cx>) -> Self {
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
    pub fn kind(&self) -> &NirKind<'cx> {
        &*self.0
    }

    /// The contents of a `Nir` are immutable and shared. If however we happen to be the sole
    /// owners, we can mutate it directly. Otherwise, this clones the internal value first.
    pub fn kind_mut(&mut self) -> &mut NirKind<'cx> {
        Rc::make_mut(&mut self.0).get_mut()
    }
    /// If we are the sole owner of this Nir, we can avoid a clone.
    pub fn into_kind(self) -> NirKind<'cx> {
        match Rc::try_unwrap(self.0) {
            Ok(lazy) => lazy.into_inner(),
            Err(rc) => (**rc).clone(),
        }
    }

    pub fn to_type(&self, u: impl Into<Universe>) -> Type<'cx> {
        Type::new(self.clone(), u.into())
    }
    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self, cx: Ctxt<'cx>, opts: ToExprOptions) -> Expr {
        self.to_hir_noenv().to_expr(cx, opts)
    }
    pub fn to_expr_tyenv(&self, tyenv: &TyEnv<'cx>) -> Expr {
        self.to_hir(tyenv.as_varenv()).to_expr_tyenv(tyenv)
    }

    pub fn app(&self, v: Self) -> Self {
        Nir::from_kind(self.app_to_kind(v))
    }
    pub fn app_to_kind(&self, v: Self) -> NirKind<'cx> {
        apply_any(self, v)
    }

    pub fn to_hir(&self, venv: VarEnv) -> Hir<'cx> {
        let map_uniontype =
            |kts: &HashMap<Label, Option<Nir<'cx>>>| -> ExprKind<Hir<'cx>> {
                ExprKind::UnionType(
                    kts.iter()
                        .map(|(k, v)| {
                            (k.clone(), v.as_ref().map(|v| v.to_hir(venv)))
                        })
                        .collect(),
                )
            };
        let builtin =
            |b| Hir::new(HirKind::Expr(ExprKind::Builtin(b)), Span::Artificial);

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
                    builtin(Builtin::Optional),
                    t.to_hir(venv),
                )),
                NirKind::EmptyOptionalLit(n) => ExprKind::Op(OpKind::App(
                    builtin(Builtin::OptionalNone),
                    n.to_hir(venv),
                )),
                NirKind::NEOptionalLit(n) => ExprKind::SomeLit(n.to_hir(venv)),
                NirKind::ListType(t) => ExprKind::Op(OpKind::App(
                    builtin(Builtin::List),
                    t.to_hir(venv),
                )),
                NirKind::EmptyListLit(n) => ExprKind::EmptyListLit(Hir::new(
                    HirKind::Expr(ExprKind::Op(OpKind::App(
                        builtin(Builtin::List),
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
    pub fn to_hir_noenv(&self) -> Hir<'cx> {
        self.to_hir(VarEnv::new())
    }
}

impl<'cx> NirKind<'cx> {
    pub fn into_nir(self) -> Nir<'cx> {
        Nir::from_kind(self)
    }

    pub fn from_builtin(cx: Ctxt<'cx>, b: Builtin) -> Self {
        NirKind::from_builtin_env(b, NzEnv::new(cx))
    }
    pub fn from_builtin_env(b: Builtin, env: NzEnv<'cx>) -> Self {
        BuiltinClosure::new(b, env)
    }
}

impl<'cx> Thunk<'cx> {
    fn new(env: NzEnv<'cx>, body: Hir<'cx>) -> Self {
        Thunk::Thunk { env, body }
    }
    fn from_partial_expr(expr: ExprKind<Nir<'cx>>) -> Self {
        Thunk::PartialExpr { expr }
    }
    fn eval(self) -> NirKind<'cx> {
        match self {
            Thunk::Thunk { env, body, .. } => normalize_hir(&env, &body),
            Thunk::PartialExpr { expr } => normalize_one_layer(expr),
        }
    }
}

impl<'cx> Closure<'cx> {
    pub fn new(env: &NzEnv<'cx>, body: Hir<'cx>) -> Self {
        Closure::Closure {
            env: env.clone(),
            body,
        }
    }
    /// New closure that ignores its argument
    pub fn new_constant(body: Nir<'cx>) -> Self {
        Closure::ConstantClosure { body }
    }

    pub fn apply(&self, val: Nir<'cx>) -> Nir<'cx> {
        match self {
            Closure::Closure { env, body, .. } => {
                body.eval(env.insert_value(val, ()))
            }
            Closure::ConstantClosure { body, .. } => body.clone(),
        }
    }
    fn apply_var(&self, var: NzVar) -> Nir<'cx> {
        match self {
            Closure::Closure { .. } => {
                self.apply(Nir::from_kind(NirKind::Var(var)))
            }
            Closure::ConstantClosure { body, .. } => body.clone(),
        }
    }

    /// Convert this closure to a Hir expression
    pub fn to_hir(&self, venv: VarEnv) -> Hir<'cx> {
        self.apply_var(NzVar::new(venv.size()))
            .to_hir(venv.insert())
    }
    /// If the closure variable is free in the closure, return Err. Otherwise, return the value
    /// with that free variable remove.
    pub fn remove_binder(&self) -> Result<Nir<'cx>, ()> {
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

impl<'cx> TextLit<'cx> {
    pub fn new(
        elts: impl Iterator<Item = InterpolatedTextContents<Nir<'cx>>>,
    ) -> Self {
        TextLit(squash_textlit(elts))
    }
    pub fn interpolate(v: Nir<'cx>) -> Self {
        TextLit(vec![InterpolatedTextContents::Expr(v)])
    }
    pub fn from_text(s: String) -> Self {
        TextLit(vec![InterpolatedTextContents::Text(s)])
    }

    pub fn concat(&self, other: &Self) -> Self {
        TextLit::new(self.iter().chain(other.iter()).cloned())
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// If the literal consists of only one interpolation and not text, return the interpolated
    /// value.
    pub fn as_single_expr(&self) -> Option<&Nir<'cx>> {
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
    ) -> impl Iterator<Item = &InterpolatedTextContents<Nir<'cx>>> {
        self.0.iter()
    }
}

impl<'cx> lazy::Eval<NirKind<'cx>> for Thunk<'cx> {
    fn eval(self) -> NirKind<'cx> {
        self.eval()
    }
}

/// Compare two values for equality modulo alpha/beta-equivalence.
impl<'cx> std::cmp::PartialEq for Nir<'cx> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0) || self.kind() == other.kind()
    }
}
impl<'cx> std::cmp::Eq for Nir<'cx> {}

impl<'cx> std::cmp::PartialEq for Thunk<'cx> {
    fn eq(&self, _other: &Self) -> bool {
        unreachable!(
            "Trying to compare thunks but we should only compare WHNFs"
        )
    }
}
impl<'cx> std::cmp::Eq for Thunk<'cx> {}

impl<'cx> std::cmp::PartialEq for Closure<'cx> {
    fn eq(&self, other: &Self) -> bool {
        let v = NzVar::fresh();
        self.apply_var(v) == other.apply_var(v)
    }
}
impl<'cx> std::cmp::Eq for Closure<'cx> {}

impl<'cx> std::fmt::Debug for Nir<'cx> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let NirKind::Const(c) = self.kind() {
            return write!(fmt, "{:?}", c);
        }
        let mut x = fmt.debug_struct("Nir");
        x.field("kind", self.kind());
        x.finish()
    }
}
