#![allow(dead_code)]
use crate::semantics::core::var::AlphaVar;
use crate::semantics::phase::typecheck::rc;
use crate::semantics::phase::{Normalized, NormalizedExpr, ToExprOptions};
use crate::syntax::{Expr, ExprKind, Label, V};

pub(crate) type Type = NzExpr;
#[derive(Debug, Clone)]
pub(crate) struct TypeError;
pub(crate) type Binder = Label;

// An expression with inferred types at every node and resolved variables.
#[derive(Debug, Clone)]
pub(crate) struct TyExpr {
    kind: Box<TyExprKind>,
    ty: Option<Type>,
}

#[derive(Debug, Clone)]
pub(crate) enum TyExprKind {
    Var(AlphaVar),
    Expr(ExprKind<TyExpr, Normalized>),
}

#[derive(Debug, Clone)]
pub(crate) struct NzExpr {
    kind: Box<NzExprKind>,
    ty: Option<Box<Type>>,
}

#[derive(Debug, Clone)]
pub(crate) enum NzExprKind {
    Var {
        var: NzVar,
    },
    Lam {
        binder: Binder,
        annot: NzExpr,
        env: NzEnv,
        body: TyExpr,
    },
    Pi {
        binder: Binder,
        annot: NzExpr,
        env: NzEnv,
        body: TyExpr,
    },
    Expr(ExprKind<NzExpr, Normalized>),
    // Unevaled {
    //     env: NzEnv,
    //     expr: TyExprKind,
    // },
}

#[derive(Debug, Clone)]
enum NzEnvItem {
    // Variable is bound with given type
    Kept(Type),
    // Variable has been replaced by corresponding value
    Replaced(NzExpr),
}

#[derive(Debug, Clone)]
pub(crate) struct TyEnv {
    names: NameEnv,
    items: NzEnv,
}

#[derive(Debug, Clone)]
pub(crate) struct NzEnv {
    items: Vec<NzEnvItem>,
}

#[derive(Debug, Clone)]
pub(crate) struct NameEnv {
    names: Vec<Binder>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct QuoteEnv {
    size: usize,
}

// Reverse-debruijn index: counts number of binders from the bottom of the stack.
#[derive(Debug, Clone, Copy, Eq)]
pub(crate) struct NzVar {
    idx: usize,
}
// TODO: temporary hopefully
impl std::cmp::PartialEq for NzVar {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl TyEnv {
    pub fn new() -> Self {
        TyEnv {
            names: NameEnv::new(),
            items: NzEnv::new(),
        }
    }
    pub fn as_quoteenv(&self) -> QuoteEnv {
        self.names.as_quoteenv()
    }
    pub fn as_nzenv(&self) -> &NzEnv {
        &self.items
    }
    pub fn as_nameenv(&self) -> &NameEnv {
        &self.names
    }

    pub fn insert_type(&self, x: &Binder, t: NzExpr) -> Self {
        TyEnv {
            names: self.names.insert(x),
            items: self.items.insert_type(t),
        }
    }
    pub fn insert_value(&self, x: &Binder, e: NzExpr) -> Self {
        TyEnv {
            names: self.names.insert(x),
            items: self.items.insert_value(e),
        }
    }
    pub fn lookup_var(&self, var: &V<Binder>) -> Option<TyExpr> {
        let var = self.names.unlabel_var(var)?;
        let ty = self.lookup_val(&var).get_type().unwrap();
        Some(TyExpr::new(TyExprKind::Var(var), Some(ty)))
    }
    pub fn lookup_val(&self, var: &AlphaVar) -> NzExpr {
        self.items.lookup_val(var)
    }
    pub fn size(&self) -> usize {
        self.names.size()
    }
}

impl NameEnv {
    pub fn new() -> Self {
        NameEnv { names: Vec::new() }
    }
    pub fn as_quoteenv(&self) -> QuoteEnv {
        QuoteEnv {
            size: self.names.len(),
        }
    }

    pub fn insert(&self, x: &Binder) -> Self {
        let mut env = self.clone();
        env.insert_mut(x);
        env
    }
    pub fn insert_mut(&mut self, x: &Binder) {
        self.names.push(x.clone())
    }
    pub fn remove_mut(&mut self) {
        self.names.pop();
    }

    pub fn unlabel_var(&self, var: &V<Binder>) -> Option<AlphaVar> {
        let V(name, idx) = var;
        let (idx, _) = self
            .names
            .iter()
            .rev()
            .enumerate()
            .filter(|(_, n)| *n == name)
            .nth(*idx)?;
        Some(AlphaVar::new(V((), idx)))
    }
    pub fn label_var(&self, var: &AlphaVar) -> V<Binder> {
        let name = &self.names[self.names.len() - 1 - var.idx()];
        let idx = self
            .names
            .iter()
            .rev()
            .take(var.idx())
            .filter(|n| *n == name)
            .count();
        V(name.clone(), idx)
    }
    pub fn size(&self) -> usize {
        self.names.len()
    }
}

impl NzEnv {
    pub fn new() -> Self {
        NzEnv { items: Vec::new() }
    }

    pub fn insert_type(&self, t: NzExpr) -> Self {
        let mut env = self.clone();
        env.items.push(NzEnvItem::Kept(t));
        env
    }
    pub fn insert_value(&self, e: NzExpr) -> Self {
        let mut env = self.clone();
        env.items.push(NzEnvItem::Replaced(e));
        env
    }
    pub fn lookup_val(&self, var: &AlphaVar) -> NzExpr {
        let idx = self.items.len() - 1 - var.idx();
        match &self.items[idx] {
            NzEnvItem::Kept(ty) => NzExpr::new(
                NzExprKind::Var { var: NzVar { idx } },
                Some(ty.clone()),
            ),
            NzEnvItem::Replaced(x) => x.clone(),
        }
    }
}

impl QuoteEnv {
    pub fn new() -> Self {
        QuoteEnv { size: 0 }
    }
    pub fn insert(&self) -> Self {
        QuoteEnv {
            size: self.size + 1,
        }
    }
    pub fn lookup(&self, var: &NzVar) -> AlphaVar {
        AlphaVar::new(V((), self.size - var.idx - 1))
    }
}

impl NzVar {
    pub fn new(idx: usize) -> Self {
        NzVar { idx }
    }
}

impl TyExpr {
    pub fn new(kind: TyExprKind, ty: Option<Type>) -> Self {
        TyExpr {
            kind: Box::new(kind),
            ty,
        }
    }

    pub fn kind(&self) -> &TyExprKind {
        self.kind.as_ref()
    }
    pub fn get_type(&self) -> Result<Type, TypeError> {
        match &self.ty {
            Some(t) => Ok(t.clone()),
            None => Err(TypeError),
        }
    }

    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self, opts: ToExprOptions) -> NormalizedExpr {
        if opts.alpha {
            self.to_expr_alpha()
        } else {
            self.to_expr_noalpha(&mut NameEnv::new())
        }
    }
    fn to_expr_noalpha(&self, env: &mut NameEnv) -> NormalizedExpr {
        rc(match self.kind() {
            TyExprKind::Var(var) => ExprKind::Var(env.label_var(var)),
            TyExprKind::Expr(e) => e.map_ref_maybe_binder(|l, tye| {
                if let Some(l) = l {
                    env.insert_mut(l);
                }
                let e = tye.to_expr_noalpha(env);
                if let Some(_) = l {
                    env.remove_mut();
                }
                e
            }),
        })
    }
    fn to_expr_alpha(&self) -> NormalizedExpr {
        rc(match self.kind() {
            TyExprKind::Var(var) => ExprKind::Var(V("_".into(), var.idx())),
            TyExprKind::Expr(e) => match e.map_ref(TyExpr::to_expr_alpha) {
                ExprKind::Lam(_, t, e) => ExprKind::Lam("_".into(), t, e),
                ExprKind::Pi(_, t, e) => ExprKind::Pi("_".into(), t, e),
                e => e,
            },
        })
    }

    pub fn normalize_nf(&self, env: &NzEnv) -> NzExpr {
        let kind = match self.kind() {
            TyExprKind::Var(var) => return env.lookup_val(var),
            TyExprKind::Expr(ExprKind::Lam(binder, annot, body)) => {
                NzExprKind::Lam {
                    binder: binder.clone(),
                    annot: annot.normalize_nf(env),
                    env: env.clone(),
                    body: body.clone(),
                }
            }
            TyExprKind::Expr(ExprKind::Pi(binder, annot, body)) => {
                NzExprKind::Pi {
                    binder: binder.clone(),
                    annot: annot.normalize_nf(env),
                    env: env.clone(),
                    body: body.clone(),
                }
            }
            TyExprKind::Expr(e) => {
                let e = e.map_ref(|tye| tye.normalize_nf(env));
                match e {
                    ExprKind::App(f, arg) => match f.kind() {
                        NzExprKind::Lam { env, body, .. } => {
                            return body.normalize_nf(&env.insert_value(arg))
                        }
                        _ => NzExprKind::Expr(ExprKind::App(f, arg)),
                    },
                    _ => NzExprKind::Expr(e),
                }
            }
        };
        let ty = self.ty.clone();
        NzExpr::new(kind, ty)
    }

    pub fn normalize(&self) -> NzExpr {
        self.normalize_nf(&NzEnv::new())
    }
}

impl NzExpr {
    pub fn new(kind: NzExprKind, ty: Option<Type>) -> Self {
        NzExpr {
            kind: Box::new(kind),
            ty: ty.map(Box::new),
        }
    }

    pub fn kind(&self) -> &NzExprKind {
        self.kind.as_ref()
    }
    pub fn get_type(&self) -> Result<Type, TypeError> {
        match &self.ty {
            Some(t) => Ok(t.as_ref().clone()),
            None => Err(TypeError),
        }
    }

    pub fn quote(&self, qenv: QuoteEnv) -> TyExpr {
        let ty = self.ty.as_ref().map(|t| (**t).clone());
        let kind = match self.kind.as_ref() {
            NzExprKind::Var { var } => TyExprKind::Var(qenv.lookup(var)),
            NzExprKind::Lam {
                binder,
                annot,
                env,
                body,
            } => TyExprKind::Expr(ExprKind::Lam(
                binder.clone(),
                annot.quote(qenv),
                body.normalize_nf(&env.insert_type(annot.clone()))
                    .quote(qenv.insert()),
            )),
            NzExprKind::Pi {
                binder,
                annot,
                env,
                body,
            } => TyExprKind::Expr(ExprKind::Pi(
                binder.clone(),
                annot.quote(qenv),
                body.normalize_nf(&env.insert_type(annot.clone()))
                    .quote(qenv.insert()),
            )),
            NzExprKind::Expr(e) => {
                TyExprKind::Expr(e.map_ref(|nze| nze.quote(qenv)))
            } // NzExprKind::Unevaled { env, expr } => {
              //     return TyExpr::new(expr.clone(), ty.clone())
              //         .normalize_nf(env)
              //         .quote(qenv)
              // }
        };
        TyExpr::new(kind, ty)
    }
    pub fn to_expr(&self) -> NormalizedExpr {
        self.quote(QuoteEnv::new()).to_expr(ToExprOptions {
            alpha: false,
            normalize: false,
        })
    }
}

/// Type-check an expression and return the expression alongside its type if type-checking
/// succeeded, or an error if type-checking failed.
fn type_with(env: &TyEnv, e: Expr<Normalized>) -> Result<TyExpr, TypeError> {
    match e.as_ref() {
        ExprKind::Var(var) => match env.lookup_var(&var) {
            Some(x) => Ok(x),
            None => Err(TypeError),
        },
        ExprKind::Lam(binder, annot, body) => {
            let annot = type_with(env, annot.clone())?;
            let annot_nf = annot.normalize_nf(env.as_nzenv());
            let body = type_with(
                &env.insert_type(&binder, annot_nf.clone()),
                body.clone(),
            )?;
            let ty = NzExpr::new(
                NzExprKind::Pi {
                    binder: binder.clone(),
                    annot: annot_nf,
                    env: env.as_nzenv().clone(),
                    body: body.get_type()?.quote(env.as_quoteenv()),
                },
                None, // TODO: function_check
            );
            Ok(TyExpr::new(
                TyExprKind::Expr(ExprKind::Lam(binder.clone(), annot, body)),
                Some(ty),
            ))
        }
        ExprKind::Pi(binder, annot, body) => {
            let annot = type_with(env, annot.clone())?;
            let annot_nf = annot.normalize_nf(env.as_nzenv());
            let body = type_with(
                &env.insert_type(&binder, annot_nf.clone()),
                body.clone(),
            )?;
            Ok(TyExpr::new(
                TyExprKind::Expr(ExprKind::Pi(binder.clone(), annot, body)),
                None, // TODO: function_check
            ))
        }
        ExprKind::App(f, arg) => {
            let f = type_with(env, f.clone())?;
            let arg = type_with(env, arg.clone())?;
            let tf = f.get_type()?;
            let (_expected_arg_ty, body_env, body_ty) = match tf.kind() {
                NzExprKind::Pi {
                    annot, env, body, ..
                } => (annot, env, body),
                _ => return Err(TypeError),
            };
            // if arg.get_type()? != *expected_arg_ty {
            //     return Err(TypeError);
            // }

            let arg_nf = arg.normalize_nf(env.as_nzenv());
            let ty = body_ty.normalize_nf(&body_env.insert_value(arg_nf));

            Ok(TyExpr::new(
                TyExprKind::Expr(ExprKind::App(f, arg)),
                Some(ty),
            ))
        }
        e => Ok(TyExpr::new(
            TyExprKind::Expr(e.traverse_ref(|e| type_with(env, e.clone()))?),
            None,
        )),
    }
}

pub(crate) fn typecheck(e: Expr<Normalized>) -> Result<TyExpr, TypeError> {
    type_with(&TyEnv::new(), e)
}
