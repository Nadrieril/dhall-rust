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
        env: TyEnv,
        body: TyExpr,
    },
    Pi {
        binder: Binder,
        annot: NzExpr,
        env: TyEnv,
        body: TyExpr,
    },
    Expr(ExprKind<NzExpr, Normalized>),
    // Unevaled {
    //     env: TyEnv,
    //     expr: TyExprKind,
    // },
}

#[derive(Debug, Clone)]
enum TyEnvItem {
    // Variable is bound with given type
    Kept(Type),
    // Variable has been replaced by corresponding value
    Replaced(NzExpr),
}

#[derive(Debug, Clone)]
pub(crate) struct TyEnv {
    env: Vec<(Binder, TyEnvItem)>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct QuoteEnv {
    size: usize,
}

// Reverse-debruijn index: counts number of binders from the bottom of the stack.
#[derive(Debug, Clone, Copy)]
pub(crate) struct NzVar {
    idx: usize,
}

impl TyEnv {
    pub fn new() -> Self {
        TyEnv { env: Vec::new() }
    }
    pub fn to_quoteenv(&self) -> QuoteEnv {
        QuoteEnv {
            size: self.env.len(),
        }
    }
    fn with_vec(&self, vec: Vec<(Binder, TyEnvItem)>) -> Self {
        TyEnv { env: vec }
    }

    pub fn insert_type(&self, x: &Binder, t: NzExpr) -> Self {
        let mut vec = self.env.clone();
        vec.push((x.clone(), TyEnvItem::Kept(t)));
        self.with_vec(vec)
    }
    pub fn insert_value(&self, x: &Binder, e: NzExpr) -> Self {
        let mut vec = self.env.clone();
        vec.push((x.clone(), TyEnvItem::Replaced(e)));
        self.with_vec(vec)
    }
    pub fn lookup_var(&self, var: &V<Binder>) -> Option<TyExpr> {
        let V(name, idx) = var;
        let (idx, (_, item)) = self
            .env
            .iter()
            .rev()
            .enumerate()
            .filter(|(_, (x, _))| x == name)
            .nth(*idx)?;
        let ty = match item {
            TyEnvItem::Kept(ty) => ty.clone(),
            TyEnvItem::Replaced(e) => e.get_type().unwrap(),
        };
        Some(TyExpr::new(
            TyExprKind::Var(AlphaVar::new(V((), idx))),
            Some(ty),
        ))
    }
    pub fn lookup_val(&self, var: &AlphaVar) -> NzExpr {
        let idx = self.env.len() - 1 - var.idx();
        match &self.env[idx].1 {
            TyEnvItem::Kept(ty) => NzExpr::new(
                NzExprKind::Var { var: NzVar { idx } },
                Some(ty.clone()),
            ),
            TyEnvItem::Replaced(x) => x.clone(),
        }
    }
    pub fn size(&self) -> usize {
        self.env.len()
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
        fn tyexpr_to_expr<'a>(
            tyexpr: &'a TyExpr,
            opts: ToExprOptions,
            env: &mut Vec<&'a Binder>,
        ) -> NormalizedExpr {
            rc(match tyexpr.kind() {
                TyExprKind::Var(var) if opts.alpha => {
                    ExprKind::Var(V("_".into(), var.idx()))
                }
                TyExprKind::Var(var) => {
                    let name = env[env.len() - 1 - var.idx()];
                    let idx = env
                        .iter()
                        .rev()
                        .take(var.idx())
                        .filter(|l| **l == name)
                        .count();
                    ExprKind::Var(V(name.clone(), idx))
                }
                TyExprKind::Expr(e) => {
                    let e = e.map_ref_maybe_binder(|l, tye| {
                        if let Some(l) = l {
                            env.push(l);
                        }
                        let e = tyexpr_to_expr(tye, opts, env);
                        if let Some(_) = l {
                            env.pop();
                        }
                        e
                    });

                    match e {
                        ExprKind::Lam(_, t, e) if opts.alpha => {
                            ExprKind::Lam("_".into(), t, e)
                        }
                        ExprKind::Pi(_, t, e) if opts.alpha => {
                            ExprKind::Pi("_".into(), t, e)
                        }
                        e => e,
                    }
                }
            })
        }

        tyexpr_to_expr(self, opts, &mut Vec::new())
    }

    pub fn normalize_nf(&self, env: &TyEnv) -> NzExpr {
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
                        NzExprKind::Lam {
                            binder, env, body, ..
                        } => {
                            return body
                                .normalize_nf(&env.insert_value(binder, arg))
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
        self.normalize_nf(&TyEnv::new())
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
                body.normalize_nf(&env.insert_type(binder, annot.clone()))
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
                body.normalize_nf(&env.insert_type(binder, annot.clone()))
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
            let annot_nf = annot.normalize_nf(env);
            let body = type_with(
                &env.insert_type(&binder, annot_nf.clone()),
                body.clone(),
            )?;
            let ty = NzExpr::new(
                NzExprKind::Pi {
                    binder: binder.clone(),
                    annot: annot_nf,
                    env: env.clone(),
                    body: body.get_type()?.quote(env.to_quoteenv()),
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
            let annot_nf = annot.normalize_nf(env);
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
            let (binder, _expected_arg_ty, body_env, body_ty) = match tf.kind()
            {
                NzExprKind::Pi {
                    binder,
                    annot,
                    env,
                    body,
                } => (binder, annot, env, body),
                _ => return Err(TypeError),
            };
            // if arg.get_type()? != *expected_arg_ty {
            //     return Err(TypeError);
            // }

            let arg_nf = arg.normalize_nf(env);
            let ty =
                body_ty.normalize_nf(&body_env.insert_value(&binder, arg_nf));

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
