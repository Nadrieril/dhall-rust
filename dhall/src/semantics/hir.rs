#![allow(dead_code)]
use crate::semantics::{rc, NameEnv, NzEnv, TyEnv, Value};
use crate::syntax::{ExprKind, Span, V};
use crate::{Normalized, NormalizedExpr, ToExprOptions};

/// Stores an alpha-normalized variable.
#[derive(Debug, Clone, Copy)]
pub struct AlphaVar {
    idx: usize,
}

#[derive(Debug, Clone)]
pub(crate) enum HirKind {
    Var(AlphaVar),
    // Forbidden ExprKind variants: Var, Import, Embed
    Expr(ExprKind<Hir, Normalized>),
}

// An expression with resolved variables and imports.
#[derive(Debug, Clone)]
pub(crate) struct Hir {
    kind: Box<HirKind>,
    span: Span,
}

impl AlphaVar {
    pub(crate) fn new(idx: usize) -> Self {
        AlphaVar { idx }
    }
    pub(crate) fn idx(&self) -> usize {
        self.idx
    }
}

impl Hir {
    pub fn new(kind: HirKind, span: Span) -> Self {
        Hir {
            kind: Box::new(kind),
            span,
        }
    }

    pub fn kind(&self) -> &HirKind {
        &*self.kind
    }
    pub fn span(&self) -> Span {
        self.span.clone()
    }

    /// Converts a HIR expr back to the corresponding AST expression.
    pub fn to_expr(&self, opts: ToExprOptions) -> NormalizedExpr {
        hir_to_expr(self, opts, &mut NameEnv::new())
    }
    pub fn to_expr_tyenv(&self, env: &TyEnv) -> NormalizedExpr {
        let opts = ToExprOptions {
            normalize: true,
            alpha: false,
        };
        let mut env = env.as_nameenv().clone();
        hir_to_expr(self, opts, &mut env)
    }

    /// Eval the Hir. It will actually get evaluated only as needed on demand.
    pub fn eval(&self, env: &NzEnv) -> Value {
        Value::new_thunk(env, self.clone())
    }
    /// Eval a closed Hir (i.e. without free variables). It will actually get evaluated only as
    /// needed on demand.
    pub fn eval_closed_expr(&self) -> Value {
        self.eval(&NzEnv::new())
    }
    /// Eval a closed Hir fully and recursively (TODO: ish, need to fix under lambdas)
    pub fn rec_eval_closed_expr(&self) -> Value {
        let mut val = self.eval_closed_expr();
        val.normalize_mut();
        val
    }
}

fn hir_to_expr(
    hir: &Hir,
    opts: ToExprOptions,
    env: &mut NameEnv,
) -> NormalizedExpr {
    rc(match hir.kind() {
        HirKind::Var(v) if opts.alpha => ExprKind::Var(V("_".into(), v.idx())),
        HirKind::Var(v) => ExprKind::Var(env.label_var(v)),
        HirKind::Expr(e) => {
            let e = e.map_ref_maybe_binder(|l, hir| {
                if let Some(l) = l {
                    env.insert_mut(l);
                }
                let e = hir_to_expr(hir, opts, env);
                if let Some(_) = l {
                    env.remove_mut();
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
