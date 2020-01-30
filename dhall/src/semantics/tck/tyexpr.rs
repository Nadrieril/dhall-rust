use crate::error::{TypeError, TypeMessage};
use crate::semantics::phase::normalize::normalize_tyexpr_whnf;
use crate::semantics::phase::Normalized;
use crate::semantics::phase::{NormalizedExpr, ToExprOptions};
use crate::semantics::{rc, NameEnv, NzEnv, TyEnv, Value};
use crate::syntax::{ExprKind, Span, V};

pub(crate) type Type = Value;

/// Stores an alpha-normalized variable.
#[derive(Debug, Clone, Copy)]
pub struct AlphaVar {
    idx: usize,
}

#[derive(Debug, Clone)]
pub(crate) enum TyExprKind {
    Var(AlphaVar),
    // Forbidden ExprKind variants: Var, Import, Embed
    Expr(ExprKind<TyExpr, Normalized>),
}

// An expression with inferred types at every node and resolved variables.
#[derive(Clone)]
pub(crate) struct TyExpr {
    kind: Box<TyExprKind>,
    ty: Option<Type>,
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

impl TyExpr {
    pub fn new(kind: TyExprKind, ty: Option<Type>, span: Span) -> Self {
        TyExpr {
            kind: Box::new(kind),
            ty,
            span,
        }
    }

    pub fn kind(&self) -> &TyExprKind {
        &*self.kind
    }
    pub fn get_type(&self) -> Result<Type, TypeError> {
        match &self.ty {
            Some(t) => Ok(t.clone()),
            None => Err(TypeError::new(TypeMessage::Sort)),
        }
    }

    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self, opts: ToExprOptions) -> NormalizedExpr {
        tyexpr_to_expr(self, opts, &mut NameEnv::new())
    }
    pub fn to_expr_tyenv(&self, env: &TyEnv) -> NormalizedExpr {
        let opts = ToExprOptions {
            normalize: true,
            alpha: false,
        };
        let mut env = env.as_nameenv().clone();
        tyexpr_to_expr(self, opts, &mut env)
    }

    pub fn normalize_whnf(&self, env: &NzEnv) -> Value {
        normalize_tyexpr_whnf(self, env)
    }
    pub fn normalize_whnf_noenv(&self) -> Value {
        self.normalize_whnf(&NzEnv::new())
    }
    pub fn normalize_nf(&self, env: &NzEnv) -> Value {
        let mut val = self.normalize_whnf(env);
        val.normalize_mut();
        val
    }
    pub fn normalize_nf_noenv(&self) -> Value {
        self.normalize_nf(&NzEnv::new())
    }
}

fn tyexpr_to_expr<'a>(
    tyexpr: &'a TyExpr,
    opts: ToExprOptions,
    env: &mut NameEnv,
) -> NormalizedExpr {
    rc(match tyexpr.kind() {
        TyExprKind::Var(v) if opts.alpha => {
            ExprKind::Var(V("_".into(), v.idx()))
        }
        TyExprKind::Var(v) => ExprKind::Var(env.label_var(v)),
        TyExprKind::Expr(e) => {
            let e = e.map_ref_maybe_binder(|l, tye| {
                if let Some(l) = l {
                    env.insert_mut(l);
                }
                let e = tyexpr_to_expr(tye, opts, env);
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

impl std::fmt::Debug for TyExpr {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut x = fmt.debug_struct("TyExpr");
        x.field("kind", self.kind());
        if let Some(ty) = self.ty.as_ref() {
            x.field("type", &ty);
        } else {
            x.field("type", &None::<()>);
        }
        x.finish()
    }
}
