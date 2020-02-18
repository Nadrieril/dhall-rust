use crate::error::TypeError;
use crate::semantics::{type_with, NameEnv, Nir, NzEnv, Tir, TyEnv};
use crate::syntax::{Expr, ExprKind, Span, V};
use crate::{NormalizedExpr, ToExprOptions};

/// Stores an alpha-normalized variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AlphaVar {
    idx: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum HirKind {
    /// A resolved variable (i.e. a DeBruijn index)
    Var(AlphaVar),
    // Forbidden ExprKind variants: Var, Import, Completion
    Expr(ExprKind<Hir>),
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

    /// Converts a closed Hir expr back to the corresponding AST expression.
    pub fn to_expr(&self, opts: ToExprOptions) -> NormalizedExpr {
        hir_to_expr(self, opts, &mut NameEnv::new())
    }
    /// Converts a closed Hir expr back to the corresponding AST expression.
    pub fn to_expr_noopts(&self) -> NormalizedExpr {
        let opts = ToExprOptions { alpha: false };
        self.to_expr(opts)
    }
    pub fn to_expr_tyenv(&self, env: &TyEnv) -> NormalizedExpr {
        let opts = ToExprOptions { alpha: false };
        let mut env = env.as_nameenv().clone();
        hir_to_expr(self, opts, &mut env)
    }

    /// Typecheck the Hir.
    pub fn typecheck<'hir>(
        &'hir self,
        env: &TyEnv,
    ) -> Result<Tir<'hir>, TypeError> {
        type_with(env, self, None)
    }

    /// Eval the Hir. It will actually get evaluated only as needed on demand.
    pub fn eval(&self, env: impl Into<NzEnv>) -> Nir {
        Nir::new_thunk(env.into(), self.clone())
    }
    /// Eval a closed Hir (i.e. without free variables). It will actually get evaluated only as
    /// needed on demand.
    pub fn eval_closed_expr(&self) -> Nir {
        self.eval(NzEnv::new())
    }
    /// Eval a closed Hir fully and recursively;
    pub fn rec_eval_closed_expr(&self) -> Nir {
        let val = self.eval_closed_expr();
        val.normalize();
        val
    }
}

fn hir_to_expr(
    hir: &Hir,
    opts: ToExprOptions,
    env: &mut NameEnv,
) -> NormalizedExpr {
    let kind = match hir.kind() {
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
    };
    Expr::new(kind, hir.span())
}

impl std::cmp::PartialEq for Hir {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}
impl std::cmp::Eq for Hir {}
