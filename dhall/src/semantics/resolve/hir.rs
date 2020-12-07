use crate::error::TypeError;
use crate::semantics::{type_with, NameEnv, Nir, NzEnv, Tir, TyEnv, Type};
use crate::syntax::{Expr, ExprKind, Span, V};
use crate::{Ctxt, ToExprOptions};

/// Stores an alpha-normalized variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AlphaVar {
    idx: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HirKind<'cx> {
    /// A resolved variable (i.e. a DeBruijn index)
    Var(AlphaVar),
    /// Result of resolving an import.
    Import(Hir<'cx>, Type<'cx>),
    // Forbidden ExprKind variants: Var, Import, Completion
    Expr(ExprKind<Hir<'cx>>),
}

// An expression with resolved variables and imports.
#[derive(Debug, Clone)]
pub struct Hir<'cx> {
    kind: Box<HirKind<'cx>>,
    span: Span,
}

impl AlphaVar {
    pub fn new(idx: usize) -> Self {
        AlphaVar { idx }
    }
    pub fn idx(self) -> usize {
        self.idx
    }
}

impl<'cx> Hir<'cx> {
    pub fn new(kind: HirKind<'cx>, span: Span) -> Self {
        Hir {
            kind: Box::new(kind),
            span,
        }
    }

    pub fn kind(&self) -> &HirKind<'cx> {
        &*self.kind
    }
    pub fn span(&self) -> Span {
        self.span.clone()
    }

    /// Converts a closed Hir expr back to the corresponding AST expression.
    pub fn to_expr(&self, cx: Ctxt<'cx>, opts: ToExprOptions) -> Expr {
        hir_to_expr(cx, self, opts, &mut NameEnv::new())
    }
    /// Converts a closed Hir expr back to the corresponding AST expression.
    pub fn to_expr_noopts(&self, cx: Ctxt<'cx>) -> Expr {
        let opts = ToExprOptions { alpha: false };
        self.to_expr(cx, opts)
    }
    pub fn to_expr_alpha(&self, cx: Ctxt<'cx>) -> Expr {
        let opts = ToExprOptions { alpha: true };
        self.to_expr(cx, opts)
    }
    pub fn to_expr_tyenv(&self, env: &TyEnv<'cx>) -> Expr {
        let opts = ToExprOptions { alpha: false };
        let cx = env.cx();
        let mut env = env.as_nameenv().clone();
        hir_to_expr(cx, self, opts, &mut env)
    }

    /// Typecheck the Hir.
    pub fn typecheck<'hir>(
        &'hir self,
        env: &TyEnv<'cx>,
    ) -> Result<Tir<'cx, 'hir>, TypeError> {
        type_with(env, self, None)
    }
    pub fn typecheck_noenv<'hir>(
        &'hir self,
        cx: Ctxt<'cx>,
    ) -> Result<Tir<'cx, 'hir>, TypeError> {
        self.typecheck(&TyEnv::new(cx))
    }

    /// Eval the Hir. It will actually get evaluated only as needed on demand.
    pub fn eval(&self, env: impl Into<NzEnv<'cx>>) -> Nir<'cx> {
        Nir::new_thunk(env.into(), self.clone())
    }
    /// Eval a closed Hir (i.e. without free variables). It will actually get evaluated only as
    /// needed on demand.
    pub fn eval_closed_expr(&self, cx: Ctxt<'cx>) -> Nir<'cx> {
        self.eval(NzEnv::new(cx))
    }
}

fn hir_to_expr<'cx>(
    cx: Ctxt<'cx>,
    hir: &Hir<'cx>,
    opts: ToExprOptions,
    env: &mut NameEnv,
) -> Expr {
    let kind = match hir.kind() {
        HirKind::Var(v) if opts.alpha => ExprKind::Var(V("_".into(), v.idx())),
        HirKind::Var(v) => ExprKind::Var(env.label_var(*v)),
        HirKind::Import(hir, _) => {
            return hir_to_expr(cx, hir, opts, &mut NameEnv::new());
        }
        HirKind::Expr(e) => {
            let e = e.map_ref_maybe_binder(|l, hir| {
                if let Some(l) = l {
                    env.insert_mut(l);
                }
                let e = hir_to_expr(cx, hir, opts, env);
                if l.is_some() {
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

impl<'cx> std::cmp::PartialEq for Hir<'cx> {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}
impl<'cx> std::cmp::Eq for Hir<'cx> {}
