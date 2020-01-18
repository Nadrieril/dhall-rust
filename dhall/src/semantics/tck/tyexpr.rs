#![allow(dead_code)]
use crate::semantics::core::var::AlphaVar;
use crate::semantics::phase::typecheck::rc;
use crate::semantics::phase::Normalized;
use crate::semantics::phase::{NormalizedExpr, ToExprOptions};
use crate::semantics::Value;
use crate::syntax::{ExprKind, Label, Span, V};

pub(crate) type Type = Value;

// An expression with inferred types at every node and resolved variables.
pub(crate) struct TyExpr {
    kind: Box<TyExprKind>,
    ty: Option<Type>,
    span: Span,
}

pub(crate) enum TyExprKind {
    Var(AlphaVar),
    // Forbidden ExprKind variants: Var
    Expr(ExprKind<TyExpr, Normalized>),
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

    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr<'a>(&'a self, opts: ToExprOptions) -> NormalizedExpr {
        tyexpr_to_expr(self, opts, &mut Vec::new())
    }
}

fn tyexpr_to_expr<'a>(
    tyexpr: &'a TyExpr,
    opts: ToExprOptions,
    ctx: &mut Vec<&'a Label>,
) -> NormalizedExpr {
    rc(match tyexpr.kind() {
        TyExprKind::Var(v) if opts.alpha => {
            ExprKind::Var(V("_".into(), v.idx()))
        }
        TyExprKind::Var(v) => {
            let name = ctx[ctx.len() - 1 - v.idx()];
            let mut idx = 0;
            for l in ctx.iter().rev().take(v.idx()) {
                if *l == name {
                    idx += 1;
                }
            }
            ExprKind::Var(V(name.clone(), idx))
        }
        TyExprKind::Expr(e) => {
            let e = e.map_ref_maybe_binder(|l, tye| {
                if let Some(l) = l {
                    ctx.push(l);
                }
                let e = tyexpr_to_expr(tye, opts, ctx);
                if let Some(_) = l {
                    ctx.pop();
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
