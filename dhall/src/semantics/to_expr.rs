use crate::semantics::core::var::Binder;
use crate::semantics::phase::typecheck::rc;
use crate::semantics::phase::NormalizedExpr;
use crate::semantics::{Value, ValueKind};
use crate::syntax;
use crate::syntax::{Builtin, ExprKind, V};

/// Controls conversion from `Value` to `Expr`
#[derive(Copy, Clone)]
pub(crate) struct ToExprOptions {
    /// Whether to convert all variables to `_`
    pub(crate) alpha: bool,
    /// Whether to normalize before converting
    pub(crate) normalize: bool,
}

/// Converts a value back to the corresponding AST expression.
pub(crate) fn value_to_expr<'a>(
    val: &'a Value,
    opts: ToExprOptions,
    ctx: &Vec<&'a Binder>,
) -> NormalizedExpr {
    if opts.normalize {
        val.normalize_whnf();
    }

    let kind = val.as_kind();
    let kind = kind.map_ref_with_special_handling_of_binders(
        |v| value_to_expr(v, opts, ctx),
        |b, _, v| {
            let mut ctx = ctx.clone();
            ctx.push(b);
            value_to_expr(v, opts, &ctx)
        },
    );
    match kind {
        ValueKind::Var(v) if opts.alpha => {
            rc(ExprKind::Var(V("_".into(), v.idx())))
        }
        ValueKind::Var(v) => {
            let name = ctx[ctx.len() - 1 - v.idx()].to_label();
            let mut idx = 0;
            for b in ctx.iter().rev().take(v.idx()) {
                if b.name() == &name {
                    idx += 1;
                }
            }
            rc(ExprKind::Var(V(name, idx)))
        }
        ValueKind::Lam(x, t, e) => {
            rc(ExprKind::Lam(x.to_label_maybe_alpha(opts.alpha), t, e))
        }
        ValueKind::AppliedBuiltin(b, args) => args
            .into_iter()
            .fold(rc(ExprKind::Builtin(b)), |acc, v| rc(ExprKind::App(acc, v))),
        ValueKind::Pi(x, t, e) => {
            rc(ExprKind::Pi(x.to_label_maybe_alpha(opts.alpha), t, e))
        }
        ValueKind::Const(c) => rc(ExprKind::Const(c)),
        ValueKind::BoolLit(b) => rc(ExprKind::BoolLit(b)),
        ValueKind::NaturalLit(n) => rc(ExprKind::NaturalLit(n)),
        ValueKind::IntegerLit(n) => rc(ExprKind::IntegerLit(n)),
        ValueKind::DoubleLit(n) => rc(ExprKind::DoubleLit(n)),
        ValueKind::EmptyOptionalLit(n) => rc(ExprKind::App(
            rc(ExprKind::Builtin(Builtin::OptionalNone)),
            n,
        )),
        ValueKind::NEOptionalLit(n) => rc(ExprKind::SomeLit(n)),
        ValueKind::EmptyListLit(n) => rc(ExprKind::EmptyListLit(rc(
            ExprKind::App(rc(ExprKind::Builtin(Builtin::List)), n),
        ))),
        ValueKind::NEListLit(elts) => rc(ExprKind::NEListLit(elts)),
        ValueKind::RecordLit(kvs) => {
            rc(ExprKind::RecordLit(kvs.into_iter().collect()))
        }
        ValueKind::RecordType(kts) => {
            rc(ExprKind::RecordType(kts.into_iter().collect()))
        }
        ValueKind::UnionType(kts) => {
            rc(ExprKind::UnionType(kts.into_iter().collect()))
        }
        ValueKind::UnionConstructor(l, kts) => rc(ExprKind::Field(
            rc(ExprKind::UnionType(kts.into_iter().collect())),
            l,
        )),
        ValueKind::UnionLit(l, v, kts) => rc(ExprKind::App(
            rc(ExprKind::Field(
                rc(ExprKind::UnionType(kts.into_iter().collect())),
                l,
            )),
            v,
        )),
        ValueKind::TextLit(elts) => {
            rc(ExprKind::TextLit(elts.into_iter().collect()))
        }
        ValueKind::Equivalence(x, y) => {
            rc(ExprKind::BinOp(syntax::BinOp::Equivalence, x, y))
        }
        ValueKind::PartialExpr(e) => rc(e),
    }
}
