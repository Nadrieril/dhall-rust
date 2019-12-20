use crate::semantics::core::value::Value;
use crate::semantics::core::value::ValueKind;
use crate::semantics::phase::typecheck::rc;
use crate::semantics::phase::NormalizedExpr;
use crate::syntax;
use crate::syntax::{Builtin, ExprKind};

#[derive(Copy, Clone)]
/// Controls conversion from `Value` to `Expr`
pub(crate) struct ToExprOptions {
    /// Whether to convert all variables to `_`
    pub(crate) alpha: bool,
    /// Whether to normalize before converting
    pub(crate) normalize: bool,
}

/// Converts a value back to the corresponding AST expression.
pub(crate) fn value_to_expr(
    val: &Value,
    opts: ToExprOptions,
) -> NormalizedExpr {
    if opts.normalize {
        val.normalize_whnf();
    }
    val.as_kind().to_expr(opts)
}

/// Converts a value back to the corresponding AST expression.
pub(crate) fn kind_to_expr(
    kind: &ValueKind,
    opts: ToExprOptions,
) -> NormalizedExpr {
    match kind {
        ValueKind::Lam(x, t, e) => rc(ExprKind::Lam(
            x.to_label_maybe_alpha(opts.alpha),
            t.to_expr(opts),
            e.to_expr(opts),
        )),
        ValueKind::AppliedBuiltin(b, args) => args
            .iter()
            .map(|v| v.to_expr(opts))
            .fold(rc(ExprKind::Builtin(*b)), |acc, v| {
                rc(ExprKind::App(acc, v))
            }),
        ValueKind::Pi(x, t, e) => rc(ExprKind::Pi(
            x.to_label_maybe_alpha(opts.alpha),
            t.to_expr(opts),
            e.to_expr(opts),
        )),
        ValueKind::Var(v) => rc(ExprKind::Var(v.to_var(opts.alpha))),
        ValueKind::Const(c) => rc(ExprKind::Const(*c)),
        ValueKind::BoolLit(b) => rc(ExprKind::BoolLit(*b)),
        ValueKind::NaturalLit(n) => rc(ExprKind::NaturalLit(*n)),
        ValueKind::IntegerLit(n) => rc(ExprKind::IntegerLit(*n)),
        ValueKind::DoubleLit(n) => rc(ExprKind::DoubleLit(*n)),
        ValueKind::EmptyOptionalLit(n) => rc(ExprKind::App(
            rc(ExprKind::Builtin(Builtin::OptionalNone)),
            n.to_expr(opts),
        )),
        ValueKind::NEOptionalLit(n) => rc(ExprKind::SomeLit(n.to_expr(opts))),
        ValueKind::EmptyListLit(n) => {
            rc(ExprKind::EmptyListLit(rc(ExprKind::App(
                rc(ExprKind::Builtin(Builtin::List)),
                n.to_expr(opts),
            ))))
        }
        ValueKind::NEListLit(elts) => rc(ExprKind::NEListLit(
            elts.iter().map(|n| n.to_expr(opts)).collect(),
        )),
        ValueKind::RecordLit(kvs) => rc(ExprKind::RecordLit(
            kvs.iter()
                .map(|(k, v)| (k.clone(), v.to_expr(opts)))
                .collect(),
        )),
        ValueKind::RecordType(kts) => rc(ExprKind::RecordType(
            kts.iter()
                .map(|(k, v)| (k.clone(), v.to_expr(opts)))
                .collect(),
        )),
        ValueKind::UnionType(kts) => rc(ExprKind::UnionType(
            kts.iter()
                .map(|(k, v)| (k.clone(), v.as_ref().map(|v| v.to_expr(opts))))
                .collect(),
        )),
        ValueKind::UnionConstructor(l, kts) => rc(ExprKind::Field(
            ValueKind::UnionType(kts.clone()).to_expr(opts),
            l.clone(),
        )),
        ValueKind::UnionLit(l, v, kts) => rc(ExprKind::App(
            ValueKind::UnionConstructor(l.clone(), kts.clone()).to_expr(opts),
            v.to_expr(opts),
        )),
        ValueKind::TextLit(elts) => rc(ExprKind::TextLit(
            elts.iter()
                .map(|contents| contents.map_ref(|e| e.to_expr(opts)))
                .collect(),
        )),
        ValueKind::Equivalence(x, y) => rc(ExprKind::BinOp(
            syntax::BinOp::Equivalence,
            x.to_expr(opts),
            y.to_expr(opts),
        )),
        ValueKind::PartialExpr(e) => rc(e.map_ref(|v| v.to_expr(opts))),
    }
}
