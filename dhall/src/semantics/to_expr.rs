use crate::semantics::core::value::Value;
use crate::semantics::core::value_kind::ValueKind;
use crate::semantics::phase::typecheck::rc;
use crate::semantics::phase::NormalizedExpr;
use crate::syntax;
use crate::syntax::{Builtin, ExprF};

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
        ValueKind::Lam(x, t, e) => rc(ExprF::Lam(
            x.to_label_maybe_alpha(opts.alpha),
            t.to_expr(opts),
            e.to_expr(opts),
        )),
        ValueKind::AppliedBuiltin(b, args) => args
            .iter()
            .map(|v| v.to_expr(opts))
            .fold(rc(ExprF::Builtin(*b)), |acc, v| rc(ExprF::App(acc, v))),
        ValueKind::Pi(x, t, e) => rc(ExprF::Pi(
            x.to_label_maybe_alpha(opts.alpha),
            t.to_expr(opts),
            e.to_expr(opts),
        )),
        ValueKind::Var(v) => rc(ExprF::Var(v.to_var(opts.alpha))),
        ValueKind::Const(c) => rc(ExprF::Const(*c)),
        ValueKind::BoolLit(b) => rc(ExprF::BoolLit(*b)),
        ValueKind::NaturalLit(n) => rc(ExprF::NaturalLit(*n)),
        ValueKind::IntegerLit(n) => rc(ExprF::IntegerLit(*n)),
        ValueKind::DoubleLit(n) => rc(ExprF::DoubleLit(*n)),
        ValueKind::EmptyOptionalLit(n) => rc(ExprF::App(
            rc(ExprF::Builtin(Builtin::OptionalNone)),
            n.to_expr(opts),
        )),
        ValueKind::NEOptionalLit(n) => rc(ExprF::SomeLit(n.to_expr(opts))),
        ValueKind::EmptyListLit(n) => rc(ExprF::EmptyListLit(rc(ExprF::App(
            rc(ExprF::Builtin(Builtin::List)),
            n.to_expr(opts),
        )))),
        ValueKind::NEListLit(elts) => rc(ExprF::NEListLit(
            elts.iter().map(|n| n.to_expr(opts)).collect(),
        )),
        ValueKind::RecordLit(kvs) => rc(ExprF::RecordLit(
            kvs.iter()
                .map(|(k, v)| (k.clone(), v.to_expr(opts)))
                .collect(),
        )),
        ValueKind::RecordType(kts) => rc(ExprF::RecordType(
            kts.iter()
                .map(|(k, v)| (k.clone(), v.to_expr(opts)))
                .collect(),
        )),
        ValueKind::UnionType(kts) => rc(ExprF::UnionType(
            kts.iter()
                .map(|(k, v)| (k.clone(), v.as_ref().map(|v| v.to_expr(opts))))
                .collect(),
        )),
        ValueKind::UnionConstructor(l, kts) => rc(ExprF::Field(
            ValueKind::UnionType(kts.clone()).to_expr(opts),
            l.clone(),
        )),
        ValueKind::UnionLit(l, v, kts) => rc(ExprF::App(
            ValueKind::UnionConstructor(l.clone(), kts.clone()).to_expr(opts),
            v.to_expr(opts),
        )),
        ValueKind::TextLit(elts) => rc(ExprF::TextLit(
            elts.iter()
                .map(|contents| contents.map_ref(|e| e.to_expr(opts)))
                .collect(),
        )),
        ValueKind::Equivalence(x, y) => rc(ExprF::BinOp(
            syntax::BinOp::Equivalence,
            x.to_expr(opts),
            y.to_expr(opts),
        )),
        ValueKind::PartialExpr(e) => rc(e.map_ref(|v| v.to_expr(opts))),
    }
}
