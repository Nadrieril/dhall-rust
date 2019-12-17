use std::collections::HashMap;

use crate::semantics::core::value::{ToExprOptions, Value};
use crate::semantics::core::var::{AlphaLabel, AlphaVar, Shift, Subst};
use crate::semantics::phase::typecheck::rc;
use crate::semantics::phase::{Normalized, NormalizedExpr};
use crate::syntax;
use crate::syntax::{
    Builtin, Const, ExprF, Integer, InterpolatedTextContents, Label,
    NaiveDouble, Natural,
};

/// A semantic value. Subexpressions are Values, which are partially evaluated expressions that are
/// normalized on-demand.
/// If you compare for equality two `ValueKind`s in WHNF, then equality will be up to
/// alpha-equivalence (renaming of bound variables) and beta-equivalence (normalization). It will
/// recursively normalize as needed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ValueKind {
    /// Closures
    Lam(AlphaLabel, Value, Value),
    Pi(AlphaLabel, Value, Value),
    // Invariant: in whnf, the evaluation must not be able to progress further.
    AppliedBuiltin(Builtin, Vec<Value>),

    Var(AlphaVar),
    Const(Const),
    BoolLit(bool),
    NaturalLit(Natural),
    IntegerLit(Integer),
    DoubleLit(NaiveDouble),
    EmptyOptionalLit(Value),
    NEOptionalLit(Value),
    // EmptyListLit(t) means `[] : List t`, not `[] : t`
    EmptyListLit(Value),
    NEListLit(Vec<Value>),
    RecordType(HashMap<Label, Value>),
    RecordLit(HashMap<Label, Value>),
    UnionType(HashMap<Label, Option<Value>>),
    UnionConstructor(Label, HashMap<Label, Option<Value>>),
    UnionLit(Label, Value, HashMap<Label, Option<Value>>),
    // Invariant: in whnf, this must not contain interpolations that are themselves TextLits, and
    // contiguous text values must be merged.
    TextLit(Vec<InterpolatedTextContents<Value>>),
    Equivalence(Value, Value),
    // Invariant: in whnf, this must not contain a value captured by one of the variants above.
    PartialExpr(ExprF<Value, Normalized>),
}

impl ValueKind {
    pub(crate) fn into_value_with_type(self, t: Value) -> Value {
        Value::from_kind_and_type(self, t)
    }

    pub(crate) fn to_expr(&self, opts: ToExprOptions) -> NormalizedExpr {
        match self {
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
            ValueKind::EmptyListLit(n) => rc(ExprF::EmptyListLit(rc(
                ExprF::App(rc(ExprF::Builtin(Builtin::List)), n.to_expr(opts)),
            ))),
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
                    .map(|(k, v)| {
                        (k.clone(), v.as_ref().map(|v| v.to_expr(opts)))
                    })
                    .collect(),
            )),
            ValueKind::UnionConstructor(l, kts) => rc(ExprF::Field(
                ValueKind::UnionType(kts.clone()).to_expr(opts),
                l.clone(),
            )),
            ValueKind::UnionLit(l, v, kts) => rc(ExprF::App(
                ValueKind::UnionConstructor(l.clone(), kts.clone())
                    .to_expr(opts),
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

    pub(crate) fn normalize_mut(&mut self) {
        match self {
            ValueKind::Var(_)
            | ValueKind::Const(_)
            | ValueKind::BoolLit(_)
            | ValueKind::NaturalLit(_)
            | ValueKind::IntegerLit(_)
            | ValueKind::DoubleLit(_) => {}

            ValueKind::EmptyOptionalLit(tth) | ValueKind::EmptyListLit(tth) => {
                tth.normalize_mut();
            }

            ValueKind::NEOptionalLit(th) => {
                th.normalize_mut();
            }
            ValueKind::Lam(_, t, e) => {
                t.normalize_mut();
                e.normalize_mut();
            }
            ValueKind::Pi(_, t, e) => {
                t.normalize_mut();
                e.normalize_mut();
            }
            ValueKind::AppliedBuiltin(_, args) => {
                for x in args.iter_mut() {
                    x.normalize_mut();
                }
            }
            ValueKind::NEListLit(elts) => {
                for x in elts.iter_mut() {
                    x.normalize_mut();
                }
            }
            ValueKind::RecordLit(kvs) => {
                for x in kvs.values_mut() {
                    x.normalize_mut();
                }
            }
            ValueKind::RecordType(kvs) => {
                for x in kvs.values_mut() {
                    x.normalize_mut();
                }
            }
            ValueKind::UnionType(kts) | ValueKind::UnionConstructor(_, kts) => {
                for x in kts.values_mut().flat_map(|opt| opt) {
                    x.normalize_mut();
                }
            }
            ValueKind::UnionLit(_, v, kts) => {
                v.normalize_mut();
                for x in kts.values_mut().flat_map(|opt| opt) {
                    x.normalize_mut();
                }
            }
            ValueKind::TextLit(elts) => {
                for x in elts.iter_mut() {
                    x.map_mut(Value::normalize_mut);
                }
            }
            ValueKind::Equivalence(x, y) => {
                x.normalize_mut();
                y.normalize_mut();
            }
            ValueKind::PartialExpr(e) => {
                e.map_mut(Value::normalize_mut);
            }
        }
    }

    pub(crate) fn from_builtin(b: Builtin) -> ValueKind {
        ValueKind::AppliedBuiltin(b, vec![])
    }
}

impl Shift for ValueKind {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(match self {
            ValueKind::Lam(x, t, e) => ValueKind::Lam(
                x.clone(),
                t.shift(delta, var)?,
                e.shift(delta, &var.under_binder(x))?,
            ),
            ValueKind::AppliedBuiltin(b, args) => {
                ValueKind::AppliedBuiltin(*b, args.shift(delta, var)?)
            }
            ValueKind::Pi(x, t, e) => ValueKind::Pi(
                x.clone(),
                t.shift(delta, var)?,
                e.shift(delta, &var.under_binder(x))?,
            ),
            ValueKind::Var(v) => ValueKind::Var(v.shift(delta, var)?),
            ValueKind::Const(c) => ValueKind::Const(*c),
            ValueKind::BoolLit(b) => ValueKind::BoolLit(*b),
            ValueKind::NaturalLit(n) => ValueKind::NaturalLit(*n),
            ValueKind::IntegerLit(n) => ValueKind::IntegerLit(*n),
            ValueKind::DoubleLit(n) => ValueKind::DoubleLit(*n),
            ValueKind::EmptyOptionalLit(tth) => {
                ValueKind::EmptyOptionalLit(tth.shift(delta, var)?)
            }
            ValueKind::NEOptionalLit(th) => {
                ValueKind::NEOptionalLit(th.shift(delta, var)?)
            }
            ValueKind::EmptyListLit(tth) => {
                ValueKind::EmptyListLit(tth.shift(delta, var)?)
            }
            ValueKind::NEListLit(elts) => {
                ValueKind::NEListLit(elts.shift(delta, var)?)
            }
            ValueKind::RecordLit(kvs) => {
                ValueKind::RecordLit(kvs.shift(delta, var)?)
            }
            ValueKind::RecordType(kvs) => {
                ValueKind::RecordType(kvs.shift(delta, var)?)
            }
            ValueKind::UnionType(kts) => {
                ValueKind::UnionType(kts.shift(delta, var)?)
            }
            ValueKind::UnionConstructor(x, kts) => {
                ValueKind::UnionConstructor(x.clone(), kts.shift(delta, var)?)
            }
            ValueKind::UnionLit(x, v, kts) => ValueKind::UnionLit(
                x.clone(),
                v.shift(delta, var)?,
                kts.shift(delta, var)?,
            ),
            ValueKind::TextLit(elts) => {
                ValueKind::TextLit(elts.shift(delta, var)?)
            }
            ValueKind::Equivalence(x, y) => ValueKind::Equivalence(
                x.shift(delta, var)?,
                y.shift(delta, var)?,
            ),
            ValueKind::PartialExpr(e) => {
                ValueKind::PartialExpr(e.shift(delta, var)?)
            }
        })
    }
}

impl Subst<Value> for ValueKind {
    fn subst_shift(&self, var: &AlphaVar, val: &Value) -> Self {
        match self {
            ValueKind::AppliedBuiltin(b, args) => {
                ValueKind::AppliedBuiltin(*b, args.subst_shift(var, val))
            }
            ValueKind::PartialExpr(e) => {
                ValueKind::PartialExpr(e.subst_shift(var, val))
            }
            ValueKind::TextLit(elts) => {
                ValueKind::TextLit(elts.subst_shift(var, val))
            }
            ValueKind::Lam(x, t, e) => ValueKind::Lam(
                x.clone(),
                t.subst_shift(var, val),
                e.subst_shift(&var.under_binder(x), &val.under_binder(x)),
            ),
            ValueKind::Pi(x, t, e) => ValueKind::Pi(
                x.clone(),
                t.subst_shift(var, val),
                e.subst_shift(&var.under_binder(x), &val.under_binder(x)),
            ),
            ValueKind::Var(v) if v == var => val.to_whnf_ignore_type(),
            ValueKind::Var(v) => ValueKind::Var(v.shift(-1, var).unwrap()),
            ValueKind::Const(c) => ValueKind::Const(*c),
            ValueKind::BoolLit(b) => ValueKind::BoolLit(*b),
            ValueKind::NaturalLit(n) => ValueKind::NaturalLit(*n),
            ValueKind::IntegerLit(n) => ValueKind::IntegerLit(*n),
            ValueKind::DoubleLit(n) => ValueKind::DoubleLit(*n),
            ValueKind::EmptyOptionalLit(tth) => {
                ValueKind::EmptyOptionalLit(tth.subst_shift(var, val))
            }
            ValueKind::NEOptionalLit(th) => {
                ValueKind::NEOptionalLit(th.subst_shift(var, val))
            }
            ValueKind::EmptyListLit(tth) => {
                ValueKind::EmptyListLit(tth.subst_shift(var, val))
            }
            ValueKind::NEListLit(elts) => {
                ValueKind::NEListLit(elts.subst_shift(var, val))
            }
            ValueKind::RecordLit(kvs) => {
                ValueKind::RecordLit(kvs.subst_shift(var, val))
            }
            ValueKind::RecordType(kvs) => {
                ValueKind::RecordType(kvs.subst_shift(var, val))
            }
            ValueKind::UnionType(kts) => {
                ValueKind::UnionType(kts.subst_shift(var, val))
            }
            ValueKind::UnionConstructor(x, kts) => ValueKind::UnionConstructor(
                x.clone(),
                kts.subst_shift(var, val),
            ),
            ValueKind::UnionLit(x, v, kts) => ValueKind::UnionLit(
                x.clone(),
                v.subst_shift(var, val),
                kts.subst_shift(var, val),
            ),
            ValueKind::Equivalence(x, y) => ValueKind::Equivalence(
                x.subst_shift(var, val),
                y.subst_shift(var, val),
            ),
        }
    }
}
