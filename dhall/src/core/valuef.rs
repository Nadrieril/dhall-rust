use std::collections::HashMap;

use dhall_syntax::{
    rc, Builtin, Const, ExprF, Integer, InterpolatedTextContents, Label,
    NaiveDouble, Natural,
};

use crate::core::value::{ToExprOptions, Value};
use crate::core::var::{AlphaLabel, AlphaVar, Shift, Subst};
use crate::phase::{Normalized, NormalizedExpr};

/// A semantic value. Subexpressions are Values, which are partially evaluated expressions that are
/// normalized on-demand.
/// If you compare for equality two `ValueF`s in WHNF, then equality will be up to
/// alpha-equivalence (renaming of bound variables) and beta-equivalence (normalization). It will
/// recursively normalize as needed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ValueF {
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

impl ValueF {
    pub(crate) fn into_value_with_type(self, t: Value) -> Value {
        Value::from_valuef_and_type(self, t)
    }

    pub(crate) fn to_expr(&self, opts: ToExprOptions) -> NormalizedExpr {
        match self {
            ValueF::Lam(x, t, e) => rc(ExprF::Lam(
                x.to_label_maybe_alpha(opts.alpha),
                t.to_expr(opts),
                e.to_expr(opts),
            )),
            ValueF::AppliedBuiltin(b, args) => args
                .iter()
                .map(|v| v.to_expr(opts))
                .fold(rc(ExprF::Builtin(*b)), |acc, v| rc(ExprF::App(acc, v))),
            ValueF::Pi(x, t, e) => rc(ExprF::Pi(
                x.to_label_maybe_alpha(opts.alpha),
                t.to_expr(opts),
                e.to_expr(opts),
            )),
            ValueF::Var(v) => rc(ExprF::Var(v.to_var(opts.alpha))),
            ValueF::Const(c) => rc(ExprF::Const(*c)),
            ValueF::BoolLit(b) => rc(ExprF::BoolLit(*b)),
            ValueF::NaturalLit(n) => rc(ExprF::NaturalLit(*n)),
            ValueF::IntegerLit(n) => rc(ExprF::IntegerLit(*n)),
            ValueF::DoubleLit(n) => rc(ExprF::DoubleLit(*n)),
            ValueF::EmptyOptionalLit(n) => rc(ExprF::App(
                rc(ExprF::Builtin(Builtin::OptionalNone)),
                n.to_expr(opts),
            )),
            ValueF::NEOptionalLit(n) => rc(ExprF::SomeLit(n.to_expr(opts))),
            ValueF::EmptyListLit(n) => rc(ExprF::EmptyListLit(rc(ExprF::App(
                rc(ExprF::Builtin(Builtin::List)),
                n.to_expr(opts),
            )))),
            ValueF::NEListLit(elts) => rc(ExprF::NEListLit(
                elts.iter().map(|n| n.to_expr(opts)).collect(),
            )),
            ValueF::RecordLit(kvs) => rc(ExprF::RecordLit(
                kvs.iter()
                    .map(|(k, v)| (k.clone(), v.to_expr(opts)))
                    .collect(),
            )),
            ValueF::RecordType(kts) => rc(ExprF::RecordType(
                kts.iter()
                    .map(|(k, v)| (k.clone(), v.to_expr(opts)))
                    .collect(),
            )),
            ValueF::UnionType(kts) => rc(ExprF::UnionType(
                kts.iter()
                    .map(|(k, v)| {
                        (k.clone(), v.as_ref().map(|v| v.to_expr(opts)))
                    })
                    .collect(),
            )),
            ValueF::UnionConstructor(l, kts) => rc(ExprF::Field(
                ValueF::UnionType(kts.clone()).to_expr(opts),
                l.clone(),
            )),
            ValueF::UnionLit(l, v, kts) => rc(ExprF::App(
                ValueF::UnionConstructor(l.clone(), kts.clone()).to_expr(opts),
                v.to_expr(opts),
            )),
            ValueF::TextLit(elts) => {
                use InterpolatedTextContents::{Expr, Text};
                rc(ExprF::TextLit(
                    elts.iter()
                        .map(|contents| match contents {
                            Expr(e) => Expr(e.to_expr(opts)),
                            Text(s) => Text(s.clone()),
                        })
                        .collect(),
                ))
            }
            ValueF::Equivalence(x, y) => rc(ExprF::BinOp(
                dhall_syntax::BinOp::Equivalence,
                x.to_expr(opts),
                y.to_expr(opts),
            )),
            ValueF::PartialExpr(e) => rc(e.map_ref(|v| v.to_expr(opts))),
        }
    }

    pub(crate) fn normalize_mut(&mut self) {
        match self {
            ValueF::Var(_)
            | ValueF::Const(_)
            | ValueF::BoolLit(_)
            | ValueF::NaturalLit(_)
            | ValueF::IntegerLit(_)
            | ValueF::DoubleLit(_) => {}

            ValueF::EmptyOptionalLit(tth) | ValueF::EmptyListLit(tth) => {
                tth.normalize_mut();
            }

            ValueF::NEOptionalLit(th) => {
                th.normalize_mut();
            }
            ValueF::Lam(_, t, e) => {
                t.normalize_mut();
                e.normalize_mut();
            }
            ValueF::Pi(_, t, e) => {
                t.normalize_mut();
                e.normalize_mut();
            }
            ValueF::AppliedBuiltin(_, args) => {
                for x in args.iter_mut() {
                    x.normalize_mut();
                }
            }
            ValueF::NEListLit(elts) => {
                for x in elts.iter_mut() {
                    x.normalize_mut();
                }
            }
            ValueF::RecordLit(kvs) => {
                for x in kvs.values_mut() {
                    x.normalize_mut();
                }
            }
            ValueF::RecordType(kvs) => {
                for x in kvs.values_mut() {
                    x.normalize_mut();
                }
            }
            ValueF::UnionType(kts) | ValueF::UnionConstructor(_, kts) => {
                for x in kts.values_mut().flat_map(|opt| opt) {
                    x.normalize_mut();
                }
            }
            ValueF::UnionLit(_, v, kts) => {
                v.normalize_mut();
                for x in kts.values_mut().flat_map(|opt| opt) {
                    x.normalize_mut();
                }
            }
            ValueF::TextLit(elts) => {
                for x in elts.iter_mut() {
                    use InterpolatedTextContents::{Expr, Text};
                    match x {
                        Expr(n) => n.normalize_mut(),
                        Text(_) => {}
                    }
                }
            }
            ValueF::Equivalence(x, y) => {
                x.normalize_mut();
                y.normalize_mut();
            }
            ValueF::PartialExpr(e) => {
                // TODO: need map_mut
                e.map_ref(|v| {
                    v.normalize_nf();
                });
            }
        }
    }

    pub(crate) fn from_builtin(b: Builtin) -> ValueF {
        ValueF::AppliedBuiltin(b, vec![])
    }
}

impl Shift for ValueF {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(match self {
            ValueF::Lam(x, t, e) => ValueF::Lam(
                x.clone(),
                t.shift(delta, var)?,
                e.shift(delta, &var.under_binder(x))?,
            ),
            ValueF::AppliedBuiltin(b, args) => {
                ValueF::AppliedBuiltin(*b, args.shift(delta, var)?)
            }
            ValueF::Pi(x, t, e) => ValueF::Pi(
                x.clone(),
                t.shift(delta, var)?,
                e.shift(delta, &var.under_binder(x))?,
            ),
            ValueF::Var(v) => ValueF::Var(v.shift(delta, var)?),
            ValueF::Const(c) => ValueF::Const(*c),
            ValueF::BoolLit(b) => ValueF::BoolLit(*b),
            ValueF::NaturalLit(n) => ValueF::NaturalLit(*n),
            ValueF::IntegerLit(n) => ValueF::IntegerLit(*n),
            ValueF::DoubleLit(n) => ValueF::DoubleLit(*n),
            ValueF::EmptyOptionalLit(tth) => {
                ValueF::EmptyOptionalLit(tth.shift(delta, var)?)
            }
            ValueF::NEOptionalLit(th) => {
                ValueF::NEOptionalLit(th.shift(delta, var)?)
            }
            ValueF::EmptyListLit(tth) => {
                ValueF::EmptyListLit(tth.shift(delta, var)?)
            }
            ValueF::NEListLit(elts) => {
                ValueF::NEListLit(elts.shift(delta, var)?)
            }
            ValueF::RecordLit(kvs) => ValueF::RecordLit(kvs.shift(delta, var)?),
            ValueF::RecordType(kvs) => {
                ValueF::RecordType(kvs.shift(delta, var)?)
            }
            ValueF::UnionType(kts) => ValueF::UnionType(kts.shift(delta, var)?),
            ValueF::UnionConstructor(x, kts) => {
                ValueF::UnionConstructor(x.clone(), kts.shift(delta, var)?)
            }
            ValueF::UnionLit(x, v, kts) => ValueF::UnionLit(
                x.clone(),
                v.shift(delta, var)?,
                kts.shift(delta, var)?,
            ),
            ValueF::TextLit(elts) => ValueF::TextLit(elts.shift(delta, var)?),
            ValueF::Equivalence(x, y) => {
                ValueF::Equivalence(x.shift(delta, var)?, y.shift(delta, var)?)
            }
            ValueF::PartialExpr(e) => ValueF::PartialExpr(e.shift(delta, var)?),
        })
    }
}

impl Subst<Value> for ValueF {
    fn subst_shift(&self, var: &AlphaVar, val: &Value) -> Self {
        match self {
            ValueF::AppliedBuiltin(b, args) => {
                ValueF::AppliedBuiltin(*b, args.subst_shift(var, val))
            }
            ValueF::PartialExpr(e) => {
                ValueF::PartialExpr(e.subst_shift(var, val))
            }
            ValueF::TextLit(elts) => {
                ValueF::TextLit(elts.subst_shift(var, val))
            }
            ValueF::Lam(x, t, e) => ValueF::Lam(
                x.clone(),
                t.subst_shift(var, val),
                e.subst_shift(&var.under_binder(x), &val.under_binder(x)),
            ),
            ValueF::Pi(x, t, e) => ValueF::Pi(
                x.clone(),
                t.subst_shift(var, val),
                e.subst_shift(&var.under_binder(x), &val.under_binder(x)),
            ),
            ValueF::Var(v) if v == var => val.to_whnf_ignore_type(),
            ValueF::Var(v) => ValueF::Var(v.shift(-1, var).unwrap()),
            ValueF::Const(c) => ValueF::Const(*c),
            ValueF::BoolLit(b) => ValueF::BoolLit(*b),
            ValueF::NaturalLit(n) => ValueF::NaturalLit(*n),
            ValueF::IntegerLit(n) => ValueF::IntegerLit(*n),
            ValueF::DoubleLit(n) => ValueF::DoubleLit(*n),
            ValueF::EmptyOptionalLit(tth) => {
                ValueF::EmptyOptionalLit(tth.subst_shift(var, val))
            }
            ValueF::NEOptionalLit(th) => {
                ValueF::NEOptionalLit(th.subst_shift(var, val))
            }
            ValueF::EmptyListLit(tth) => {
                ValueF::EmptyListLit(tth.subst_shift(var, val))
            }
            ValueF::NEListLit(elts) => {
                ValueF::NEListLit(elts.subst_shift(var, val))
            }
            ValueF::RecordLit(kvs) => {
                ValueF::RecordLit(kvs.subst_shift(var, val))
            }
            ValueF::RecordType(kvs) => {
                ValueF::RecordType(kvs.subst_shift(var, val))
            }
            ValueF::UnionType(kts) => {
                ValueF::UnionType(kts.subst_shift(var, val))
            }
            ValueF::UnionConstructor(x, kts) => {
                ValueF::UnionConstructor(x.clone(), kts.subst_shift(var, val))
            }
            ValueF::UnionLit(x, v, kts) => ValueF::UnionLit(
                x.clone(),
                v.subst_shift(var, val),
                kts.subst_shift(var, val),
            ),
            ValueF::Equivalence(x, y) => ValueF::Equivalence(
                x.subst_shift(var, val),
                y.subst_shift(var, val),
            ),
        }
    }
}
