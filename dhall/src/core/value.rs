use std::collections::BTreeMap;

use dhall_proc_macros as dhall;
use dhall_syntax::{
    rc, Builtin, Const, ExprF, Integer, InterpolatedTextContents, Label,
    Natural, V, X,
};

use crate::core::thunk::{Thunk, TypeThunk};
use crate::phase::normalize::{
    apply_builtin, normalize_one_layer, squash_textlit, OutputSubExpr,
};
use crate::phase::Typed;

/// Stores a pair of variables: a normal one and if relevant one
/// that corresponds to the alpha-normalized version of the first one.
/// Equality is up to alpha-equivalence.
#[derive(Debug, Clone, Eq)]
pub(crate) struct AlphaVar {
    normal: V<Label>,
    alpha: Option<V<()>>,
}

// Exactly like a Label, but equality returns always true.
// This is so that Value equality is exactly alpha-equivalence.
#[derive(Debug, Clone, Eq)]
pub(crate) struct AlphaLabel(Label);

/// A semantic value. The invariants ensure this value represents a Weak-Head
/// Normal Form (WHNF). This means that this first constructor is the first constructor of the
/// final Normal Form (NF).
/// This WHNF must be preserved by operations on `Value`s. In particular, `subst_shift` could break
/// the invariants so need to be careful to reevaluate as needed.
/// Subexpressions are Thunks, which are partially evaluated expressions that are normalized
/// on-demand. When all the Thunks in a Value are at least in WHNF, and recursively so, then the
/// Value is in NF. This is because WHNF ensures that we have the first constructor of the NF; so
/// if we have the first constructor of the NF at all levels, we actually have the NF.
/// Equality is up to alpha-equivalence (renaming of bound variables) and beta-equivalence
/// (normalization). Equality will normalize only as needed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Value {
    /// Closures
    Lam(AlphaLabel, TypeThunk, Thunk),
    Pi(AlphaLabel, TypeThunk, TypeThunk),
    // Invariant: the evaluation must not be able to progress further.
    AppliedBuiltin(Builtin, Vec<Thunk>),
    /// `λ(x: a) -> Some x`
    OptionalSomeClosure(TypeThunk),
    /// `λ(x : a) -> λ(xs : List a) -> [ x ] # xs`
    /// `λ(xs : List a) -> [ x ] # xs`
    ListConsClosure(TypeThunk, Option<Thunk>),
    /// `λ(x : Natural) -> x + 1`
    NaturalSuccClosure,

    Var(AlphaVar),
    Const(Const),
    BoolLit(bool),
    NaturalLit(Natural),
    IntegerLit(Integer),
    EmptyOptionalLit(TypeThunk),
    NEOptionalLit(Thunk),
    EmptyListLit(TypeThunk),
    NEListLit(Vec<Thunk>),
    RecordLit(BTreeMap<Label, Thunk>),
    RecordType(BTreeMap<Label, TypeThunk>),
    UnionType(BTreeMap<Label, Option<TypeThunk>>),
    UnionConstructor(Label, BTreeMap<Label, Option<TypeThunk>>),
    UnionLit(Label, Thunk, BTreeMap<Label, Option<TypeThunk>>),
    // Invariant: this must not contain interpolations that are themselves TextLits, and
    // contiguous text values must be merged.
    TextLit(Vec<InterpolatedTextContents<Thunk>>),
    // Invariant: this must not contain a value captured by one of the variants above.
    PartialExpr(ExprF<Thunk, Label, X>),
}

impl AlphaVar {
    pub(crate) fn to_var(&self, alpha: bool) -> V<Label> {
        match (alpha, &self.alpha) {
            (true, Some(x)) => V("_".into(), x.1),
            _ => self.normal.clone(),
        }
    }
    pub(crate) fn from_var(normal: V<Label>) -> Self {
        AlphaVar {
            normal,
            alpha: None,
        }
    }
    pub(crate) fn shift(&self, delta: isize, var: &AlphaVar) -> Self {
        AlphaVar {
            normal: self.normal.shift(delta, &var.normal),
            alpha: match (&self.alpha, &var.alpha) {
                (Some(x), Some(v)) => Some(x.shift(delta, v)),
                _ => None,
            },
        }
    }
}

impl AlphaLabel {
    fn to_label_maybe_alpha(&self, alpha: bool) -> Label {
        if alpha {
            "_".into()
        } else {
            self.to_label()
        }
    }
    fn to_label(&self) -> Label {
        self.clone().into()
    }
}

impl Value {
    pub(crate) fn into_thunk(self) -> Thunk {
        Thunk::from_value(self)
    }

    /// Convert the value to a fully normalized syntactic expression
    pub(crate) fn normalize_to_expr(&self) -> OutputSubExpr {
        self.normalize_to_expr_maybe_alpha(false)
    }
    /// Convert the value to a fully normalized syntactic expression. Also alpha-normalize
    /// if alpha is `true`
    pub(crate) fn normalize_to_expr_maybe_alpha(
        &self,
        alpha: bool,
    ) -> OutputSubExpr {
        match self {
            Value::Lam(x, t, e) => rc(ExprF::Lam(
                x.to_label_maybe_alpha(alpha),
                t.normalize_to_expr_maybe_alpha(alpha),
                e.normalize_to_expr_maybe_alpha(alpha),
            )),
            Value::AppliedBuiltin(b, args) => {
                let mut e = rc(ExprF::Builtin(*b));
                for v in args {
                    e = rc(ExprF::App(
                        e,
                        v.normalize_to_expr_maybe_alpha(alpha),
                    ));
                }
                e
            }
            Value::OptionalSomeClosure(n) => {
                let a = n.normalize_to_expr_maybe_alpha(alpha);
                dhall::subexpr!(λ(x: a) -> Some x)
            }
            Value::ListConsClosure(a, None) => {
                // Avoid accidental capture of the new `x` variable
                let a1 = a.shift(1, &Label::from("x").into());
                let a1 = a1.normalize_to_expr_maybe_alpha(alpha);
                let a = a.normalize_to_expr_maybe_alpha(alpha);
                dhall::subexpr!(λ(x : a) -> λ(xs : List a1) -> [ x ] # xs)
            }
            Value::ListConsClosure(n, Some(v)) => {
                // Avoid accidental capture of the new `xs` variable
                let v = v.shift(1, &Label::from("xs").into());
                let v = v.normalize_to_expr_maybe_alpha(alpha);
                let a = n.normalize_to_expr_maybe_alpha(alpha);
                dhall::subexpr!(λ(xs : List a) -> [ v ] # xs)
            }
            Value::NaturalSuccClosure => {
                dhall::subexpr!(λ(x : Natural) -> x + 1)
            }
            Value::Pi(x, t, e) => rc(ExprF::Pi(
                x.to_label_maybe_alpha(alpha),
                t.normalize_to_expr_maybe_alpha(alpha),
                e.normalize_to_expr_maybe_alpha(alpha),
            )),
            Value::Var(v) => rc(ExprF::Var(v.to_var(alpha))),
            Value::Const(c) => rc(ExprF::Const(*c)),
            Value::BoolLit(b) => rc(ExprF::BoolLit(*b)),
            Value::NaturalLit(n) => rc(ExprF::NaturalLit(*n)),
            Value::IntegerLit(n) => rc(ExprF::IntegerLit(*n)),
            Value::EmptyOptionalLit(n) => rc(ExprF::App(
                rc(ExprF::Builtin(Builtin::OptionalNone)),
                n.normalize_to_expr_maybe_alpha(alpha),
            )),
            Value::NEOptionalLit(n) => {
                rc(ExprF::SomeLit(n.normalize_to_expr_maybe_alpha(alpha)))
            }
            Value::EmptyListLit(n) => {
                rc(ExprF::EmptyListLit(n.normalize_to_expr_maybe_alpha(alpha)))
            }
            Value::NEListLit(elts) => rc(ExprF::NEListLit(
                elts.into_iter()
                    .map(|n| n.normalize_to_expr_maybe_alpha(alpha))
                    .collect(),
            )),
            Value::RecordLit(kvs) => rc(ExprF::RecordLit(
                kvs.iter()
                    .map(|(k, v)| {
                        (k.clone(), v.normalize_to_expr_maybe_alpha(alpha))
                    })
                    .collect(),
            )),
            Value::RecordType(kts) => rc(ExprF::RecordType(
                kts.iter()
                    .map(|(k, v)| {
                        (k.clone(), v.normalize_to_expr_maybe_alpha(alpha))
                    })
                    .collect(),
            )),
            Value::UnionType(kts) => rc(ExprF::UnionType(
                kts.iter()
                    .map(|(k, v)| {
                        (
                            k.clone(),
                            v.as_ref().map(|v| {
                                v.normalize_to_expr_maybe_alpha(alpha)
                            }),
                        )
                    })
                    .collect(),
            )),
            Value::UnionConstructor(l, kts) => {
                let kts = kts
                    .iter()
                    .map(|(k, v)| {
                        (
                            k.clone(),
                            v.as_ref().map(|v| {
                                v.normalize_to_expr_maybe_alpha(alpha)
                            }),
                        )
                    })
                    .collect();
                rc(ExprF::Field(rc(ExprF::UnionType(kts)), l.clone()))
            }
            Value::UnionLit(l, v, kts) => rc(ExprF::UnionLit(
                l.clone(),
                v.normalize_to_expr_maybe_alpha(alpha),
                kts.iter()
                    .map(|(k, v)| {
                        (
                            k.clone(),
                            v.as_ref().map(|v| {
                                v.normalize_to_expr_maybe_alpha(alpha)
                            }),
                        )
                    })
                    .collect(),
            )),
            Value::TextLit(elts) => {
                use InterpolatedTextContents::{Expr, Text};
                rc(ExprF::TextLit(
                    elts.iter()
                        .map(|contents| match contents {
                            Expr(e) => {
                                Expr(e.normalize_to_expr_maybe_alpha(alpha))
                            }
                            Text(s) => Text(s.clone()),
                        })
                        .collect(),
                ))
            }
            Value::PartialExpr(e) => {
                rc(e.map_ref_simple(|v| v.normalize_to_expr_maybe_alpha(alpha)))
            }
        }
    }

    // Deprecated
    pub(crate) fn normalize(&self) -> Value {
        let mut v = self.clone();
        v.normalize_mut();
        v
    }

    pub(crate) fn normalize_mut(&mut self) {
        match self {
            Value::NaturalSuccClosure
            | Value::Var(_)
            | Value::Const(_)
            | Value::BoolLit(_)
            | Value::NaturalLit(_)
            | Value::IntegerLit(_) => {}

            Value::EmptyOptionalLit(tth)
            | Value::OptionalSomeClosure(tth)
            | Value::EmptyListLit(tth) => {
                tth.normalize_mut();
            }

            Value::NEOptionalLit(th) => {
                th.normalize_mut();
            }
            Value::Lam(_, t, e) => {
                t.normalize_mut();
                e.normalize_mut();
            }
            Value::Pi(_, t, e) => {
                t.normalize_mut();
                e.normalize_mut();
            }
            Value::AppliedBuiltin(_, args) => {
                for x in args.iter_mut() {
                    x.normalize_mut();
                }
            }
            Value::ListConsClosure(t, v) => {
                t.normalize_mut();
                for x in v.iter_mut() {
                    x.normalize_mut();
                }
            }
            Value::NEListLit(elts) => {
                for x in elts.iter_mut() {
                    x.normalize_mut();
                }
            }
            Value::RecordLit(kvs) => {
                for x in kvs.values_mut() {
                    x.normalize_mut();
                }
            }
            Value::RecordType(kvs) => {
                for x in kvs.values_mut() {
                    x.normalize_mut();
                }
            }
            Value::UnionType(kts) | Value::UnionConstructor(_, kts) => {
                for x in kts.values_mut().flat_map(|opt| opt) {
                    x.normalize_mut();
                }
            }
            Value::UnionLit(_, v, kts) => {
                v.normalize_mut();
                for x in kts.values_mut().flat_map(|opt| opt) {
                    x.normalize_mut();
                }
            }
            Value::TextLit(elts) => {
                for x in elts.iter_mut() {
                    use InterpolatedTextContents::{Expr, Text};
                    match x {
                        Expr(n) => n.normalize_mut(),
                        Text(_) => {}
                    }
                }
            }
            Value::PartialExpr(e) => {
                // TODO: need map_mut_simple
                e.map_ref_simple(|v| {
                    v.normalize_nf();
                });
            }
        }
    }

    /// Apply to a value
    pub(crate) fn app(self, val: Value) -> Value {
        self.app_val(val)
    }

    /// Apply to a value
    pub(crate) fn app_val(self, val: Value) -> Value {
        self.app_thunk(val.into_thunk())
    }

    /// Apply to a thunk
    pub(crate) fn app_thunk(self, th: Thunk) -> Value {
        Thunk::from_value(self).app_thunk(th)
    }

    pub(crate) fn from_builtin(b: Builtin) -> Value {
        Value::AppliedBuiltin(b, vec![])
    }

    pub(crate) fn shift(&self, delta: isize, var: &AlphaVar) -> Self {
        match self {
            Value::Lam(x, t, e) => Value::Lam(
                x.clone(),
                t.shift(delta, var),
                e.shift(delta, &var.shift(1, &x.into())),
            ),
            Value::AppliedBuiltin(b, args) => Value::AppliedBuiltin(
                *b,
                args.iter().map(|v| v.shift(delta, var)).collect(),
            ),
            Value::NaturalSuccClosure => Value::NaturalSuccClosure,
            Value::OptionalSomeClosure(tth) => {
                Value::OptionalSomeClosure(tth.shift(delta, var))
            }
            Value::ListConsClosure(t, v) => Value::ListConsClosure(
                t.shift(delta, var),
                v.as_ref().map(|v| v.shift(delta, var)),
            ),
            Value::Pi(x, t, e) => Value::Pi(
                x.clone(),
                t.shift(delta, var),
                e.shift(delta, &var.shift(1, &x.into())),
            ),
            Value::Var(v) => Value::Var(v.shift(delta, var)),
            Value::Const(c) => Value::Const(*c),
            Value::BoolLit(b) => Value::BoolLit(*b),
            Value::NaturalLit(n) => Value::NaturalLit(*n),
            Value::IntegerLit(n) => Value::IntegerLit(*n),
            Value::EmptyOptionalLit(tth) => {
                Value::EmptyOptionalLit(tth.shift(delta, var))
            }
            Value::NEOptionalLit(th) => {
                Value::NEOptionalLit(th.shift(delta, var))
            }
            Value::EmptyListLit(tth) => {
                Value::EmptyListLit(tth.shift(delta, var))
            }
            Value::NEListLit(elts) => Value::NEListLit(
                elts.iter().map(|v| v.shift(delta, var)).collect(),
            ),
            Value::RecordLit(kvs) => Value::RecordLit(
                kvs.iter()
                    .map(|(k, v)| (k.clone(), v.shift(delta, var)))
                    .collect(),
            ),
            Value::RecordType(kvs) => Value::RecordType(
                kvs.iter()
                    .map(|(k, v)| (k.clone(), v.shift(delta, var)))
                    .collect(),
            ),
            Value::UnionType(kts) => Value::UnionType(
                kts.iter()
                    .map(|(k, v)| {
                        (k.clone(), v.as_ref().map(|v| v.shift(delta, var)))
                    })
                    .collect(),
            ),
            Value::UnionConstructor(x, kts) => Value::UnionConstructor(
                x.clone(),
                kts.iter()
                    .map(|(k, v)| {
                        (k.clone(), v.as_ref().map(|v| v.shift(delta, var)))
                    })
                    .collect(),
            ),
            Value::UnionLit(x, v, kts) => Value::UnionLit(
                x.clone(),
                v.shift(delta, var),
                kts.iter()
                    .map(|(k, v)| {
                        (k.clone(), v.as_ref().map(|v| v.shift(delta, var)))
                    })
                    .collect(),
            ),
            Value::TextLit(elts) => Value::TextLit(
                elts.iter()
                    .map(|contents| {
                        use InterpolatedTextContents::{Expr, Text};
                        match contents {
                            Expr(th) => Expr(th.shift(delta, var)),
                            Text(s) => Text(s.clone()),
                        }
                    })
                    .collect(),
            ),
            Value::PartialExpr(e) => {
                Value::PartialExpr(e.map_ref_with_special_handling_of_binders(
                    |v| v.shift(delta, var),
                    |x, v| v.shift(delta, &var.shift(1, &x.into())),
                    X::clone,
                    Label::clone,
                ))
            }
        }
    }

    pub(crate) fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        match self {
            // Retry normalizing since substituting may allow progress
            Value::AppliedBuiltin(b, args) => apply_builtin(
                *b,
                args.iter().map(|v| v.subst_shift(var, val)).collect(),
            ),
            // Retry normalizing since substituting may allow progress
            Value::PartialExpr(e) => {
                normalize_one_layer(e.map_ref_with_special_handling_of_binders(
                    |v| v.subst_shift(var, val),
                    |x, v| {
                        v.subst_shift(
                            &var.shift(1, &x.into()),
                            &val.shift(1, &x.into()),
                        )
                    },
                    X::clone,
                    Label::clone,
                ))
            }
            // Retry normalizing since substituting may allow progress
            Value::TextLit(elts) => {
                Value::TextLit(squash_textlit(elts.iter().map(|contents| {
                    use InterpolatedTextContents::{Expr, Text};
                    match contents {
                        Expr(th) => Expr(th.subst_shift(var, val)),
                        Text(s) => Text(s.clone()),
                    }
                })))
            }
            Value::Lam(x, t, e) => Value::Lam(
                x.clone(),
                t.subst_shift(var, val),
                e.subst_shift(
                    &var.shift(1, &x.into()),
                    &val.shift(1, &x.into()),
                ),
            ),
            Value::NaturalSuccClosure => Value::NaturalSuccClosure,
            Value::OptionalSomeClosure(tth) => {
                Value::OptionalSomeClosure(tth.subst_shift(var, val))
            }
            Value::ListConsClosure(t, v) => Value::ListConsClosure(
                t.subst_shift(var, val),
                v.as_ref().map(|v| v.subst_shift(var, val)),
            ),
            Value::Pi(x, t, e) => Value::Pi(
                x.clone(),
                t.subst_shift(var, val),
                e.subst_shift(
                    &var.shift(1, &x.into()),
                    &val.shift(1, &x.into()),
                ),
            ),
            Value::Var(v) if v == var => val.to_value().clone(),
            Value::Var(v) => Value::Var(v.shift(-1, var)),
            Value::Const(c) => Value::Const(*c),
            Value::BoolLit(b) => Value::BoolLit(*b),
            Value::NaturalLit(n) => Value::NaturalLit(*n),
            Value::IntegerLit(n) => Value::IntegerLit(*n),
            Value::EmptyOptionalLit(tth) => {
                Value::EmptyOptionalLit(tth.subst_shift(var, val))
            }
            Value::NEOptionalLit(th) => {
                Value::NEOptionalLit(th.subst_shift(var, val))
            }
            Value::EmptyListLit(tth) => {
                Value::EmptyListLit(tth.subst_shift(var, val))
            }
            Value::NEListLit(elts) => Value::NEListLit(
                elts.iter().map(|v| v.subst_shift(var, val)).collect(),
            ),
            Value::RecordLit(kvs) => Value::RecordLit(
                kvs.iter()
                    .map(|(k, v)| (k.clone(), v.subst_shift(var, val)))
                    .collect(),
            ),
            Value::RecordType(kvs) => Value::RecordType(
                kvs.iter()
                    .map(|(k, v)| (k.clone(), v.subst_shift(var, val)))
                    .collect(),
            ),
            Value::UnionType(kts) => Value::UnionType(
                kts.iter()
                    .map(|(k, v)| {
                        (k.clone(), v.as_ref().map(|v| v.subst_shift(var, val)))
                    })
                    .collect(),
            ),
            Value::UnionConstructor(x, kts) => Value::UnionConstructor(
                x.clone(),
                kts.iter()
                    .map(|(k, v)| {
                        (k.clone(), v.as_ref().map(|v| v.subst_shift(var, val)))
                    })
                    .collect(),
            ),
            Value::UnionLit(x, v, kts) => Value::UnionLit(
                x.clone(),
                v.subst_shift(var, val),
                kts.iter()
                    .map(|(k, v)| {
                        (k.clone(), v.as_ref().map(|v| v.subst_shift(var, val)))
                    })
                    .collect(),
            ),
        }
    }
}

impl std::cmp::PartialEq for AlphaVar {
    fn eq(&self, other: &Self) -> bool {
        match (&self.alpha, &other.alpha) {
            (Some(x), Some(y)) => x == y,
            (None, None) => self.normal == other.normal,
            _ => false,
        }
    }
}
impl std::cmp::PartialEq for AlphaLabel {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl From<Label> for AlphaVar {
    fn from(x: Label) -> AlphaVar {
        AlphaVar {
            normal: V(x, 0),
            alpha: Some(V((), 0)),
        }
    }
}
impl<'a> From<&'a Label> for AlphaVar {
    fn from(x: &'a Label) -> AlphaVar {
        x.clone().into()
    }
}
impl From<AlphaLabel> for AlphaVar {
    fn from(x: AlphaLabel) -> AlphaVar {
        let l: Label = x.into();
        l.into()
    }
}
impl<'a> From<&'a AlphaLabel> for AlphaVar {
    fn from(x: &'a AlphaLabel) -> AlphaVar {
        x.clone().into()
    }
}

impl From<Label> for AlphaLabel {
    fn from(x: Label) -> AlphaLabel {
        AlphaLabel(x)
    }
}
impl From<AlphaLabel> for Label {
    fn from(x: AlphaLabel) -> Label {
        x.0
    }
}
