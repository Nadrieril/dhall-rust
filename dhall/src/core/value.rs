use std::collections::HashMap;

use dhall_syntax::{
    rc, Builtin, Const, ExprF, Integer, InterpolatedTextContents, Label,
    NaiveDouble, Natural,
};

use crate::core::thunk::{Thunk, TypedThunk};
use crate::core::var::{AlphaLabel, AlphaVar, Shift, Subst};
use crate::phase::normalize::{
    apply_builtin, normalize_one_layer, squash_textlit, OutputSubExpr,
};
use crate::phase::{Normalized, Typed};

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
pub enum Value {
    /// Closures
    Lam(AlphaLabel, TypedThunk, Thunk),
    Pi(AlphaLabel, TypedThunk, TypedThunk),
    // Invariant: the evaluation must not be able to progress further.
    AppliedBuiltin(Builtin, Vec<Thunk>),
    /// `λ(x: a) -> Some x`
    OptionalSomeClosure(TypedThunk),
    /// `λ(x : a) -> λ(xs : List a) -> [ x ] # xs`
    /// `λ(xs : List a) -> [ x ] # xs`
    ListConsClosure(TypedThunk, Option<Thunk>),
    /// `λ(x : Natural) -> x + 1`
    NaturalSuccClosure,

    Var(AlphaVar),
    Const(Const),
    BoolLit(bool),
    NaturalLit(Natural),
    IntegerLit(Integer),
    DoubleLit(NaiveDouble),
    EmptyOptionalLit(TypedThunk),
    NEOptionalLit(Thunk),
    // EmptyListLit(t) means `[] : List t`, not `[] : t`
    EmptyListLit(TypedThunk),
    NEListLit(Vec<Thunk>),
    RecordLit(HashMap<Label, Thunk>),
    RecordType(HashMap<Label, TypedThunk>),
    UnionType(HashMap<Label, Option<TypedThunk>>),
    UnionConstructor(Label, HashMap<Label, Option<TypedThunk>>),
    UnionLit(Label, Thunk, HashMap<Label, Option<TypedThunk>>),
    // Invariant: this must not contain interpolations that are themselves TextLits, and
    // contiguous text values must be merged.
    TextLit(Vec<InterpolatedTextContents<Thunk>>),
    Equivalence(TypedThunk, TypedThunk),
    // Invariant: this must not contain a value captured by one of the variants above.
    PartialExpr(ExprF<Thunk, Normalized>),
}

impl Value {
    pub fn into_thunk(self) -> Thunk {
        Thunk::from_value(self)
    }

    /// Convert the value to a fully normalized syntactic expression
    pub fn normalize_to_expr(&self) -> OutputSubExpr {
        self.normalize_to_expr_maybe_alpha(false)
    }
    /// Convert the value to a fully normalized syntactic expression. Also alpha-normalize
    /// if alpha is `true`
    pub fn normalize_to_expr_maybe_alpha(&self, alpha: bool) -> OutputSubExpr {
        // Ad-hoc macro to help construct the unapplied closures
        macro_rules! make_expr {
            (Natural) => { rc(ExprF::Builtin(Builtin::Natural)) };
            (var($var:ident)) => {
                rc(ExprF::Var(dhall_syntax::V(stringify!($var).into(), 0)))
            };
            ($var:ident) => { $var };
            (List $($rest:tt)*) => {
                rc(ExprF::App(
                    rc(ExprF::Builtin(Builtin::List)),
                    make_expr!($($rest)*)
                ))
            };
            (Some $($rest:tt)*) => {
                rc(ExprF::SomeLit(
                    make_expr!($($rest)*)
                ))
            };
            (1 + $($rest:tt)*) => {
                rc(ExprF::BinOp(
                    dhall_syntax::BinOp::NaturalPlus,
                    rc(ExprF::NaturalLit(1)),
                    make_expr!($($rest)*)
                ))
            };
            ([ $($head:tt)* ] # $($tail:tt)*) => {
                rc(ExprF::BinOp(
                    dhall_syntax::BinOp::ListAppend,
                    rc(ExprF::NEListLit(vec![make_expr!($($head)*)])),
                    make_expr!($($tail)*)
                ))
            };
            (λ($var:ident : $($ty:tt)*) -> $($rest:tt)*) => {
                rc(ExprF::Lam(
                    stringify!($var).into(),
                    make_expr!($($ty)*),
                    make_expr!($($rest)*)
                ))
            };
        }

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
                make_expr!(λ(x: a) -> Some var(x))
            }
            Value::ListConsClosure(a, None) => {
                // Avoid accidental capture of the new `x` variable
                let a1 = a.under_binder(Label::from("x"));
                let a1 = a1.normalize_to_expr_maybe_alpha(alpha);
                let a = a.normalize_to_expr_maybe_alpha(alpha);
                make_expr!(λ(x : a) -> λ(xs : List a1) -> [ var(x) ] # var(xs))
            }
            Value::ListConsClosure(n, Some(v)) => {
                // Avoid accidental capture of the new `xs` variable
                let v = v.under_binder(Label::from("xs"));
                let v = v.normalize_to_expr_maybe_alpha(alpha);
                let a = n.normalize_to_expr_maybe_alpha(alpha);
                make_expr!(λ(xs : List a) -> [ v ] # var(xs))
            }
            Value::NaturalSuccClosure => {
                make_expr!(λ(x : Natural) -> 1 + var(x))
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
            Value::DoubleLit(n) => rc(ExprF::DoubleLit(*n)),
            Value::EmptyOptionalLit(n) => rc(ExprF::App(
                rc(ExprF::Builtin(Builtin::OptionalNone)),
                n.normalize_to_expr_maybe_alpha(alpha),
            )),
            Value::NEOptionalLit(n) => {
                rc(ExprF::SomeLit(n.normalize_to_expr_maybe_alpha(alpha)))
            }
            Value::EmptyListLit(n) => rc(ExprF::EmptyListLit(rc(ExprF::App(
                rc(ExprF::Builtin(Builtin::List)),
                n.normalize_to_expr_maybe_alpha(alpha),
            )))),
            Value::NEListLit(elts) => rc(ExprF::NEListLit(
                elts.iter()
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
            Value::UnionLit(l, v, kts) => rc(ExprF::App(
                Value::UnionConstructor(l.clone(), kts.clone())
                    .normalize_to_expr_maybe_alpha(alpha),
                v.normalize_to_expr_maybe_alpha(alpha),
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
            Value::Equivalence(x, y) => rc(ExprF::BinOp(
                dhall_syntax::BinOp::Equivalence,
                x.normalize_to_expr_maybe_alpha(alpha),
                y.normalize_to_expr_maybe_alpha(alpha),
            )),
            Value::PartialExpr(e) => {
                rc(e.map_ref(|v| v.normalize_to_expr_maybe_alpha(alpha)))
            }
        }
    }

    // Deprecated
    pub fn normalize(&self) -> Value {
        let mut v = self.clone();
        v.normalize_mut();
        v
    }

    pub fn normalize_mut(&mut self) {
        match self {
            Value::NaturalSuccClosure
            | Value::Var(_)
            | Value::Const(_)
            | Value::BoolLit(_)
            | Value::NaturalLit(_)
            | Value::IntegerLit(_)
            | Value::DoubleLit(_) => {}

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
            Value::Equivalence(x, y) => {
                x.normalize_mut();
                y.normalize_mut();
            }
            Value::PartialExpr(e) => {
                // TODO: need map_mut
                e.map_ref(|v| {
                    v.normalize_nf();
                });
            }
        }
    }

    /// Apply to a value
    pub fn app(self, val: Value) -> Value {
        self.app_val(val)
    }

    /// Apply to a value
    pub fn app_val(self, val: Value) -> Value {
        self.app_thunk(val.into_thunk())
    }

    /// Apply to a thunk
    pub fn app_thunk(self, th: Thunk) -> Value {
        Thunk::from_value(self).app_thunk(th)
    }

    pub fn from_builtin(b: Builtin) -> Value {
        Value::AppliedBuiltin(b, vec![])
    }
}

impl Shift for Value {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(match self {
            Value::Lam(x, t, e) => Value::Lam(
                x.clone(),
                t.shift(delta, var)?,
                e.shift(delta, &var.under_binder(x))?,
            ),
            Value::AppliedBuiltin(b, args) => Value::AppliedBuiltin(
                *b,
                args.iter()
                    .map(|v| Ok(v.shift(delta, var)?))
                    .collect::<Result<_, _>>()?,
            ),
            Value::NaturalSuccClosure => Value::NaturalSuccClosure,
            Value::OptionalSomeClosure(tth) => {
                Value::OptionalSomeClosure(tth.shift(delta, var)?)
            }
            Value::ListConsClosure(t, v) => Value::ListConsClosure(
                t.shift(delta, var)?,
                v.as_ref().map(|v| Ok(v.shift(delta, var)?)).transpose()?,
            ),
            Value::Pi(x, t, e) => Value::Pi(
                x.clone(),
                t.shift(delta, var)?,
                e.shift(delta, &var.under_binder(x))?,
            ),
            Value::Var(v) => Value::Var(v.shift(delta, var)?),
            Value::Const(c) => Value::Const(*c),
            Value::BoolLit(b) => Value::BoolLit(*b),
            Value::NaturalLit(n) => Value::NaturalLit(*n),
            Value::IntegerLit(n) => Value::IntegerLit(*n),
            Value::DoubleLit(n) => Value::DoubleLit(*n),
            Value::EmptyOptionalLit(tth) => {
                Value::EmptyOptionalLit(tth.shift(delta, var)?)
            }
            Value::NEOptionalLit(th) => {
                Value::NEOptionalLit(th.shift(delta, var)?)
            }
            Value::EmptyListLit(tth) => {
                Value::EmptyListLit(tth.shift(delta, var)?)
            }
            Value::NEListLit(elts) => Value::NEListLit(
                elts.iter()
                    .map(|v| Ok(v.shift(delta, var)?))
                    .collect::<Result<_, _>>()?,
            ),
            Value::RecordLit(kvs) => Value::RecordLit(
                kvs.iter()
                    .map(|(k, v)| Ok((k.clone(), v.shift(delta, var)?)))
                    .collect::<Result<_, _>>()?,
            ),
            Value::RecordType(kvs) => Value::RecordType(
                kvs.iter()
                    .map(|(k, v)| Ok((k.clone(), v.shift(delta, var)?)))
                    .collect::<Result<_, _>>()?,
            ),
            Value::UnionType(kts) => Value::UnionType(
                kts.iter()
                    .map(|(k, v)| {
                        Ok((
                            k.clone(),
                            v.as_ref()
                                .map(|v| Ok(v.shift(delta, var)?))
                                .transpose()?,
                        ))
                    })
                    .collect::<Result<_, _>>()?,
            ),
            Value::UnionConstructor(x, kts) => Value::UnionConstructor(
                x.clone(),
                kts.iter()
                    .map(|(k, v)| {
                        Ok((
                            k.clone(),
                            v.as_ref()
                                .map(|v| Ok(v.shift(delta, var)?))
                                .transpose()?,
                        ))
                    })
                    .collect::<Result<_, _>>()?,
            ),
            Value::UnionLit(x, v, kts) => Value::UnionLit(
                x.clone(),
                v.shift(delta, var)?,
                kts.iter()
                    .map(|(k, v)| {
                        Ok((
                            k.clone(),
                            v.as_ref()
                                .map(|v| Ok(v.shift(delta, var)?))
                                .transpose()?,
                        ))
                    })
                    .collect::<Result<_, _>>()?,
            ),
            Value::TextLit(elts) => Value::TextLit(
                elts.iter()
                    .map(|contents| {
                        use InterpolatedTextContents::{Expr, Text};
                        Ok(match contents {
                            Expr(th) => Expr(th.shift(delta, var)?),
                            Text(s) => Text(s.clone()),
                        })
                    })
                    .collect::<Result<_, _>>()?,
            ),
            Value::Equivalence(x, y) => {
                Value::Equivalence(x.shift(delta, var)?, y.shift(delta, var)?)
            }
            Value::PartialExpr(e) => Value::PartialExpr(
                e.traverse_ref_with_special_handling_of_binders(
                    |v| Ok(v.shift(delta, var)?),
                    |x, v| Ok(v.shift(delta, &var.under_binder(x))?),
                )?,
            ),
        })
    }
}

impl Subst<Typed> for Value {
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
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
                            &var.under_binder(x),
                            &val.under_binder(x),
                        )
                    },
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
                e.subst_shift(&var.under_binder(x), &val.under_binder(x)),
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
                e.subst_shift(&var.under_binder(x), &val.under_binder(x)),
            ),
            Value::Var(v) => match v.shift(-1, var) {
                None => val.to_value().clone(),
                Some(newvar) => Value::Var(newvar),
            },
            Value::Const(c) => Value::Const(*c),
            Value::BoolLit(b) => Value::BoolLit(*b),
            Value::NaturalLit(n) => Value::NaturalLit(*n),
            Value::IntegerLit(n) => Value::IntegerLit(*n),
            Value::DoubleLit(n) => Value::DoubleLit(*n),
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
            Value::Equivalence(x, y) => Value::Equivalence(
                x.subst_shift(var, val),
                y.subst_shift(var, val),
            ),
        }
    }
}
