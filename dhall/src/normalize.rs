#![allow(non_snake_case)]
use std::collections::BTreeMap;
use std::rc::Rc;

use dhall_proc_macros as dhall;
use dhall_syntax::context::Context;
use dhall_syntax::{
    rc, BinOp, Builtin, Const, ExprF, Integer,
    InterpolatedTextContents, Label, Natural, Span, SubExpr, V, X,
};

use crate::expr::{Normalized, Type, Typed, TypedInternal};

type InputSubExpr = SubExpr<Span, Normalized>;
type OutputSubExpr = SubExpr<X, X>;

impl Typed {
    /// Reduce an expression to its normal form, performing beta reduction
    ///
    /// `normalize` does not type-check the expression.  You may want to type-check
    /// expressions before normalizing them since normalization can convert an
    /// ill-typed expression into a well-typed expression.
    ///
    /// However, `normalize` will not fail if the expression is ill-typed and will
    /// leave ill-typed sub-expressions unevaluated.
    ///
    pub fn normalize(self) -> Normalized {
        match &self.0 {
            TypedInternal::Sort => {}
            TypedInternal::Value(thunk, _) => {
                thunk.normalize_nf();
            }
        }
        Normalized(self.0)
    }

    pub(crate) fn shift(&self, delta: isize, var: &DoubleVar) -> Self {
        Typed(self.0.shift(delta, var))
    }

    pub(crate) fn subst_shift(&self, var: &DoubleVar, val: &Typed) -> Self {
        Typed(self.0.subst_shift(var, val))
    }

    pub(crate) fn to_value(&self) -> Value {
        self.0.to_value()
    }

    pub(crate) fn to_thunk(&self) -> Thunk {
        self.0.to_thunk()
    }
}

/// Stores a pair of variables: a normal one and if relevant one
/// that corresponds to the alpha-normalized version of the first one.
#[derive(Debug, Clone, Eq)]
pub(crate) struct DoubleVar {
    normal: V<Label>,
    alpha: Option<V<()>>,
}

impl DoubleVar {
    pub(crate) fn to_var(&self, alpha: bool) -> V<Label> {
        match (alpha, &self.alpha) {
            (true, Some(x)) => V("_".into(), x.1),
            _ => self.normal.clone(),
        }
    }
    pub(crate) fn from_var(normal: V<Label>) -> Self {
        DoubleVar {
            normal,
            alpha: None,
        }
    }
    pub(crate) fn shift(&self, delta: isize, var: &DoubleVar) -> Self {
        DoubleVar {
            normal: self.normal.shift(delta, &var.normal),
            alpha: match (&self.alpha, &var.alpha) {
                (Some(x), Some(v)) => Some(x.shift(delta, v)),
                _ => None,
            },
        }
    }
}

/// Equality is up to alpha-equivalence.
impl std::cmp::PartialEq for DoubleVar {
    fn eq(&self, other: &Self) -> bool {
        match (&self.alpha, &other.alpha) {
            (Some(x), Some(y)) => x == y,
            (None, None) => self.normal == other.normal,
            _ => false,
        }
    }
}

impl From<Label> for DoubleVar {
    fn from(x: Label) -> DoubleVar {
        DoubleVar {
            normal: V(x, 0),
            alpha: Some(V((), 0)),
        }
    }
}
impl<'a> From<&'a Label> for DoubleVar {
    fn from(x: &'a Label) -> DoubleVar {
        x.clone().into()
    }
}
impl From<AlphaLabel> for DoubleVar {
    fn from(x: AlphaLabel) -> DoubleVar {
        let l: Label = x.into();
        l.into()
    }
}
impl<'a> From<&'a AlphaLabel> for DoubleVar {
    fn from(x: &'a AlphaLabel) -> DoubleVar {
        x.clone().into()
    }
}

// Exactly like a Label, but equality returns always true.
// This is so that Value equality is exactly alpha-equivalence.
#[derive(Debug, Clone, Eq)]
pub(crate) struct AlphaLabel(Label);

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

impl std::cmp::PartialEq for AlphaLabel {
    fn eq(&self, _other: &Self) -> bool {
        true
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

#[derive(Debug, Clone)]
enum EnvItem {
    Thunk(Thunk),
    Skip(DoubleVar),
}

impl EnvItem {
    fn shift(&self, delta: isize, var: &DoubleVar) -> Self {
        use EnvItem::*;
        match self {
            Thunk(e) => Thunk(e.shift(delta, var)),
            Skip(v) => Skip(v.shift(delta, var)),
        }
    }

    pub(crate) fn subst_shift(&self, var: &DoubleVar, val: &Typed) -> Self {
        match self {
            EnvItem::Thunk(e) => EnvItem::Thunk(e.subst_shift(var, val)),
            EnvItem::Skip(v) if v == var => EnvItem::Thunk(val.to_thunk()),
            EnvItem::Skip(v) => EnvItem::Skip(v.shift(-1, var)),
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct NormalizationContext(Rc<Context<Label, EnvItem>>);

impl NormalizationContext {
    pub(crate) fn new() -> Self {
        NormalizationContext(Rc::new(Context::new()))
    }
    fn skip(&self, x: &Label) -> Self {
        NormalizationContext(Rc::new(
            self.0
                .map(|_, e| e.shift(1, &x.into()))
                .insert(x.clone(), EnvItem::Skip(x.into())),
        ))
    }
    fn lookup(&self, var: &V<Label>) -> Value {
        let V(x, n) = var;
        match self.0.lookup(x, *n) {
            Some(EnvItem::Thunk(t)) => t.to_value(),
            Some(EnvItem::Skip(newvar)) => Value::Var(newvar.clone()),
            // Free variable
            None => Value::Var(DoubleVar::from_var(var.clone())),
        }
    }
    pub(crate) fn from_typecheck_ctx(
        tc_ctx: &crate::typecheck::TypecheckContext,
    ) -> Self {
        use crate::typecheck::EnvItem::*;
        let mut ctx = Context::new();
        for (k, vs) in tc_ctx.0.iter_keys() {
            for v in vs.iter() {
                let new_item = match v {
                    Type(var, _) => EnvItem::Skip(var.clone()),
                    Value(e) => EnvItem::Thunk(e.to_thunk()),
                };
                ctx = ctx.insert(k.clone(), new_item);
            }
        }
        NormalizationContext(Rc::new(ctx))
    }

    fn shift(&self, delta: isize, var: &DoubleVar) -> Self {
        NormalizationContext(Rc::new(self.0.map(|_, e| e.shift(delta, var))))
    }

    fn subst_shift(&self, var: &DoubleVar, val: &Typed) -> Self {
        NormalizationContext(Rc::new(
            self.0.map(|_, e| e.subst_shift(var, val)),
        ))
    }
}

/// A semantic value.
/// Equality is up to alpha-equivalence (renaming of bound variables).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Value {
    /// Closures
    Lam(AlphaLabel, Thunk, Thunk),
    AppliedBuiltin(Builtin, Vec<Thunk>),
    /// `λ(x: a) -> Some x`
    OptionalSomeClosure(TypeThunk),
    /// `λ(x : a) -> λ(xs : List a) -> [ x ] # xs`
    /// `λ(xs : List a) -> [ x ] # xs`
    ListConsClosure(TypeThunk, Option<Thunk>),
    /// `λ(x : Natural) -> x + 1`
    NaturalSuccClosure,
    Pi(AlphaLabel, TypeThunk, TypeThunk),

    Var(DoubleVar),
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
    TextLit(Vec<InterpolatedTextContents<Thunk>>),
    /// Invariant: This must not contain a value captured by one of the variants above.
    PartialExpr(ExprF<Thunk, Label, X>),
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
    fn normalize(&self) -> Value {
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

    fn shift(&self, delta: isize, var: &DoubleVar) -> Self {
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

    pub(crate) fn subst_shift(&self, var: &DoubleVar, val: &Typed) -> Self {
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

mod thunk {
    use super::{
        apply_any, normalize_whnf, DoubleVar, InputSubExpr,
        NormalizationContext, OutputSubExpr, Value,
    };
    use crate::expr::Typed;
    use std::cell::{Ref, RefCell};
    use std::rc::Rc;

    #[derive(Debug, Clone, Copy)]
    enum Marker {
        /// Weak Head Normal Form, i.e. subexpressions may not be normalized
        WHNF,
        /// Normal form, i.e. completely normalized
        NF,
    }
    use Marker::{NF, WHNF};

    #[derive(Debug)]
    enum ThunkInternal {
        /// Non-normalized value alongside a normalization context
        Unnormalized(NormalizationContext, InputSubExpr),
        /// Partially normalized value.
        /// Invariant: if the marker is `NF`, the value must be fully normalized
        Value(Marker, Value),
    }

    /// Stores a possibl unevaluated value. Uses RefCell to ensure that
    /// the value gets normalized at most once.
    #[derive(Debug, Clone)]
    pub struct Thunk(Rc<RefCell<ThunkInternal>>);

    impl ThunkInternal {
        fn into_thunk(self) -> Thunk {
            Thunk(Rc::new(RefCell::new(self)))
        }

        fn normalize_whnf(&mut self) {
            match self {
                ThunkInternal::Unnormalized(ctx, e) => {
                    *self = ThunkInternal::Value(
                        WHNF,
                        normalize_whnf(ctx.clone(), e.clone()),
                    )
                }
                // Already at least in WHNF
                ThunkInternal::Value(_, _) => {}
            }
        }

        fn normalize_nf(&mut self) {
            match self {
                ThunkInternal::Unnormalized(_, _) => {
                    self.normalize_whnf();
                    self.normalize_nf();
                }
                ThunkInternal::Value(m @ WHNF, v) => {
                    v.normalize_mut();
                    *m = NF;
                }
                // Already in NF
                ThunkInternal::Value(NF, _) => {}
            }
        }

        // Always use normalize_whnf before
        fn as_whnf(&self) -> &Value {
            match self {
                ThunkInternal::Unnormalized(_, _) => unreachable!(),
                ThunkInternal::Value(_, v) => v,
            }
        }

        // Always use normalize_nf before
        fn as_nf(&self) -> &Value {
            match self {
                ThunkInternal::Unnormalized(_, _) => unreachable!(),
                ThunkInternal::Value(WHNF, _) => unreachable!(),
                ThunkInternal::Value(NF, v) => v,
            }
        }

        fn shift(&self, delta: isize, var: &DoubleVar) -> Self {
            match self {
                ThunkInternal::Unnormalized(ctx, e) => {
                    ThunkInternal::Unnormalized(
                        ctx.shift(delta, var),
                        e.clone(),
                    )
                }
                ThunkInternal::Value(m, v) => {
                    ThunkInternal::Value(*m, v.shift(delta, var))
                }
            }
        }

        fn subst_shift(&self, var: &DoubleVar, val: &Typed) -> Self {
            match self {
                ThunkInternal::Unnormalized(ctx, e) => {
                    ThunkInternal::Unnormalized(
                        ctx.subst_shift(var, val),
                        e.clone(),
                    )
                }
                ThunkInternal::Value(_, v) => {
                    // The resulting value may not stay in normal form after substitution
                    ThunkInternal::Value(WHNF, v.subst_shift(var, val))
                }
            }
        }
    }

    impl Thunk {
        pub(crate) fn new(ctx: NormalizationContext, e: InputSubExpr) -> Thunk {
            ThunkInternal::Unnormalized(ctx, e).into_thunk()
        }

        pub(crate) fn from_value(v: Value) -> Thunk {
            ThunkInternal::Value(WHNF, v).into_thunk()
        }

        pub(crate) fn from_normalized_expr(e: OutputSubExpr) -> Thunk {
            Thunk::new(
                NormalizationContext::new(),
                e.embed_absurd().note_absurd(),
            )
        }

        // Normalizes contents to normal form; faster than `normalize_nf` if
        // no one else shares this thunk
        pub(crate) fn normalize_mut(&mut self) {
            match Rc::get_mut(&mut self.0) {
                // Mutate directly if sole owner
                Some(refcell) => RefCell::get_mut(refcell).normalize_nf(),
                // Otherwise mutate through the refcell
                None => self.0.borrow_mut().normalize_nf(),
            }
        }

        fn do_normalize_whnf(&self) {
            let borrow = self.0.borrow();
            match &*borrow {
                ThunkInternal::Unnormalized(_, _) => {
                    drop(borrow);
                    self.0.borrow_mut().normalize_whnf();
                }
                // Already at least in WHNF
                ThunkInternal::Value(_, _) => {}
            }
        }

        fn do_normalize_nf(&self) {
            let borrow = self.0.borrow();
            match &*borrow {
                ThunkInternal::Unnormalized(_, _)
                | ThunkInternal::Value(WHNF, _) => {
                    drop(borrow);
                    self.0.borrow_mut().normalize_nf();
                }
                // Already in NF
                ThunkInternal::Value(NF, _) => {}
            }
        }

        // WARNING: avoid normalizing any thunk while holding on to this ref
        // or you could run into BorrowMut panics
        pub(crate) fn normalize_nf(&self) -> Ref<Value> {
            self.do_normalize_nf();
            Ref::map(self.0.borrow(), ThunkInternal::as_nf)
        }

        // WARNING: avoid normalizing any thunk while holding on to this ref
        // or you could run into BorrowMut panics
        pub(crate) fn as_value(&self) -> Ref<Value> {
            self.do_normalize_whnf();
            Ref::map(self.0.borrow(), ThunkInternal::as_whnf)
        }

        pub(crate) fn to_value(&self) -> Value {
            self.as_value().clone()
        }

        pub(crate) fn normalize_to_expr(&self) -> OutputSubExpr {
            self.normalize_to_expr_maybe_alpha(false)
        }

        pub(crate) fn normalize_to_expr_maybe_alpha(
            &self,
            alpha: bool,
        ) -> OutputSubExpr {
            self.normalize_nf().normalize_to_expr_maybe_alpha(alpha)
        }

        pub(crate) fn app_val(&self, val: Value) -> Value {
            self.app_thunk(val.into_thunk())
        }

        pub(crate) fn app_thunk(&self, th: Thunk) -> Value {
            apply_any(self.clone(), th)
        }

        pub(crate) fn shift(&self, delta: isize, var: &DoubleVar) -> Self {
            self.0.borrow().shift(delta, var).into_thunk()
        }

        pub(crate) fn subst_shift(&self, var: &DoubleVar, val: &Typed) -> Self {
            self.0.borrow().subst_shift(var, val).into_thunk()
        }
    }

    impl std::cmp::PartialEq for Thunk {
        fn eq(&self, other: &Self) -> bool {
            &*self.as_value() == &*other.as_value()
        }
    }
    impl std::cmp::Eq for Thunk {}
}

pub(crate) use thunk::Thunk;

/// A thunk in type position.
#[derive(Debug, Clone)]
pub(crate) enum TypeThunk {
    Thunk(Thunk),
    Type(Type),
}

impl TypeThunk {
    fn from_value(v: Value) -> TypeThunk {
        TypeThunk::from_thunk(Thunk::from_value(v))
    }

    fn from_thunk(th: Thunk) -> TypeThunk {
        TypeThunk::Thunk(th)
    }

    pub(crate) fn from_type(t: Type) -> TypeThunk {
        TypeThunk::Type(t)
    }

    fn normalize_mut(&mut self) {
        match self {
            TypeThunk::Thunk(th) => th.normalize_mut(),
            TypeThunk::Type(_) => {}
        }
    }

    pub(crate) fn normalize_nf(&self) -> Value {
        match self {
            TypeThunk::Thunk(th) => th.normalize_nf().clone(),
            TypeThunk::Type(t) => t.to_value().normalize(),
        }
    }

    pub(crate) fn to_value(&self) -> Value {
        match self {
            TypeThunk::Thunk(th) => th.to_value(),
            TypeThunk::Type(t) => t.to_value(),
        }
    }

    pub(crate) fn normalize_to_expr_maybe_alpha(
        &self,
        alpha: bool,
    ) -> OutputSubExpr {
        self.normalize_nf().normalize_to_expr_maybe_alpha(alpha)
    }

    fn shift(&self, delta: isize, var: &DoubleVar) -> Self {
        match self {
            TypeThunk::Thunk(th) => TypeThunk::Thunk(th.shift(delta, var)),
            TypeThunk::Type(t) => TypeThunk::Type(t.shift(delta, var)),
        }
    }

    pub(crate) fn subst_shift(&self, var: &DoubleVar, val: &Typed) -> Self {
        match self {
            TypeThunk::Thunk(th) => TypeThunk::Thunk(th.subst_shift(var, val)),
            TypeThunk::Type(t) => TypeThunk::Type(t.subst_shift(var, val)),
        }
    }
}

impl std::cmp::PartialEq for TypeThunk {
    fn eq(&self, other: &Self) -> bool {
        self.to_value() == other.to_value()
    }
}
impl std::cmp::Eq for TypeThunk {}

fn apply_builtin(b: Builtin, args: Vec<Thunk>) -> Value {
    use dhall_syntax::Builtin::*;
    use Value::*;

    // Return Ok((unconsumed args, returned value)), or Err(()) if value could not be produced.
    let ret = match (b, args.as_slice()) {
        (OptionalNone, [t, r..]) => {
            Ok((r, EmptyOptionalLit(TypeThunk::from_thunk(t.clone()))))
        }
        (NaturalIsZero, [n, r..]) => match &*n.as_value() {
            NaturalLit(n) => Ok((r, BoolLit(*n == 0))),
            _ => Err(()),
        },
        (NaturalEven, [n, r..]) => match &*n.as_value() {
            NaturalLit(n) => Ok((r, BoolLit(*n % 2 == 0))),
            _ => Err(()),
        },
        (NaturalOdd, [n, r..]) => match &*n.as_value() {
            NaturalLit(n) => Ok((r, BoolLit(*n % 2 != 0))),
            _ => Err(()),
        },
        (NaturalToInteger, [n, r..]) => match &*n.as_value() {
            NaturalLit(n) => Ok((r, IntegerLit(*n as isize))),
            _ => Err(()),
        },
        (NaturalShow, [n, r..]) => match &*n.as_value() {
            NaturalLit(n) => Ok((
                r,
                TextLit(vec![InterpolatedTextContents::Text(n.to_string())]),
            )),
            _ => Err(()),
        },
        (ListLength, [_, l, r..]) => match &*l.as_value() {
            EmptyListLit(_) => Ok((r, NaturalLit(0))),
            NEListLit(xs) => Ok((r, NaturalLit(xs.len()))),
            _ => Err(()),
        },
        (ListHead, [_, l, r..]) => match &*l.as_value() {
            EmptyListLit(n) => Ok((r, EmptyOptionalLit(n.clone()))),
            NEListLit(xs) => {
                Ok((r, NEOptionalLit(xs.iter().next().unwrap().clone())))
            }
            _ => Err(()),
        },
        (ListLast, [_, l, r..]) => match &*l.as_value() {
            EmptyListLit(n) => Ok((r, EmptyOptionalLit(n.clone()))),
            NEListLit(xs) => {
                Ok((r, NEOptionalLit(xs.iter().rev().next().unwrap().clone())))
            }
            _ => Err(()),
        },
        (ListReverse, [_, l, r..]) => match &*l.as_value() {
            EmptyListLit(n) => Ok((r, EmptyListLit(n.clone()))),
            NEListLit(xs) => {
                Ok((r, NEListLit(xs.iter().rev().cloned().collect())))
            }
            _ => Err(()),
        },
        (ListIndexed, [_, l, r..]) => match &*l.as_value() {
            EmptyListLit(t) => {
                let mut kts = BTreeMap::new();
                kts.insert(
                    "index".into(),
                    TypeThunk::from_value(Value::from_builtin(Natural)),
                );
                kts.insert("value".into(), t.clone());
                Ok((r, EmptyListLit(TypeThunk::from_value(RecordType(kts)))))
            }
            NEListLit(xs) => {
                let xs = xs
                    .iter()
                    .enumerate()
                    .map(|(i, e)| {
                        let i = NaturalLit(i);
                        let mut kvs = BTreeMap::new();
                        kvs.insert("index".into(), Thunk::from_value(i));
                        kvs.insert("value".into(), e.clone());
                        Thunk::from_value(RecordLit(kvs))
                    })
                    .collect();
                Ok((r, NEListLit(xs)))
            }
            _ => Err(()),
        },
        (ListBuild, [t, f, r..]) => match &*f.as_value() {
            // fold/build fusion
            Value::AppliedBuiltin(ListFold, args) => {
                if args.len() >= 2 {
                    Ok((r, args[1].to_value()))
                } else {
                    // Do we really need to handle this case ?
                    unimplemented!()
                }
            }
            _ => Ok((
                r,
                f.app_val(Value::from_builtin(List).app_thunk(t.clone()))
                    .app_val(ListConsClosure(
                        TypeThunk::from_thunk(t.clone()),
                        None,
                    ))
                    .app_val(EmptyListLit(TypeThunk::from_thunk(t.clone()))),
            )),
        },
        (ListFold, [_, l, _, cons, nil, r..]) => match &*l.as_value() {
            EmptyListLit(_) => Ok((r, nil.to_value())),
            NEListLit(xs) => {
                let mut v = nil.clone();
                for x in xs.iter().rev() {
                    v = cons
                        .clone()
                        .app_thunk(x.clone())
                        .app_thunk(v)
                        .into_thunk();
                }
                Ok((r, v.to_value()))
            }
            _ => Err(()),
        },
        (OptionalBuild, [t, f, r..]) => match &*f.as_value() {
            // fold/build fusion
            Value::AppliedBuiltin(OptionalFold, args) => {
                if args.len() >= 2 {
                    Ok((r, args[1].to_value()))
                } else {
                    // Do we really need to handle this case ?
                    unimplemented!()
                }
            }
            _ => Ok((
                r,
                f.app_val(Value::from_builtin(Optional).app_thunk(t.clone()))
                    .app_val(OptionalSomeClosure(TypeThunk::from_thunk(
                        t.clone(),
                    )))
                    .app_val(EmptyOptionalLit(TypeThunk::from_thunk(
                        t.clone(),
                    ))),
            )),
        },
        (OptionalFold, [_, v, _, just, nothing, r..]) => match &*v.as_value() {
            EmptyOptionalLit(_) => Ok((r, nothing.to_value())),
            NEOptionalLit(x) => Ok((r, just.app_thunk(x.clone()))),
            _ => Err(()),
        },
        (NaturalBuild, [f, r..]) => match &*f.as_value() {
            // fold/build fusion
            Value::AppliedBuiltin(NaturalFold, args) => {
                if args.len() >= 1 {
                    Ok((r, args[0].to_value()))
                } else {
                    // Do we really need to handle this case ?
                    unimplemented!()
                }
            }
            _ => Ok((
                r,
                f.app_val(Value::from_builtin(Natural))
                    .app_val(NaturalSuccClosure)
                    .app_val(NaturalLit(0)),
            )),
        },
        (NaturalFold, [n, t, succ, zero, r..]) => match &*n.as_value() {
            NaturalLit(0) => Ok((r, zero.to_value())),
            NaturalLit(n) => {
                let fold = Value::from_builtin(NaturalFold)
                    .app(NaturalLit(n - 1))
                    .app_thunk(t.clone())
                    .app_thunk(succ.clone())
                    .app_thunk(zero.clone());
                Ok((r, succ.app_val(fold)))
            }
            _ => Err(()),
        },
        _ => Err(()),
    };
    match ret {
        Ok((unconsumed_args, mut v)) => {
            let n_consumed_args = args.len() - unconsumed_args.len();
            for x in args.into_iter().skip(n_consumed_args) {
                v = v.app_thunk(x);
            }
            v
        }
        Err(()) => AppliedBuiltin(b, args),
    }
}

fn apply_any(f: Thunk, a: Thunk) -> Value {
    let fallback = |f: Thunk, a: Thunk| Value::PartialExpr(ExprF::App(f, a));

    let f_borrow = f.as_value();
    match &*f_borrow {
        Value::Lam(x, _, e) => {
            let val = Typed::from_thunk_untyped(a);
            e.subst_shift(&x.into(), &val).to_value()
        }
        Value::AppliedBuiltin(b, args) => {
            use std::iter::once;
            let args = args.iter().cloned().chain(once(a.clone())).collect();
            apply_builtin(*b, args)
        }
        Value::OptionalSomeClosure(_) => Value::NEOptionalLit(a),
        Value::ListConsClosure(t, None) => {
            Value::ListConsClosure(t.clone(), Some(a))
        }
        Value::ListConsClosure(_, Some(x)) => {
            let a_borrow = a.as_value();
            match &*a_borrow {
                Value::EmptyListLit(_) => Value::NEListLit(vec![x.clone()]),
                Value::NEListLit(xs) => {
                    use std::iter::once;
                    let xs =
                        once(x.clone()).chain(xs.iter().cloned()).collect();
                    Value::NEListLit(xs)
                }
                _ => {
                    drop(f_borrow);
                    drop(a_borrow);
                    fallback(f, a)
                }
            }
        }
        Value::NaturalSuccClosure => {
            let a_borrow = a.as_value();
            match &*a_borrow {
                Value::NaturalLit(n) => Value::NaturalLit(n + 1),
                _ => {
                    drop(f_borrow);
                    drop(a_borrow);
                    fallback(f, a)
                }
            }
        }
        Value::UnionConstructor(l, kts) => {
            Value::UnionLit(l.clone(), a, kts.clone())
        }
        _ => {
            drop(f_borrow);
            fallback(f, a)
        }
    }
}

fn squash_textlit(
    elts: impl Iterator<Item = InterpolatedTextContents<Thunk>>,
) -> Vec<InterpolatedTextContents<Thunk>> {
    use std::mem::replace;
    use InterpolatedTextContents::{Expr, Text};

    fn inner(
        elts: impl Iterator<Item = InterpolatedTextContents<Thunk>>,
        crnt_str: &mut String,
        ret: &mut Vec<InterpolatedTextContents<Thunk>>,
    ) {
        for contents in elts {
            match contents {
                Text(s) => crnt_str.push_str(&s),
                Expr(e) => {
                    let e_borrow = e.as_value();
                    match &*e_borrow {
                        Value::TextLit(elts2) => {
                            inner(elts2.iter().cloned(), crnt_str, ret)
                        }
                        _ => {
                            drop(e_borrow);
                            if !crnt_str.is_empty() {
                                ret.push(Text(replace(crnt_str, String::new())))
                            }
                            ret.push(Expr(e.clone()))
                        }
                    }
                }
            }
        }
    }

    let mut crnt_str = String::new();
    let mut ret = Vec::new();
    inner(elts, &mut crnt_str, &mut ret);
    if !crnt_str.is_empty() {
        ret.push(Text(replace(&mut crnt_str, String::new())))
    }
    ret
}

/// Reduces the imput expression to a Value. Evaluates as little as possible.
fn normalize_whnf(ctx: NormalizationContext, expr: InputSubExpr) -> Value {
    match expr.as_ref() {
        ExprF::Embed(e) => return e.to_value(),
        ExprF::Var(v) => return ctx.lookup(v),
        _ => {}
    }

    // Thunk subexpressions
    let expr: ExprF<Thunk, Label, X> =
        expr.as_ref().map_ref_with_special_handling_of_binders(
            |e| Thunk::new(ctx.clone(), e.clone()),
            |x, e| Thunk::new(ctx.skip(x), e.clone()),
            |_| unreachable!(),
            Label::clone,
        );

    normalize_one_layer(expr)
}

fn normalize_one_layer(expr: ExprF<Thunk, Label, X>) -> Value {
    use Value::{
        BoolLit, EmptyListLit, EmptyOptionalLit, IntegerLit, Lam, NEListLit,
        NEOptionalLit, NaturalLit, Pi, RecordLit, RecordType, TextLit,
        UnionConstructor, UnionLit, UnionType,
    };

    // Small helper enum to avoid repetition
    enum Ret<'a> {
        RetValue(Value),
        RetThunk(Thunk),
        RetThunkRef(&'a Thunk),
        RetExpr(ExprF<Thunk, Label, X>),
    }
    use Ret::{RetExpr, RetThunk, RetThunkRef, RetValue};

    let ret = match expr {
        ExprF::Embed(_) => unreachable!(),
        ExprF::Var(_) => unreachable!(),
        ExprF::Annot(x, _) => RetThunk(x),
        ExprF::Lam(x, t, e) => RetValue(Lam(x.into(), t, e)),
        ExprF::Pi(x, t, e) => RetValue(Pi(
            x.into(),
            TypeThunk::from_thunk(t),
            TypeThunk::from_thunk(e),
        )),
        ExprF::Let(x, _, v, b) => {
            let v = Typed::from_thunk_untyped(v);
            RetThunk(b.subst_shift(&x.into(), &v))
        }
        ExprF::App(v, a) => RetValue(v.app_thunk(a)),
        ExprF::Builtin(b) => RetValue(Value::from_builtin(b)),
        ExprF::Const(c) => RetValue(Value::Const(c)),
        ExprF::BoolLit(b) => RetValue(BoolLit(b)),
        ExprF::NaturalLit(n) => RetValue(NaturalLit(n)),
        ExprF::IntegerLit(n) => RetValue(IntegerLit(n)),
        ExprF::DoubleLit(_) => RetExpr(expr),
        ExprF::OldOptionalLit(None, t) => {
            RetValue(EmptyOptionalLit(TypeThunk::from_thunk(t)))
        }
        ExprF::OldOptionalLit(Some(e), _) => RetValue(NEOptionalLit(e)),
        ExprF::SomeLit(e) => RetValue(NEOptionalLit(e)),
        ExprF::EmptyListLit(t) => {
            RetValue(EmptyListLit(TypeThunk::from_thunk(t)))
        }
        ExprF::NEListLit(elts) => {
            RetValue(NEListLit(elts.into_iter().collect()))
        }
        ExprF::RecordLit(kvs) => RetValue(RecordLit(kvs.into_iter().collect())),
        ExprF::RecordType(kts) => RetValue(RecordType(
            kts.into_iter()
                .map(|(k, t)| (k, TypeThunk::from_thunk(t)))
                .collect(),
        )),
        ExprF::UnionLit(l, x, kts) => RetValue(UnionLit(
            l,
            x,
            kts.into_iter()
                .map(|(k, t)| (k, t.map(|t| TypeThunk::from_thunk(t))))
                .collect(),
        )),
        ExprF::UnionType(kts) => RetValue(UnionType(
            kts.into_iter()
                .map(|(k, t)| (k, t.map(|t| TypeThunk::from_thunk(t))))
                .collect(),
        )),
        ExprF::TextLit(elts) => {
            use InterpolatedTextContents::Expr;
            let elts: Vec<_> = squash_textlit(elts.into_iter());
            // Simplify bare interpolation
            if let [Expr(th)] = elts.as_slice() {
                RetThunk(th.clone())
            } else {
                RetValue(TextLit(elts))
            }
        }
        ExprF::BoolIf(ref b, ref e1, ref e2) => {
            let b_borrow = b.as_value();
            match &*b_borrow {
                BoolLit(true) => RetThunkRef(e1),
                BoolLit(false) => RetThunkRef(e2),
                _ => {
                    let e1_borrow = e1.as_value();
                    let e2_borrow = e2.as_value();
                    match (&*e1_borrow, &*e2_borrow) {
                        // Simplify `if b then True else False`
                        (BoolLit(true), BoolLit(false)) => RetThunkRef(b),
                        _ => {
                            drop(b_borrow);
                            drop(e1_borrow);
                            drop(e2_borrow);
                            RetExpr(expr)
                        }
                    }
                }
            }
        }
        ExprF::BinOp(o, ref x, ref y) => {
            use BinOp::{
                BoolAnd, BoolEQ, BoolNE, BoolOr, ListAppend, NaturalPlus,
                NaturalTimes, TextAppend,
            };
            let x_borrow = x.as_value();
            let y_borrow = y.as_value();
            match (o, &*x_borrow, &*y_borrow) {
                (BoolAnd, BoolLit(true), _) => RetThunkRef(y),
                (BoolAnd, _, BoolLit(true)) => RetThunkRef(x),
                (BoolAnd, BoolLit(false), _) => RetValue(BoolLit(false)),
                (BoolAnd, _, BoolLit(false)) => RetValue(BoolLit(false)),
                (BoolOr, BoolLit(true), _) => RetValue(BoolLit(true)),
                (BoolOr, _, BoolLit(true)) => RetValue(BoolLit(true)),
                (BoolOr, BoolLit(false), _) => RetThunkRef(y),
                (BoolOr, _, BoolLit(false)) => RetThunkRef(x),
                (BoolEQ, BoolLit(true), _) => RetThunkRef(y),
                (BoolEQ, _, BoolLit(true)) => RetThunkRef(x),
                (BoolEQ, BoolLit(x), BoolLit(y)) => RetValue(BoolLit(x == y)),
                (BoolNE, BoolLit(false), _) => RetThunkRef(y),
                (BoolNE, _, BoolLit(false)) => RetThunkRef(x),
                (BoolNE, BoolLit(x), BoolLit(y)) => RetValue(BoolLit(x != y)),

                (NaturalPlus, NaturalLit(0), _) => RetThunkRef(y),
                (NaturalPlus, _, NaturalLit(0)) => RetThunkRef(x),
                (NaturalPlus, NaturalLit(x), NaturalLit(y)) => {
                    RetValue(NaturalLit(x + y))
                }
                (NaturalTimes, NaturalLit(0), _) => RetValue(NaturalLit(0)),
                (NaturalTimes, _, NaturalLit(0)) => RetValue(NaturalLit(0)),
                (NaturalTimes, NaturalLit(1), _) => RetThunkRef(y),
                (NaturalTimes, _, NaturalLit(1)) => RetThunkRef(x),
                (NaturalTimes, NaturalLit(x), NaturalLit(y)) => {
                    RetValue(NaturalLit(x * y))
                }

                (ListAppend, EmptyListLit(_), _) => RetThunkRef(y),
                (ListAppend, _, EmptyListLit(_)) => RetThunkRef(x),
                (ListAppend, NEListLit(xs), NEListLit(ys)) => RetValue(
                    NEListLit(xs.iter().chain(ys.iter()).cloned().collect()),
                ),

                (TextAppend, TextLit(x), _) if x.is_empty() => RetThunkRef(y),
                (TextAppend, _, TextLit(y)) if y.is_empty() => RetThunkRef(x),
                (TextAppend, TextLit(x), TextLit(y)) => RetValue(TextLit(
                    x.iter().chain(y.iter()).cloned().collect(),
                )),
                (TextAppend, TextLit(x), _) => {
                    use std::iter::once;
                    let y = InterpolatedTextContents::Expr(y.clone());
                    RetValue(TextLit(
                        x.iter().cloned().chain(once(y)).collect(),
                    ))
                }
                (TextAppend, _, TextLit(y)) => {
                    use std::iter::once;
                    let x = InterpolatedTextContents::Expr(x.clone());
                    RetValue(TextLit(
                        once(x).chain(y.iter().cloned()).collect(),
                    ))
                }

                _ => {
                    drop(x_borrow);
                    drop(y_borrow);
                    RetExpr(expr)
                }
            }
        }

        ExprF::Projection(_, ls) if ls.is_empty() => {
            RetValue(RecordLit(std::collections::BTreeMap::new()))
        }
        ExprF::Projection(ref v, ref ls) => {
            let v_borrow = v.as_value();
            match &*v_borrow {
                RecordLit(kvs) => RetValue(RecordLit(
                    ls.iter()
                        .filter_map(|l| {
                            kvs.get(l).map(|x| (l.clone(), x.clone()))
                        })
                        .collect(),
                )),
                _ => {
                    drop(v_borrow);
                    RetExpr(expr)
                }
            }
        }
        ExprF::Field(ref v, ref l) => {
            let v_borrow = v.as_value();
            match &*v_borrow {
                RecordLit(kvs) => match kvs.get(l) {
                    Some(r) => RetThunk(r.clone()),
                    None => {
                        drop(v_borrow);
                        RetExpr(expr)
                    }
                },
                UnionType(kts) => {
                    RetValue(UnionConstructor(l.clone(), kts.clone()))
                }
                _ => {
                    drop(v_borrow);
                    RetExpr(expr)
                }
            }
        }

        ExprF::Merge(ref handlers, ref variant, _) => {
            let handlers_borrow = handlers.as_value();
            let variant_borrow = variant.as_value();
            match (&*handlers_borrow, &*variant_borrow) {
                (RecordLit(kvs), UnionConstructor(l, _)) => match kvs.get(l) {
                    Some(h) => RetThunk(h.clone()),
                    None => {
                        drop(handlers_borrow);
                        drop(variant_borrow);
                        RetExpr(expr)
                    }
                },
                (RecordLit(kvs), UnionLit(l, v, _)) => match kvs.get(l) {
                    Some(h) => RetValue(h.app_thunk(v.clone())),
                    None => {
                        drop(handlers_borrow);
                        drop(variant_borrow);
                        RetExpr(expr)
                    }
                },
                _ => {
                    drop(handlers_borrow);
                    drop(variant_borrow);
                    RetExpr(expr)
                }
            }
        }
    };

    match ret {
        RetValue(v) => v,
        RetThunk(th) => th.to_value(),
        RetThunkRef(th) => th.to_value(),
        RetExpr(expr) => Value::PartialExpr(expr),
    }
}

#[cfg(test)]
mod spec_tests {
    #![rustfmt::skip]

    macro_rules! norm {
        ($name:ident, $path:expr) => {
            make_spec_test!(Normalization, Success, $name, $path);
        };
    }

    macro_rules! alpha_norm {
        ($name:ident, $path:expr) => {
            make_spec_test!(AlphaNormalization, Success, $name, $path);
        };
    }

    norm!(success_haskell_tutorial_access_0, "haskell-tutorial/access/0");
    norm!(success_haskell_tutorial_access_1, "haskell-tutorial/access/1");
    // norm!(success_haskell_tutorial_combineTypes_0, "haskell-tutorial/combineTypes/0");
    // norm!(success_haskell_tutorial_combineTypes_1, "haskell-tutorial/combineTypes/1");
    // norm!(success_haskell_tutorial_prefer_0, "haskell-tutorial/prefer/0");
    norm!(success_haskell_tutorial_projection_0, "haskell-tutorial/projection/0");

    norm!(success_prelude_Bool_and_0, "prelude/Bool/and/0");
    norm!(success_prelude_Bool_and_1, "prelude/Bool/and/1");
    norm!(success_prelude_Bool_build_0, "prelude/Bool/build/0");
    norm!(success_prelude_Bool_build_1, "prelude/Bool/build/1");
    norm!(success_prelude_Bool_even_0, "prelude/Bool/even/0");
    norm!(success_prelude_Bool_even_1, "prelude/Bool/even/1");
    norm!(success_prelude_Bool_even_2, "prelude/Bool/even/2");
    norm!(success_prelude_Bool_even_3, "prelude/Bool/even/3");
    norm!(success_prelude_Bool_fold_0, "prelude/Bool/fold/0");
    norm!(success_prelude_Bool_fold_1, "prelude/Bool/fold/1");
    norm!(success_prelude_Bool_not_0, "prelude/Bool/not/0");
    norm!(success_prelude_Bool_not_1, "prelude/Bool/not/1");
    norm!(success_prelude_Bool_odd_0, "prelude/Bool/odd/0");
    norm!(success_prelude_Bool_odd_1, "prelude/Bool/odd/1");
    norm!(success_prelude_Bool_odd_2, "prelude/Bool/odd/2");
    norm!(success_prelude_Bool_odd_3, "prelude/Bool/odd/3");
    norm!(success_prelude_Bool_or_0, "prelude/Bool/or/0");
    norm!(success_prelude_Bool_or_1, "prelude/Bool/or/1");
    norm!(success_prelude_Bool_show_0, "prelude/Bool/show/0");
    norm!(success_prelude_Bool_show_1, "prelude/Bool/show/1");
    // norm!(success_prelude_Double_show_0, "prelude/Double/show/0");
    // norm!(success_prelude_Double_show_1, "prelude/Double/show/1");
    // norm!(success_prelude_Integer_show_0, "prelude/Integer/show/0");
    // norm!(success_prelude_Integer_show_1, "prelude/Integer/show/1");
    // norm!(success_prelude_Integer_toDouble_0, "prelude/Integer/toDouble/0");
    // norm!(success_prelude_Integer_toDouble_1, "prelude/Integer/toDouble/1");
    norm!(success_prelude_List_all_0, "prelude/List/all/0");
    norm!(success_prelude_List_all_1, "prelude/List/all/1");
    norm!(success_prelude_List_any_0, "prelude/List/any/0");
    norm!(success_prelude_List_any_1, "prelude/List/any/1");
    norm!(success_prelude_List_build_0, "prelude/List/build/0");
    norm!(success_prelude_List_build_1, "prelude/List/build/1");
    norm!(success_prelude_List_concat_0, "prelude/List/concat/0");
    norm!(success_prelude_List_concat_1, "prelude/List/concat/1");
    norm!(success_prelude_List_concatMap_0, "prelude/List/concatMap/0");
    norm!(success_prelude_List_concatMap_1, "prelude/List/concatMap/1");
    norm!(success_prelude_List_filter_0, "prelude/List/filter/0");
    norm!(success_prelude_List_filter_1, "prelude/List/filter/1");
    norm!(success_prelude_List_fold_0, "prelude/List/fold/0");
    norm!(success_prelude_List_fold_1, "prelude/List/fold/1");
    norm!(success_prelude_List_fold_2, "prelude/List/fold/2");
    norm!(success_prelude_List_generate_0, "prelude/List/generate/0");
    norm!(success_prelude_List_generate_1, "prelude/List/generate/1");
    norm!(success_prelude_List_head_0, "prelude/List/head/0");
    norm!(success_prelude_List_head_1, "prelude/List/head/1");
    norm!(success_prelude_List_indexed_0, "prelude/List/indexed/0");
    norm!(success_prelude_List_indexed_1, "prelude/List/indexed/1");
    norm!(success_prelude_List_iterate_0, "prelude/List/iterate/0");
    norm!(success_prelude_List_iterate_1, "prelude/List/iterate/1");
    norm!(success_prelude_List_last_0, "prelude/List/last/0");
    norm!(success_prelude_List_last_1, "prelude/List/last/1");
    norm!(success_prelude_List_length_0, "prelude/List/length/0");
    norm!(success_prelude_List_length_1, "prelude/List/length/1");
    norm!(success_prelude_List_map_0, "prelude/List/map/0");
    norm!(success_prelude_List_map_1, "prelude/List/map/1");
    norm!(success_prelude_List_null_0, "prelude/List/null/0");
    norm!(success_prelude_List_null_1, "prelude/List/null/1");
    norm!(success_prelude_List_replicate_0, "prelude/List/replicate/0");
    norm!(success_prelude_List_replicate_1, "prelude/List/replicate/1");
    norm!(success_prelude_List_reverse_0, "prelude/List/reverse/0");
    norm!(success_prelude_List_reverse_1, "prelude/List/reverse/1");
    norm!(success_prelude_List_shifted_0, "prelude/List/shifted/0");
    norm!(success_prelude_List_shifted_1, "prelude/List/shifted/1");
    norm!(success_prelude_List_unzip_0, "prelude/List/unzip/0");
    norm!(success_prelude_List_unzip_1, "prelude/List/unzip/1");
    norm!(success_prelude_Natural_build_0, "prelude/Natural/build/0");
    norm!(success_prelude_Natural_build_1, "prelude/Natural/build/1");
    norm!(success_prelude_Natural_enumerate_0, "prelude/Natural/enumerate/0");
    norm!(success_prelude_Natural_enumerate_1, "prelude/Natural/enumerate/1");
    norm!(success_prelude_Natural_even_0, "prelude/Natural/even/0");
    norm!(success_prelude_Natural_even_1, "prelude/Natural/even/1");
    norm!(success_prelude_Natural_fold_0, "prelude/Natural/fold/0");
    norm!(success_prelude_Natural_fold_1, "prelude/Natural/fold/1");
    norm!(success_prelude_Natural_fold_2, "prelude/Natural/fold/2");
    norm!(success_prelude_Natural_isZero_0, "prelude/Natural/isZero/0");
    norm!(success_prelude_Natural_isZero_1, "prelude/Natural/isZero/1");
    norm!(success_prelude_Natural_odd_0, "prelude/Natural/odd/0");
    norm!(success_prelude_Natural_odd_1, "prelude/Natural/odd/1");
    norm!(success_prelude_Natural_product_0, "prelude/Natural/product/0");
    norm!(success_prelude_Natural_product_1, "prelude/Natural/product/1");
    norm!(success_prelude_Natural_show_0, "prelude/Natural/show/0");
    norm!(success_prelude_Natural_show_1, "prelude/Natural/show/1");
    norm!(success_prelude_Natural_sum_0, "prelude/Natural/sum/0");
    norm!(success_prelude_Natural_sum_1, "prelude/Natural/sum/1");
    // norm!(success_prelude_Natural_toDouble_0, "prelude/Natural/toDouble/0");
    // norm!(success_prelude_Natural_toDouble_1, "prelude/Natural/toDouble/1");
    norm!(success_prelude_Natural_toInteger_0, "prelude/Natural/toInteger/0");
    norm!(success_prelude_Natural_toInteger_1, "prelude/Natural/toInteger/1");
    norm!(success_prelude_Optional_all_0, "prelude/Optional/all/0");
    norm!(success_prelude_Optional_all_1, "prelude/Optional/all/1");
    norm!(success_prelude_Optional_any_0, "prelude/Optional/any/0");
    norm!(success_prelude_Optional_any_1, "prelude/Optional/any/1");
    norm!(success_prelude_Optional_build_0, "prelude/Optional/build/0");
    norm!(success_prelude_Optional_build_1, "prelude/Optional/build/1");
    norm!(success_prelude_Optional_concat_0, "prelude/Optional/concat/0");
    norm!(success_prelude_Optional_concat_1, "prelude/Optional/concat/1");
    norm!(success_prelude_Optional_concat_2, "prelude/Optional/concat/2");
    norm!(success_prelude_Optional_filter_0, "prelude/Optional/filter/0");
    norm!(success_prelude_Optional_filter_1, "prelude/Optional/filter/1");
    norm!(success_prelude_Optional_fold_0, "prelude/Optional/fold/0");
    norm!(success_prelude_Optional_fold_1, "prelude/Optional/fold/1");
    norm!(success_prelude_Optional_head_0, "prelude/Optional/head/0");
    norm!(success_prelude_Optional_head_1, "prelude/Optional/head/1");
    norm!(success_prelude_Optional_head_2, "prelude/Optional/head/2");
    norm!(success_prelude_Optional_last_0, "prelude/Optional/last/0");
    norm!(success_prelude_Optional_last_1, "prelude/Optional/last/1");
    norm!(success_prelude_Optional_last_2, "prelude/Optional/last/2");
    norm!(success_prelude_Optional_length_0, "prelude/Optional/length/0");
    norm!(success_prelude_Optional_length_1, "prelude/Optional/length/1");
    norm!(success_prelude_Optional_map_0, "prelude/Optional/map/0");
    norm!(success_prelude_Optional_map_1, "prelude/Optional/map/1");
    norm!(success_prelude_Optional_null_0, "prelude/Optional/null/0");
    norm!(success_prelude_Optional_null_1, "prelude/Optional/null/1");
    norm!(success_prelude_Optional_toList_0, "prelude/Optional/toList/0");
    norm!(success_prelude_Optional_toList_1, "prelude/Optional/toList/1");
    norm!(success_prelude_Optional_unzip_0, "prelude/Optional/unzip/0");
    norm!(success_prelude_Optional_unzip_1, "prelude/Optional/unzip/1");
    norm!(success_prelude_Text_concat_0, "prelude/Text/concat/0");
    norm!(success_prelude_Text_concat_1, "prelude/Text/concat/1");
    norm!(success_prelude_Text_concatMap_0, "prelude/Text/concatMap/0");
    norm!(success_prelude_Text_concatMap_1, "prelude/Text/concatMap/1");
    // norm!(success_prelude_Text_concatMapSep_0, "prelude/Text/concatMapSep/0");
    // norm!(success_prelude_Text_concatMapSep_1, "prelude/Text/concatMapSep/1");
    // norm!(success_prelude_Text_concatSep_0, "prelude/Text/concatSep/0");
    // norm!(success_prelude_Text_concatSep_1, "prelude/Text/concatSep/1");
    // norm!(success_prelude_Text_show_0, "prelude/Text/show/0");
    // norm!(success_prelude_Text_show_1, "prelude/Text/show/1");
    // norm!(success_remoteSystems, "remoteSystems");

    // norm!(success_simple_doubleShow, "simple/doubleShow");
    norm!(success_simple_enum, "simple/enum");
    // norm!(success_simple_integerShow, "simple/integerShow");
    // norm!(success_simple_integerToDouble, "simple/integerToDouble");
    norm!(success_simple_letlet, "simple/letlet");
    norm!(success_simple_listBuild, "simple/listBuild");
    norm!(success_simple_multiLine, "simple/multiLine");
    norm!(success_simple_naturalBuild, "simple/naturalBuild");
    norm!(success_simple_naturalPlus, "simple/naturalPlus");
    norm!(success_simple_naturalShow, "simple/naturalShow");
    norm!(success_simple_naturalToInteger, "simple/naturalToInteger");
    norm!(success_simple_optionalBuild, "simple/optionalBuild");
    norm!(success_simple_optionalBuildFold, "simple/optionalBuildFold");
    norm!(success_simple_optionalFold, "simple/optionalFold");
    // norm!(success_simple_sortOperator, "simple/sortOperator");
    // norm!(success_simplifications_and, "simplifications/and");
    // norm!(success_simplifications_eq, "simplifications/eq");
    // norm!(success_simplifications_ifThenElse, "simplifications/ifThenElse");
    // norm!(success_simplifications_ne, "simplifications/ne");
    // norm!(success_simplifications_or, "simplifications/or");

    norm!(success_unit_Bool, "unit/Bool");
    norm!(success_unit_Double, "unit/Double");
    norm!(success_unit_DoubleLiteral, "unit/DoubleLiteral");
    norm!(success_unit_DoubleShow, "unit/DoubleShow");
    // norm!(success_unit_DoubleShowValue, "unit/DoubleShowValue");
    norm!(success_unit_EmptyAlternative, "unit/EmptyAlternative");
    norm!(success_unit_FunctionApplicationCapture, "unit/FunctionApplicationCapture");
    norm!(success_unit_FunctionApplicationNoSubstitute, "unit/FunctionApplicationNoSubstitute");
    norm!(success_unit_FunctionApplicationNormalizeArguments, "unit/FunctionApplicationNormalizeArguments");
    norm!(success_unit_FunctionApplicationSubstitute, "unit/FunctionApplicationSubstitute");
    norm!(success_unit_FunctionNormalizeArguments, "unit/FunctionNormalizeArguments");
    norm!(success_unit_FunctionTypeNormalizeArguments, "unit/FunctionTypeNormalizeArguments");
    // norm!(success_unit_IfAlternativesIdentical, "unit/IfAlternativesIdentical");
    norm!(success_unit_IfFalse, "unit/IfFalse");
    norm!(success_unit_IfNormalizePredicateAndBranches, "unit/IfNormalizePredicateAndBranches");
    norm!(success_unit_IfTrivial, "unit/IfTrivial");
    norm!(success_unit_IfTrue, "unit/IfTrue");
    norm!(success_unit_Integer, "unit/Integer");
    norm!(success_unit_IntegerNegative, "unit/IntegerNegative");
    norm!(success_unit_IntegerPositive, "unit/IntegerPositive");
    // norm!(success_unit_IntegerShow_12, "unit/IntegerShow-12");
    // norm!(success_unit_IntegerShow12, "unit/IntegerShow12");
    norm!(success_unit_IntegerShow, "unit/IntegerShow");
    // norm!(success_unit_IntegerToDouble_12, "unit/IntegerToDouble-12");
    // norm!(success_unit_IntegerToDouble12, "unit/IntegerToDouble12");
    norm!(success_unit_IntegerToDouble, "unit/IntegerToDouble");
    norm!(success_unit_Kind, "unit/Kind");
    norm!(success_unit_Let, "unit/Let");
    norm!(success_unit_LetWithType, "unit/LetWithType");
    norm!(success_unit_List, "unit/List");
    norm!(success_unit_ListBuild, "unit/ListBuild");
    norm!(success_unit_ListBuildFoldFusion, "unit/ListBuildFoldFusion");
    norm!(success_unit_ListBuildImplementation, "unit/ListBuildImplementation");
    norm!(success_unit_ListFold, "unit/ListFold");
    norm!(success_unit_ListFoldEmpty, "unit/ListFoldEmpty");
    norm!(success_unit_ListFoldOne, "unit/ListFoldOne");
    norm!(success_unit_ListHead, "unit/ListHead");
    norm!(success_unit_ListHeadEmpty, "unit/ListHeadEmpty");
    norm!(success_unit_ListHeadOne, "unit/ListHeadOne");
    norm!(success_unit_ListIndexed, "unit/ListIndexed");
    norm!(success_unit_ListIndexedEmpty, "unit/ListIndexedEmpty");
    norm!(success_unit_ListIndexedOne, "unit/ListIndexedOne");
    norm!(success_unit_ListLast, "unit/ListLast");
    norm!(success_unit_ListLastEmpty, "unit/ListLastEmpty");
    norm!(success_unit_ListLastOne, "unit/ListLastOne");
    norm!(success_unit_ListLength, "unit/ListLength");
    norm!(success_unit_ListLengthEmpty, "unit/ListLengthEmpty");
    norm!(success_unit_ListLengthOne, "unit/ListLengthOne");
    norm!(success_unit_ListNormalizeElements, "unit/ListNormalizeElements");
    norm!(success_unit_ListNormalizeTypeAnnotation, "unit/ListNormalizeTypeAnnotation");
    norm!(success_unit_ListReverse, "unit/ListReverse");
    norm!(success_unit_ListReverseEmpty, "unit/ListReverseEmpty");
    norm!(success_unit_ListReverseTwo, "unit/ListReverseTwo");
    norm!(success_unit_Merge, "unit/Merge");
    norm!(success_unit_MergeEmptyAlternative, "unit/MergeEmptyAlternative");
    norm!(success_unit_MergeNormalizeArguments, "unit/MergeNormalizeArguments");
    norm!(success_unit_MergeWithType, "unit/MergeWithType");
    norm!(success_unit_MergeWithTypeNormalizeArguments, "unit/MergeWithTypeNormalizeArguments");
    norm!(success_unit_Natural, "unit/Natural");
    norm!(success_unit_NaturalBuild, "unit/NaturalBuild");
    norm!(success_unit_NaturalBuildFoldFusion, "unit/NaturalBuildFoldFusion");
    norm!(success_unit_NaturalBuildImplementation, "unit/NaturalBuildImplementation");
    norm!(success_unit_NaturalEven, "unit/NaturalEven");
    norm!(success_unit_NaturalEvenOne, "unit/NaturalEvenOne");
    norm!(success_unit_NaturalEvenZero, "unit/NaturalEvenZero");
    norm!(success_unit_NaturalFold, "unit/NaturalFold");
    norm!(success_unit_NaturalFoldOne, "unit/NaturalFoldOne");
    norm!(success_unit_NaturalFoldZero, "unit/NaturalFoldZero");
    norm!(success_unit_NaturalIsZero, "unit/NaturalIsZero");
    norm!(success_unit_NaturalIsZeroOne, "unit/NaturalIsZeroOne");
    norm!(success_unit_NaturalIsZeroZero, "unit/NaturalIsZeroZero");
    norm!(success_unit_NaturalLiteral, "unit/NaturalLiteral");
    norm!(success_unit_NaturalOdd, "unit/NaturalOdd");
    norm!(success_unit_NaturalOddOne, "unit/NaturalOddOne");
    norm!(success_unit_NaturalOddZero, "unit/NaturalOddZero");
    norm!(success_unit_NaturalShow, "unit/NaturalShow");
    norm!(success_unit_NaturalShowOne, "unit/NaturalShowOne");
    norm!(success_unit_NaturalToInteger, "unit/NaturalToInteger");
    norm!(success_unit_NaturalToIntegerOne, "unit/NaturalToIntegerOne");
    norm!(success_unit_None, "unit/None");
    norm!(success_unit_NoneNatural, "unit/NoneNatural");
    // norm!(success_unit_OperatorAndEquivalentArguments, "unit/OperatorAndEquivalentArguments");
    norm!(success_unit_OperatorAndLhsFalse, "unit/OperatorAndLhsFalse");
    norm!(success_unit_OperatorAndLhsTrue, "unit/OperatorAndLhsTrue");
    norm!(success_unit_OperatorAndNormalizeArguments, "unit/OperatorAndNormalizeArguments");
    norm!(success_unit_OperatorAndRhsFalse, "unit/OperatorAndRhsFalse");
    norm!(success_unit_OperatorAndRhsTrue, "unit/OperatorAndRhsTrue");
    // norm!(success_unit_OperatorEqualEquivalentArguments, "unit/OperatorEqualEquivalentArguments");
    norm!(success_unit_OperatorEqualLhsTrue, "unit/OperatorEqualLhsTrue");
    norm!(success_unit_OperatorEqualNormalizeArguments, "unit/OperatorEqualNormalizeArguments");
    norm!(success_unit_OperatorEqualRhsTrue, "unit/OperatorEqualRhsTrue");
    norm!(success_unit_OperatorListConcatenateLhsEmpty, "unit/OperatorListConcatenateLhsEmpty");
    norm!(success_unit_OperatorListConcatenateListList, "unit/OperatorListConcatenateListList");
    norm!(success_unit_OperatorListConcatenateNormalizeArguments, "unit/OperatorListConcatenateNormalizeArguments");
    norm!(success_unit_OperatorListConcatenateRhsEmpty, "unit/OperatorListConcatenateRhsEmpty");
    // norm!(success_unit_OperatorNotEqualEquivalentArguments, "unit/OperatorNotEqualEquivalentArguments");
    norm!(success_unit_OperatorNotEqualLhsFalse, "unit/OperatorNotEqualLhsFalse");
    norm!(success_unit_OperatorNotEqualNormalizeArguments, "unit/OperatorNotEqualNormalizeArguments");
    norm!(success_unit_OperatorNotEqualRhsFalse, "unit/OperatorNotEqualRhsFalse");
    // norm!(success_unit_OperatorOrEquivalentArguments, "unit/OperatorOrEquivalentArguments");
    norm!(success_unit_OperatorOrLhsFalse, "unit/OperatorOrLhsFalse");
    norm!(success_unit_OperatorOrLhsTrue, "unit/OperatorOrLhsTrue");
    norm!(success_unit_OperatorOrNormalizeArguments, "unit/OperatorOrNormalizeArguments");
    norm!(success_unit_OperatorOrRhsFalse, "unit/OperatorOrRhsFalse");
    norm!(success_unit_OperatorOrRhsTrue, "unit/OperatorOrRhsTrue");
    norm!(success_unit_OperatorPlusLhsZero, "unit/OperatorPlusLhsZero");
    norm!(success_unit_OperatorPlusNormalizeArguments, "unit/OperatorPlusNormalizeArguments");
    norm!(success_unit_OperatorPlusOneAndOne, "unit/OperatorPlusOneAndOne");
    norm!(success_unit_OperatorPlusRhsZero, "unit/OperatorPlusRhsZero");
    norm!(success_unit_OperatorTextConcatenateLhsEmpty, "unit/OperatorTextConcatenateLhsEmpty");
    norm!(success_unit_OperatorTextConcatenateLhsNonEmpty, "unit/OperatorTextConcatenateLhsNonEmpty");
    norm!(success_unit_OperatorTextConcatenateTextText, "unit/OperatorTextConcatenateTextText");
    norm!(success_unit_OperatorTimesLhsOne, "unit/OperatorTimesLhsOne");
    norm!(success_unit_OperatorTimesLhsZero, "unit/OperatorTimesLhsZero");
    norm!(success_unit_OperatorTimesNormalizeArguments, "unit/OperatorTimesNormalizeArguments");
    norm!(success_unit_OperatorTimesRhsOne, "unit/OperatorTimesRhsOne");
    norm!(success_unit_OperatorTimesRhsZero, "unit/OperatorTimesRhsZero");
    norm!(success_unit_OperatorTimesTwoAndTwo, "unit/OperatorTimesTwoAndTwo");
    norm!(success_unit_Optional, "unit/Optional");
    norm!(success_unit_OptionalBuild, "unit/OptionalBuild");
    norm!(success_unit_OptionalBuildFoldFusion, "unit/OptionalBuildFoldFusion");
    norm!(success_unit_OptionalBuildImplementation, "unit/OptionalBuildImplementation");
    norm!(success_unit_OptionalFold, "unit/OptionalFold");
    norm!(success_unit_OptionalFoldNone, "unit/OptionalFoldNone");
    norm!(success_unit_OptionalFoldSome, "unit/OptionalFoldSome");
    norm!(success_unit_Record, "unit/Record");
    norm!(success_unit_RecordEmpty, "unit/RecordEmpty");
    norm!(success_unit_RecordProjection, "unit/RecordProjection");
    norm!(success_unit_RecordProjectionEmpty, "unit/RecordProjectionEmpty");
    norm!(success_unit_RecordProjectionNormalizeArguments, "unit/RecordProjectionNormalizeArguments");
    norm!(success_unit_RecordSelection, "unit/RecordSelection");
    norm!(success_unit_RecordSelectionNormalizeArguments, "unit/RecordSelectionNormalizeArguments");
    norm!(success_unit_RecordType, "unit/RecordType");
    norm!(success_unit_RecordTypeEmpty, "unit/RecordTypeEmpty");
    // norm!(success_unit_RecursiveRecordMergeCollision, "unit/RecursiveRecordMergeCollision");
    // norm!(success_unit_RecursiveRecordMergeLhsEmpty, "unit/RecursiveRecordMergeLhsEmpty");
    // norm!(success_unit_RecursiveRecordMergeNoCollision, "unit/RecursiveRecordMergeNoCollision");
    // norm!(success_unit_RecursiveRecordMergeNormalizeArguments, "unit/RecursiveRecordMergeNormalizeArguments");
    // norm!(success_unit_RecursiveRecordMergeRhsEmpty, "unit/RecursiveRecordMergeRhsEmpty");
    // norm!(success_unit_RecursiveRecordTypeMergeCollision, "unit/RecursiveRecordTypeMergeCollision");
    // norm!(success_unit_RecursiveRecordTypeMergeLhsEmpty, "unit/RecursiveRecordTypeMergeLhsEmpty");
    // norm!(success_unit_RecursiveRecordTypeMergeNoCollision, "unit/RecursiveRecordTypeMergeNoCollision");
    // norm!(success_unit_RecursiveRecordTypeMergeNormalizeArguments, "unit/RecursiveRecordTypeMergeNormalizeArguments");
    // norm!(success_unit_RecursiveRecordTypeMergeRhsEmpty, "unit/RecursiveRecordTypeMergeRhsEmpty");
    // norm!(success_unit_RecursiveRecordTypeMergeSorts, "unit/RecursiveRecordTypeMergeSorts");
    // norm!(success_unit_RightBiasedRecordMergeCollision, "unit/RightBiasedRecordMergeCollision");
    // norm!(success_unit_RightBiasedRecordMergeLhsEmpty, "unit/RightBiasedRecordMergeLhsEmpty");
    // norm!(success_unit_RightBiasedRecordMergeNoCollision, "unit/RightBiasedRecordMergeNoCollision");
    // norm!(success_unit_RightBiasedRecordMergeNormalizeArguments, "unit/RightBiasedRecordMergeNormalizeArguments");
    // norm!(success_unit_RightBiasedRecordMergeRhsEmpty, "unit/RightBiasedRecordMergeRhsEmpty");
    norm!(success_unit_SomeNormalizeArguments, "unit/SomeNormalizeArguments");
    norm!(success_unit_Sort, "unit/Sort");
    norm!(success_unit_Text, "unit/Text");
    norm!(success_unit_TextInterpolate, "unit/TextInterpolate");
    norm!(success_unit_TextLiteral, "unit/TextLiteral");
    norm!(success_unit_TextNormalizeInterpolations, "unit/TextNormalizeInterpolations");
    norm!(success_unit_TextShow, "unit/TextShow");
    // norm!(success_unit_TextShowAllEscapes, "unit/TextShowAllEscapes");
    norm!(success_unit_True, "unit/True");
    norm!(success_unit_Type, "unit/Type");
    norm!(success_unit_TypeAnnotation, "unit/TypeAnnotation");
    norm!(success_unit_UnionNormalizeAlternatives, "unit/UnionNormalizeAlternatives");
    norm!(success_unit_UnionNormalizeArguments, "unit/UnionNormalizeArguments");
    norm!(success_unit_UnionProjectConstructor, "unit/UnionProjectConstructor");
    norm!(success_unit_UnionSortAlternatives, "unit/UnionSortAlternatives");
    norm!(success_unit_UnionType, "unit/UnionType");
    norm!(success_unit_UnionTypeEmpty, "unit/UnionTypeEmpty");
    norm!(success_unit_UnionTypeNormalizeArguments, "unit/UnionTypeNormalizeArguments");
    norm!(success_unit_Variable, "unit/Variable");

    alpha_norm!(alpha_success_unit_FunctionBindingUnderscore, "unit/FunctionBindingUnderscore");
    alpha_norm!(alpha_success_unit_FunctionBindingX, "unit/FunctionBindingX");
    alpha_norm!(alpha_success_unit_FunctionNestedBindingX, "unit/FunctionNestedBindingX");
    alpha_norm!(alpha_success_unit_FunctionTypeBindingUnderscore, "unit/FunctionTypeBindingUnderscore");
    alpha_norm!(alpha_success_unit_FunctionTypeBindingX, "unit/FunctionTypeBindingX");
    alpha_norm!(alpha_success_unit_FunctionTypeNestedBindingX, "unit/FunctionTypeNestedBindingX");
}
