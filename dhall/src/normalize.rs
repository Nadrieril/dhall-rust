#![allow(non_snake_case)]
use std::collections::BTreeMap;
use std::rc::Rc;

use dhall_core::context::Context;
use dhall_core::{
    rc, Builtin, Const, ExprF, Integer, InterpolatedText,
    InterpolatedTextContents, Label, Natural, SubExpr, V, X,
};
use dhall_generator as dhall;

use crate::expr::{Normalized, Type, Typed, TypedInternal};

type InputSubExpr = SubExpr<X, Normalized<'static>>;
type OutputSubExpr = SubExpr<X, X>;

impl<'a> Typed<'a> {
    /// Reduce an expression to its normal form, performing beta reduction
    ///
    /// `normalize` does not type-check the expression.  You may want to type-check
    /// expressions before normalizing them since normalization can convert an
    /// ill-typed expression into a well-typed expression.
    ///
    /// However, `normalize` will not fail if the expression is ill-typed and will
    /// leave ill-typed sub-expressions unevaluated.
    ///
    pub fn normalize(self) -> Normalized<'a> {
        let internal = match self.0 {
            TypedInternal::Sort => TypedInternal::Sort,
            TypedInternal::Value(thunk, t) => {
                // TODO: stupid but needed for now
                let thunk =
                    Thunk::from_normalized_expr(thunk.normalize_to_expr());
                thunk.normalize_nf();
                TypedInternal::Value(thunk, t)
            }
        };
        Normalized(internal, self.1)
    }

    pub(crate) fn shift0(&self, delta: isize, x: &Label) -> Self {
        self.shift(delta, &V(x.clone(), 0))
    }

    pub(crate) fn shift(&self, delta: isize, var: &V<Label>) -> Self {
        Typed(self.0.shift(delta, var), self.1)
    }

    pub(crate) fn subst_shift(
        &self,
        var: &V<Label>,
        val: &Typed<'static>,
    ) -> Self {
        Typed(self.0.subst_shift(var, val), self.1)
    }

    pub(crate) fn to_value(&self) -> Value {
        self.0.to_value()
    }

    pub(crate) fn to_thunk(&self) -> Thunk {
        self.0.to_thunk()
    }
}

fn apply_builtin(b: Builtin, args: Vec<Value>) -> Value {
    use dhall_core::Builtin::*;
    use Value::*;

    let ret = match b {
        OptionalNone => improved_slice_patterns::match_vec!(args;
            [t] => EmptyOptionalLit(TypeThunk::from_whnf(t)),
        ),
        NaturalIsZero => improved_slice_patterns::match_vec!(args;
            [NaturalLit(n)] => BoolLit(n == 0),
        ),
        NaturalEven => improved_slice_patterns::match_vec!(args;
            [NaturalLit(n)] => BoolLit(n % 2 == 0),
        ),
        NaturalOdd => improved_slice_patterns::match_vec!(args;
            [NaturalLit(n)] => BoolLit(n % 2 != 0),
        ),
        NaturalToInteger => improved_slice_patterns::match_vec!(args;
            [NaturalLit(n)] => IntegerLit(n as isize),
        ),
        NaturalShow => improved_slice_patterns::match_vec!(args;
            [NaturalLit(n)] => {
                TextLit(vec![InterpolatedTextContents::Text(n.to_string())])
            }
        ),
        ListLength => improved_slice_patterns::match_vec!(args;
           [_, EmptyListLit(_)] => NaturalLit(0),
           [_, NEListLit(xs)] => NaturalLit(xs.len()),
        ),
        ListHead => improved_slice_patterns::match_vec!(args;
            [_, EmptyListLit(n)] => EmptyOptionalLit(n),
            [_, NEListLit(xs)] => {
                NEOptionalLit(xs.into_iter().next().unwrap())
            }
        ),
        ListLast => improved_slice_patterns::match_vec!(args;
            [_, EmptyListLit(n)] => EmptyOptionalLit(n),
            [_, NEListLit(xs)] => {
                NEOptionalLit(xs.into_iter().rev().next().unwrap())
            }
        ),
        ListReverse => improved_slice_patterns::match_vec!(args;
            [_, EmptyListLit(n)] => EmptyListLit(n),
            [_, NEListLit(xs)] => {
                let mut xs = xs;
                xs.reverse();
                NEListLit(xs)
            }
        ),
        ListIndexed => improved_slice_patterns::match_vec!(args;
            [_, EmptyListLit(t)] => {
                let mut kts = BTreeMap::new();
                kts.insert(
                    "index".into(),
                    TypeThunk::from_whnf(
                        Value::from_builtin(Natural)
                    ),
                );
                kts.insert("value".into(), t);
                EmptyListLit(TypeThunk::from_whnf(RecordType(kts)))
            },
            [_, NEListLit(xs)] => {
                let xs = xs
                    .into_iter()
                    .enumerate()
                    .map(|(i, e)| {
                        let i = NaturalLit(i);
                        let mut kvs = BTreeMap::new();
                        kvs.insert("index".into(), Thunk::from_whnf(i));
                        kvs.insert("value".into(), e);
                        Thunk::from_whnf(RecordLit(kvs))
                    })
                    .collect();
                NEListLit(xs)
            }
        ),
        ListBuild => improved_slice_patterns::match_vec!(args;
            // fold/build fusion
            [_, Value::AppliedBuiltin(ListFold, args)] => {
                let mut args = args;
                if args.len() >= 2 {
                    args.remove(1)
                } else {
                    // Do we really need to handle this case ?
                    unimplemented!()
                }
            },
            [t, g] => g
                .app(Value::from_builtin(List).app(t.clone()))
                .app(ListConsClosure(TypeThunk::from_whnf(t.clone()), None))
                .app(EmptyListLit(TypeThunk::from_whnf(t))),
        ),
        ListFold => improved_slice_patterns::match_vec!(args;
            // fold/build fusion
            [_, Value::AppliedBuiltin(ListBuild, args)] => {
                let mut args = args;
                if args.len() >= 2 {
                    args.remove(1)
                } else {
                    unimplemented!()
                }
            },
            [_, EmptyListLit(_), _, _, nil] => nil,
            [_, NEListLit(xs), _, cons, nil] => {
                let mut v = nil;
                for x in xs.into_iter().rev() {
                    v = cons.clone().app_thunk(x).app(v);
                }
                v
            }
        ),
        OptionalBuild => improved_slice_patterns::match_vec!(args;
            // fold/build fusion
            [_, Value::AppliedBuiltin(OptionalFold, args)] => {
                let mut args = args;
                if args.len() >= 2 {
                    args.remove(1)
                } else {
                    unimplemented!()
                }
            },
            [t, g] => g
                .app(Value::from_builtin(Optional).app(t.clone()))
                .app(OptionalSomeClosure(TypeThunk::from_whnf(t.clone())))
                .app(EmptyOptionalLit(TypeThunk::from_whnf(t))),
        ),
        OptionalFold => improved_slice_patterns::match_vec!(args;
            // fold/build fusion
            [_, Value::AppliedBuiltin(OptionalBuild, args)] => {
                let mut args = args;
                if args.len() >= 2 {
                    args.remove(1)
                } else {
                    unimplemented!()
                }
            },
            [_, EmptyOptionalLit(_), _, _, nothing] => {
                nothing
            },
            [_, NEOptionalLit(x), _, just, _] => {
                just.app_thunk(x)
            }
        ),
        NaturalBuild => improved_slice_patterns::match_vec!(args;
            // fold/build fusion
            [Value::AppliedBuiltin(NaturalFold, args)] => {
                let mut args = args;
                if args.len() >= 1 {
                    args.remove(0)
                } else {
                    unimplemented!()
                }
            },
            [g] => g
                .app(Value::from_builtin(Natural))
                .app(NaturalSuccClosure)
                .app(NaturalLit(0)),
        ),
        NaturalFold => improved_slice_patterns::match_vec!(args;
            // fold/build fusion
            [Value::AppliedBuiltin(NaturalBuild, args)] => {
                let mut args = args;
                if args.len() >= 1 {
                    args.remove(0)
                } else {
                    unimplemented!()
                }
            },
            [NaturalLit(0), _, _, zero] => zero,
            [NaturalLit(n), t, succ, zero] => {
                let fold = Value::from_builtin(NaturalFold)
                    .app(NaturalLit(n - 1))
                    .app(t)
                    .app(succ.clone())
                    .app(zero);
                succ.app(fold)
            },
        ),
        _ => Err(args),
    };

    match ret {
        Ok(x) => x,
        Err(args) => AppliedBuiltin(b, args),
    }
}

#[derive(Debug, Clone)]
enum EnvItem {
    Thunk(Thunk),
    Skip(V<Label>),
}

impl EnvItem {
    fn shift0(&self, delta: isize, x: &Label) -> Self {
        self.shift(delta, &V(x.clone(), 0))
    }

    fn shift(&self, delta: isize, var: &V<Label>) -> Self {
        use EnvItem::*;
        match self {
            Thunk(e) => Thunk(e.shift(delta, var)),
            Skip(v) => Skip(v.shift(delta, var)),
        }
    }

    pub(crate) fn subst_shift(
        &self,
        var: &V<Label>,
        val: &Typed<'static>,
    ) -> Self {
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
    fn insert(&self, x: &Label, e: Thunk) -> Self {
        NormalizationContext(Rc::new(
            self.0.insert(x.clone(), EnvItem::Thunk(e)),
        ))
    }
    fn skip(&self, x: &Label) -> Self {
        NormalizationContext(Rc::new(
            self.0
                .map(|_, e| e.shift0(1, x))
                .insert(x.clone(), EnvItem::Skip(V(x.clone(), 0))),
        ))
    }
    fn lookup(&self, var: &V<Label>) -> Value {
        let V(x, n) = var;
        match self.0.lookup(x, *n) {
            Some(EnvItem::Thunk(t)) => t.normalize_whnf().clone(),
            Some(EnvItem::Skip(newvar)) => Value::Var(newvar.clone()),
            None => Value::Var(var.clone()),
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
                    Value(e) => EnvItem::Thunk(Thunk::new(
                        NormalizationContext::new(),
                        e.as_expr().embed_absurd(),
                    )),
                };
                ctx = ctx.insert(k.clone(), new_item);
            }
        }
        NormalizationContext(Rc::new(ctx))
    }

    fn shift(&self, delta: isize, var: &V<Label>) -> Self {
        NormalizationContext(Rc::new(self.0.map(|_, e| e.shift(delta, var))))
    }

    fn subst_shift(&self, var: &V<Label>, val: &Typed<'static>) -> Self {
        NormalizationContext(Rc::new(
            self.0.map(|_, e| e.subst_shift(var, val)),
        ))
    }
}

/// A semantic value.
#[derive(Debug, Clone)]
pub(crate) enum Value {
    /// Closures
    Lam(Label, Thunk, Thunk),
    AppliedBuiltin(Builtin, Vec<Value>),
    /// `λ(x: a) -> Some x`
    OptionalSomeClosure(TypeThunk),
    /// `λ(x : a) -> λ(xs : List a) -> [ x ] # xs`
    /// `λ(xs : List a) -> [ x ] # xs`
    ListConsClosure(TypeThunk, Option<Thunk>),
    /// `λ(x : Natural) -> x + 1`
    NaturalSuccClosure,
    Pi(Label, TypeThunk, TypeThunk),

    Var(V<Label>),
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
    PartialExpr(Box<ExprF<Value, Label, X, X>>),
    Expr(OutputSubExpr),
}

impl Value {
    pub(crate) fn into_thunk(self) -> Thunk {
        Thunk::from_whnf(self)
    }

    /// Convert the value back to a (normalized) syntactic expression
    pub(crate) fn normalize_to_expr(&self) -> OutputSubExpr {
        match self {
            Value::Lam(x, t, e) => rc(ExprF::Lam(
                x.clone(),
                t.normalize_to_expr(),
                e.normalize_to_expr(),
            )),
            Value::AppliedBuiltin(b, args) => {
                let mut e = rc(ExprF::Builtin(*b));
                for v in args {
                    e = rc(ExprF::App(e, v.normalize_to_expr()));
                }
                e
            }
            Value::OptionalSomeClosure(n) => {
                let a = n.normalize_to_expr();
                dhall::subexpr!(λ(x: a) -> Some x)
            }
            Value::ListConsClosure(n, None) => {
                let a = n.normalize_to_expr();
                // Avoid accidental capture of the new `x` variable
                let a1 = a.shift0(1, &"x".into());
                dhall::subexpr!(λ(x : a) -> λ(xs : List a1) -> [ x ] # xs)
            }
            Value::ListConsClosure(n, Some(v)) => {
                let v = v.normalize_to_expr();
                let a = n.normalize_to_expr();
                // Avoid accidental capture of the new `xs` variable
                let v = v.shift0(1, &"xs".into());
                dhall::subexpr!(λ(xs : List a) -> [ v ] # xs)
            }
            Value::NaturalSuccClosure => {
                dhall::subexpr!(λ(x : Natural) -> x + 1)
            }
            Value::Pi(x, t, e) => rc(ExprF::Pi(
                x.clone(),
                t.normalize_to_expr(),
                e.normalize_to_expr(),
            )),
            Value::Var(v) => rc(ExprF::Var(v.clone())),
            Value::Const(c) => rc(ExprF::Const(*c)),
            Value::BoolLit(b) => rc(ExprF::BoolLit(*b)),
            Value::NaturalLit(n) => rc(ExprF::NaturalLit(*n)),
            Value::IntegerLit(n) => rc(ExprF::IntegerLit(*n)),
            Value::EmptyOptionalLit(n) => rc(ExprF::App(
                rc(ExprF::Builtin(Builtin::OptionalNone)),
                n.normalize_to_expr(),
            )),
            Value::NEOptionalLit(n) => {
                rc(ExprF::SomeLit(n.normalize_to_expr()))
            }
            Value::EmptyListLit(n) => {
                rc(ExprF::EmptyListLit(n.normalize_to_expr()))
            }
            Value::NEListLit(elts) => rc(ExprF::NEListLit(
                elts.into_iter().map(|n| n.normalize_to_expr()).collect(),
            )),
            Value::RecordLit(kvs) => rc(ExprF::RecordLit(
                kvs.iter()
                    .map(|(k, v)| (k.clone(), v.normalize_to_expr()))
                    .collect(),
            )),
            Value::RecordType(kts) => rc(ExprF::RecordType(
                kts.iter()
                    .map(|(k, v)| (k.clone(), v.normalize_to_expr()))
                    .collect(),
            )),
            Value::UnionType(kts) => rc(ExprF::UnionType(
                kts.iter()
                    .map(|(k, v)| {
                        (k.clone(), v.as_ref().map(|v| v.normalize_to_expr()))
                    })
                    .collect(),
            )),
            Value::UnionConstructor(l, kts) => {
                let kts = kts
                    .iter()
                    .map(|(k, v)| {
                        (k.clone(), v.as_ref().map(|v| v.normalize_to_expr()))
                    })
                    .collect();
                rc(ExprF::Field(rc(ExprF::UnionType(kts)), l.clone()))
            }
            Value::UnionLit(l, v, kts) => rc(ExprF::UnionLit(
                l.clone(),
                v.normalize_to_expr(),
                kts.iter()
                    .map(|(k, v)| {
                        (k.clone(), v.as_ref().map(|v| v.normalize_to_expr()))
                    })
                    .collect(),
            )),
            Value::TextLit(elts) => {
                fn normalize_textlit(
                    elts: &Vec<InterpolatedTextContents<Thunk>>,
                ) -> InterpolatedText<OutputSubExpr> {
                    elts.iter()
                        .flat_map(|contents| {
                            use InterpolatedTextContents::{Expr, Text};
                            let new_interpolated = match contents {
                                Expr(n) => match &*n.normalize_nf() {
                                    Value::TextLit(elts2) => {
                                        normalize_textlit(elts2)
                                    }
                                    e => InterpolatedText::from((
                                        String::new(),
                                        vec![(
                                            e.normalize_to_expr(),
                                            String::new(),
                                        )],
                                    )),
                                },
                                Text(s) => InterpolatedText::from(s.clone()),
                            };
                            new_interpolated.into_iter()
                        })
                        .collect()
                }

                rc(ExprF::TextLit(normalize_textlit(elts)))
            }
            Value::PartialExpr(e) => {
                rc(e.map_ref_simple(|v| v.normalize_to_expr()))
            }
            Value::Expr(e) => e.clone(),
        }
    }

    // Deprecated
    pub(crate) fn normalize(&self) -> Value {
        match self {
            Value::Lam(x, t, e) => {
                Value::Lam(x.clone(), t.normalize(), e.normalize())
            }
            Value::AppliedBuiltin(b, args) => Value::AppliedBuiltin(
                *b,
                args.iter().map(|v| v.normalize()).collect(),
            ),
            Value::NaturalSuccClosure => Value::NaturalSuccClosure,
            Value::OptionalSomeClosure(tth) => {
                Value::OptionalSomeClosure(tth.normalize())
            }
            Value::ListConsClosure(t, v) => Value::ListConsClosure(
                t.normalize(),
                v.as_ref().map(|v| v.normalize()),
            ),
            Value::Pi(x, t, e) => {
                Value::Pi(x.clone(), t.normalize(), e.normalize())
            }
            Value::Var(v) => Value::Var(v.clone()),
            Value::Const(c) => Value::Const(*c),
            Value::BoolLit(b) => Value::BoolLit(*b),
            Value::NaturalLit(n) => Value::NaturalLit(*n),
            Value::IntegerLit(n) => Value::IntegerLit(*n),
            Value::EmptyOptionalLit(tth) => {
                Value::EmptyOptionalLit(tth.normalize())
            }
            Value::NEOptionalLit(th) => Value::NEOptionalLit(th.normalize()),
            Value::EmptyListLit(tth) => Value::EmptyListLit(tth.normalize()),
            Value::NEListLit(elts) => {
                Value::NEListLit(elts.iter().map(|v| v.normalize()).collect())
            }
            Value::RecordLit(kvs) => Value::RecordLit(
                kvs.iter()
                    .map(|(k, v)| (k.clone(), v.normalize()))
                    .collect(),
            ),
            Value::RecordType(kvs) => Value::RecordType(
                kvs.iter()
                    .map(|(k, v)| (k.clone(), v.normalize()))
                    .collect(),
            ),
            Value::UnionType(kts) => Value::UnionType(
                kts.iter()
                    .map(|(k, v)| {
                        (k.clone(), v.as_ref().map(|v| v.normalize()))
                    })
                    .collect(),
            ),
            Value::UnionConstructor(x, kts) => Value::UnionConstructor(
                x.clone(),
                kts.iter()
                    .map(|(k, v)| {
                        (k.clone(), v.as_ref().map(|v| v.normalize()))
                    })
                    .collect(),
            ),
            Value::UnionLit(x, v, kts) => Value::UnionLit(
                x.clone(),
                v.normalize(),
                kts.iter()
                    .map(|(k, v)| {
                        (k.clone(), v.as_ref().map(|v| v.normalize()))
                    })
                    .collect(),
            ),
            Value::TextLit(elts) => Value::TextLit(
                elts.iter()
                    .map(|contents| {
                        use InterpolatedTextContents::{Expr, Text};
                        match contents {
                            Expr(th) => Expr(th.normalize()),
                            Text(s) => Text(s.clone()),
                        }
                    })
                    .collect(),
            ),
            Value::PartialExpr(e) => Value::PartialExpr(Box::new(
                e.map_ref_simple(|v| v.normalize()),
            )),
            Value::Expr(e) => Value::Expr(e.clone()),
        }
    }

    pub(crate) fn normalize_mut(&mut self) {
        match self {
            Value::NaturalSuccClosure
            | Value::Var(_)
            | Value::Const(_)
            | Value::BoolLit(_)
            | Value::NaturalLit(_)
            | Value::IntegerLit(_)
            | Value::Expr(_) => {}

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
                *self = Value::PartialExpr(Box::new(
                    e.map_ref_simple(|v| v.normalize()),
                ))
            }
        }
    }

    /// Apply to a value
    pub(crate) fn app(self, val: Value) -> Value {
        self.app_thunk(val.into_thunk())
    }

    /// Apply to a thunk
    pub(crate) fn app_thunk(self, th: Thunk) -> Value {
        let fallback = |f: Value, a: Thunk| {
            Value::PartialExpr(Box::new(ExprF::App(
                f,
                a.normalize_whnf().clone(),
            )))
        };

        match self {
            Value::Lam(x, _, e) => {
                let val = Typed(
                    TypedInternal::Value(th, None),
                    std::marker::PhantomData,
                );
                e.subst_shift(&V(x, 0), &val).normalize_whnf().clone()
            }
            Value::AppliedBuiltin(b, mut args) => {
                args.push(th.normalize_whnf().clone());
                apply_builtin(b, args)
            }
            Value::OptionalSomeClosure(_) => Value::NEOptionalLit(th),
            Value::ListConsClosure(t, None) => {
                Value::ListConsClosure(t, Some(th))
            }
            Value::ListConsClosure(t, Some(x)) => {
                let v = th.normalize_whnf();
                match &*v {
                    Value::EmptyListLit(_) => Value::NEListLit(vec![x]),
                    Value::NEListLit(xs) => {
                        let mut xs = xs.clone();
                        xs.insert(0, x);
                        Value::NEListLit(xs)
                    }
                    _ => {
                        drop(v);
                        fallback(Value::ListConsClosure(t, Some(x)), th)
                    }
                }
            }
            Value::NaturalSuccClosure => {
                let v = th.normalize_whnf();
                match &*v {
                    Value::NaturalLit(n) => Value::NaturalLit(n + 1),
                    _ => {
                        drop(v);
                        fallback(Value::NaturalSuccClosure, th)
                    }
                }
            }
            Value::UnionConstructor(l, kts) => Value::UnionLit(l, th, kts),
            f => fallback(f, th),
        }
    }

    pub(crate) fn from_builtin(b: Builtin) -> Value {
        Value::AppliedBuiltin(b, vec![])
    }

    fn shift(&self, delta: isize, var: &V<Label>) -> Self {
        match self {
            Value::Lam(x, t, e) => Value::Lam(
                x.clone(),
                t.shift(delta, var),
                e.shift(delta, &var.shift0(1, x)),
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
                e.shift(delta, &var.shift0(1, x)),
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
            Value::PartialExpr(e) => Value::PartialExpr(Box::new(
                e.map_ref_with_special_handling_of_binders(
                    |v| v.shift(delta, var),
                    |x, v| v.shift(delta, &var.shift0(1, x)),
                    X::clone,
                    X::clone,
                    Label::clone,
                ),
            )),
            Value::Expr(e) => Value::Expr(e.shift(delta, var)),
        }
    }

    pub(crate) fn subst_shift(
        &self,
        var: &V<Label>,
        val: &Typed<'static>,
    ) -> Self {
        match self {
            Value::Lam(x, t, e) => Value::Lam(
                x.clone(),
                t.subst_shift(var, val),
                e.subst_shift(&var.shift0(1, x), &val.shift0(1, x)),
            ),
            Value::AppliedBuiltin(b, args) => Value::AppliedBuiltin(
                *b,
                args.iter().map(|v| v.subst_shift(var, val)).collect(),
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
                e.subst_shift(&var.shift0(1, x), &val.shift0(1, x)),
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
            Value::TextLit(elts) => Value::TextLit(
                elts.iter()
                    .map(|contents| {
                        use InterpolatedTextContents::{Expr, Text};
                        match contents {
                            Expr(th) => Expr(th.subst_shift(var, val)),
                            Text(s) => Text(s.clone()),
                        }
                    })
                    .collect(),
            ),
            Value::PartialExpr(e) => Value::PartialExpr(Box::new(
                e.map_ref_with_special_handling_of_binders(
                    |v| v.subst_shift(var, val),
                    |x, v| v.subst_shift(&var.shift0(1, x), &val.shift0(1, x)),
                    X::clone,
                    X::clone,
                    Label::clone,
                ),
            )),
            Value::Expr(e) => Value::Expr(
                e.subst_shift(var, &val.clone().normalize().as_expr()),
            ),
        }
    }
}

mod thunk {
    use super::{
        normalize_whnf, InputSubExpr, NormalizationContext, OutputSubExpr,
        Value,
    };
    use crate::expr::Typed;
    use dhall_core::{Label, V};
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
            self.normalize_whnf();
            match self {
                ThunkInternal::Unnormalized(_, _) => unreachable!(),
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

        fn shift(&self, delta: isize, var: &V<Label>) -> Self {
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

        fn subst_shift(&self, var: &V<Label>, val: &Typed<'static>) -> Self {
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

        pub(crate) fn from_whnf(v: Value) -> Thunk {
            ThunkInternal::Value(WHNF, v).into_thunk()
        }

        pub(crate) fn from_normalized_expr(e: OutputSubExpr) -> Thunk {
            Thunk::new(NormalizationContext::new(), e.embed_absurd())
        }

        // Deprecated
        pub(crate) fn normalize(&self) -> Thunk {
            self.normalize_nf();
            self.clone()
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

        // WARNING: avoid normalizing any thunk while holding on to this ref
        // or you will run into BorrowMut panics
        pub(crate) fn normalize_whnf(&self) -> Ref<Value> {
            self.0.borrow_mut().normalize_whnf();
            Ref::map(self.0.borrow(), ThunkInternal::as_whnf)
        }

        // WARNING: avoid normalizing any thunk while holding on to this ref
        // or you will run into BorrowMut panics
        pub(crate) fn normalize_nf(&self) -> Ref<Value> {
            self.0.borrow_mut().normalize_nf();
            Ref::map(self.0.borrow(), ThunkInternal::as_nf)
        }

        pub(crate) fn normalize_to_expr(&self) -> OutputSubExpr {
            self.normalize_nf().normalize_to_expr()
        }

        pub(crate) fn shift(&self, delta: isize, var: &V<Label>) -> Self {
            self.0.borrow().shift(delta, var).into_thunk()
        }

        pub(crate) fn subst_shift(
            &self,
            var: &V<Label>,
            val: &Typed<'static>,
        ) -> Self {
            self.0.borrow().subst_shift(var, val).into_thunk()
        }
    }
}

pub(crate) use thunk::Thunk;

/// A thunk in type position.
#[derive(Debug, Clone)]
pub(crate) enum TypeThunk {
    Thunk(Thunk),
    Type(Type<'static>),
}

impl TypeThunk {
    fn new(ctx: NormalizationContext, e: InputSubExpr) -> TypeThunk {
        TypeThunk::from_thunk(Thunk::new(ctx, e))
    }

    fn from_whnf(v: Value) -> TypeThunk {
        TypeThunk::from_thunk(Thunk::from_whnf(v))
    }

    fn from_thunk(th: Thunk) -> TypeThunk {
        TypeThunk::Thunk(th)
    }

    pub(crate) fn from_type(t: Type<'static>) -> TypeThunk {
        TypeThunk::Type(t)
    }

    // Deprecated
    fn normalize(&self) -> TypeThunk {
        match self {
            TypeThunk::Thunk(th) => TypeThunk::Thunk(th.normalize()),
            TypeThunk::Type(t) => TypeThunk::Type(t.clone()),
        }
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

    pub(crate) fn normalize_to_expr(&self) -> OutputSubExpr {
        self.normalize_nf().normalize_to_expr()
    }

    fn shift(&self, delta: isize, var: &V<Label>) -> Self {
        match self {
            TypeThunk::Thunk(th) => TypeThunk::Thunk(th.shift(delta, var)),
            TypeThunk::Type(t) => TypeThunk::Type(t.shift(delta, var)),
        }
    }

    pub(crate) fn subst_shift(
        &self,
        var: &V<Label>,
        val: &Typed<'static>,
    ) -> Self {
        match self {
            TypeThunk::Thunk(th) => TypeThunk::Thunk(th.subst_shift(var, val)),
            TypeThunk::Type(t) => TypeThunk::Type(t.subst_shift(var, val)),
        }
    }
}

/// Reduces the imput expression to Value. See doc on `Value` for details.
fn normalize_whnf(ctx: NormalizationContext, expr: InputSubExpr) -> Value {
    match expr.as_ref() {
        ExprF::Var(v) => ctx.lookup(&v),
        ExprF::Annot(x, _) => normalize_whnf(ctx, x.clone()),
        ExprF::Note(_, e) => normalize_whnf(ctx, e.clone()),
        ExprF::Embed(e) => e.to_value(),
        ExprF::Let(x, _, r, b) => {
            let t = Thunk::new(ctx.clone(), r.clone());
            normalize_whnf(ctx.insert(x, t), b.clone())
        }
        ExprF::Lam(x, t, e) => Value::Lam(
            x.clone(),
            Thunk::new(ctx.clone(), t.clone()),
            Thunk::new(ctx.skip(x), e.clone()),
        ),
        ExprF::Builtin(b) => Value::from_builtin(*b),
        ExprF::Const(c) => Value::Const(*c),
        ExprF::BoolLit(b) => Value::BoolLit(*b),
        ExprF::NaturalLit(n) => Value::NaturalLit(*n),
        ExprF::OldOptionalLit(None, e) => {
            Value::EmptyOptionalLit(TypeThunk::new(ctx, e.clone()))
        }
        ExprF::OldOptionalLit(Some(e), _) => {
            Value::NEOptionalLit(Thunk::new(ctx, e.clone()))
        }
        ExprF::SomeLit(e) => Value::NEOptionalLit(Thunk::new(ctx, e.clone())),
        ExprF::EmptyListLit(e) => {
            Value::EmptyListLit(TypeThunk::new(ctx, e.clone()))
        }
        ExprF::NEListLit(elts) => Value::NEListLit(
            elts.iter()
                .map(|e| Thunk::new(ctx.clone(), e.clone()))
                .collect(),
        ),
        ExprF::RecordLit(kvs) => Value::RecordLit(
            kvs.iter()
                .map(|(k, e)| (k.clone(), Thunk::new(ctx.clone(), e.clone())))
                .collect(),
        ),
        ExprF::UnionType(kts) => Value::UnionType(
            kts.iter()
                .map(|(k, t)| {
                    (
                        k.clone(),
                        t.as_ref()
                            .map(|t| TypeThunk::new(ctx.clone(), t.clone())),
                    )
                })
                .collect(),
        ),
        ExprF::UnionLit(l, x, kts) => Value::UnionLit(
            l.clone(),
            Thunk::new(ctx.clone(), x.clone()),
            kts.iter()
                .map(|(k, t)| {
                    (
                        k.clone(),
                        t.as_ref()
                            .map(|t| TypeThunk::new(ctx.clone(), t.clone())),
                    )
                })
                .collect(),
        ),
        ExprF::TextLit(elts) => Value::TextLit(
            elts.iter()
                .map(|contents| {
                    use InterpolatedTextContents::{Expr, Text};
                    match contents {
                        Expr(n) => Expr(Thunk::new(ctx.clone(), n.clone())),
                        Text(s) => Text(s.clone()),
                    }
                })
                .collect(),
        ),
        ExprF::BoolIf(b, e1, e2) => {
            let b = normalize_whnf(ctx.clone(), b.clone());
            match b {
                Value::BoolLit(true) => normalize_whnf(ctx, e1.clone()),
                Value::BoolLit(false) => normalize_whnf(ctx, e2.clone()),
                b => {
                    let e1 = normalize_whnf(ctx.clone(), e1.clone());
                    let e2 = normalize_whnf(ctx, e2.clone());
                    match (e1, e2) {
                        (Value::BoolLit(true), Value::BoolLit(false)) => b,
                        (e1, e2) => {
                            normalize_last_layer(ExprF::BoolIf(b, e1, e2))
                        }
                    }
                }
            }
        }
        expr => {
            // Recursively normalize subexpressions
            let expr: ExprF<Value, Label, X, X> = expr
                .map_ref_with_special_handling_of_binders(
                    |e| normalize_whnf(ctx.clone(), e.clone()),
                    |x, e| normalize_whnf(ctx.skip(x), e.clone()),
                    X::clone,
                    |_| unreachable!(),
                    Label::clone,
                );

            normalize_last_layer(expr)
        }
    }
}

/// When all sub-expressions have been (partially) normalized, eval the remaining toplevel layer.
fn normalize_last_layer(expr: ExprF<Value, Label, X, X>) -> Value {
    use dhall_core::BinOp::*;
    use Value::*;

    match expr {
        ExprF::App(v, a) => v.app(a),

        ExprF::BinOp(BoolAnd, BoolLit(true), y) => y,
        ExprF::BinOp(BoolAnd, x, BoolLit(true)) => x,
        ExprF::BinOp(BoolAnd, BoolLit(false), _) => BoolLit(false),
        ExprF::BinOp(BoolAnd, _, BoolLit(false)) => BoolLit(false),
        ExprF::BinOp(BoolOr, BoolLit(true), _) => BoolLit(true),
        ExprF::BinOp(BoolOr, _, BoolLit(true)) => BoolLit(true),
        ExprF::BinOp(BoolOr, BoolLit(false), y) => y,
        ExprF::BinOp(BoolOr, x, BoolLit(false)) => x,
        ExprF::BinOp(BoolEQ, BoolLit(true), y) => y,
        ExprF::BinOp(BoolEQ, x, BoolLit(true)) => x,
        ExprF::BinOp(BoolNE, BoolLit(false), y) => y,
        ExprF::BinOp(BoolNE, x, BoolLit(false)) => x,
        ExprF::BinOp(BoolEQ, BoolLit(x), BoolLit(y)) => BoolLit(x == y),
        ExprF::BinOp(BoolNE, BoolLit(x), BoolLit(y)) => BoolLit(x != y),

        ExprF::BinOp(NaturalPlus, NaturalLit(0), y) => y,
        ExprF::BinOp(NaturalPlus, x, NaturalLit(0)) => x,
        ExprF::BinOp(NaturalTimes, NaturalLit(0), _) => NaturalLit(0),
        ExprF::BinOp(NaturalTimes, _, NaturalLit(0)) => NaturalLit(0),
        ExprF::BinOp(NaturalTimes, NaturalLit(1), y) => y,
        ExprF::BinOp(NaturalTimes, x, NaturalLit(1)) => x,
        ExprF::BinOp(NaturalPlus, NaturalLit(x), NaturalLit(y)) => {
            NaturalLit(x + y)
        }
        ExprF::BinOp(NaturalTimes, NaturalLit(x), NaturalLit(y)) => {
            NaturalLit(x * y)
        }

        ExprF::BinOp(ListAppend, EmptyListLit(_), y) => y,
        ExprF::BinOp(ListAppend, x, EmptyListLit(_)) => x,
        ExprF::BinOp(ListAppend, NEListLit(mut xs), NEListLit(mut ys)) => {
            xs.append(&mut ys);
            NEListLit(xs)
        }
        ExprF::BinOp(TextAppend, TextLit(mut x), TextLit(mut y)) => {
            x.append(&mut y);
            TextLit(x)
        }
        ExprF::BinOp(TextAppend, TextLit(x), y) if x.is_empty() => y,
        ExprF::BinOp(TextAppend, x, TextLit(y)) if y.is_empty() => x,

        ExprF::Field(UnionType(kts), l) => UnionConstructor(l, kts),
        ExprF::Field(RecordLit(mut kvs), l) => match kvs.remove(&l) {
            Some(r) => r.normalize_whnf().clone(),
            None => {
                // Couldn't do anything useful, so just normalize subexpressions
                Expr(rc(ExprF::Field(RecordLit(kvs).normalize_to_expr(), l)))
            }
        },
        ExprF::Projection(_, ls) if ls.is_empty() => {
            RecordLit(std::collections::BTreeMap::new())
        }
        ExprF::Projection(RecordLit(mut kvs), ls) => RecordLit(
            ls.into_iter()
                .filter_map(|l| kvs.remove(&l).map(|x| (l, x)))
                .collect(),
        ),
        ExprF::Merge(RecordLit(mut handlers), e, t) => {
            let e = match e {
                UnionConstructor(l, kts) => match handlers.remove(&l) {
                    Some(h) => return h.normalize_whnf().clone(),
                    None => UnionConstructor(l, kts),
                },
                UnionLit(l, v, kts) => match handlers.remove(&l) {
                    Some(h) => {
                        let h = h.normalize_whnf().clone();
                        return h.app_thunk(v);
                    }
                    None => UnionLit(l, v, kts),
                },
                e => e,
            };
            // Couldn't do anything useful, so just normalize subexpressions
            Expr(rc(ExprF::Merge(
                RecordLit(handlers).normalize_to_expr(),
                e.normalize_to_expr(),
                t.as_ref().map(Value::normalize_to_expr),
            )))
        }
        expr => PartialExpr(Box::new(expr)),
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
    // norm!(success_prelude_List_iterate_0, "prelude/List/iterate/0");
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
    // norm!(success_prelude_Natural_show_0, "prelude/Natural/show/0");
    // norm!(success_prelude_Natural_show_1, "prelude/Natural/show/1");
    norm!(success_prelude_Natural_sum_0, "prelude/Natural/sum/0");
    norm!(success_prelude_Natural_sum_1, "prelude/Natural/sum/1");
    // norm!(success_prelude_Natural_toDouble_0, "prelude/Natural/toDouble/0");
    // norm!(success_prelude_Natural_toDouble_1, "prelude/Natural/toDouble/1");
    // norm!(success_prelude_Natural_toInteger_0, "prelude/Natural/toInteger/0");
    // norm!(success_prelude_Natural_toInteger_1, "prelude/Natural/toInteger/1");
    norm!(success_prelude_Optional_all_0, "prelude/Optional/all/0");
    norm!(success_prelude_Optional_all_1, "prelude/Optional/all/1");
    norm!(success_prelude_Optional_any_0, "prelude/Optional/any/0");
    norm!(success_prelude_Optional_any_1, "prelude/Optional/any/1");
    // norm!(success_prelude_Optional_build_0, "prelude/Optional/build/0");
    // norm!(success_prelude_Optional_build_1, "prelude/Optional/build/1");
    norm!(success_prelude_Optional_concat_0, "prelude/Optional/concat/0");
    norm!(success_prelude_Optional_concat_1, "prelude/Optional/concat/1");
    norm!(success_prelude_Optional_concat_2, "prelude/Optional/concat/2");
    // norm!(success_prelude_Optional_filter_0, "prelude/Optional/filter/0");
    // norm!(success_prelude_Optional_filter_1, "prelude/Optional/filter/1");
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
    // norm!(success_simple_integerShow, "simple/integerShow");
    // norm!(success_simple_integerToDouble, "simple/integerToDouble");
    // norm!(success_simple_letlet, "simple/letlet");
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
    norm!(success_unit_OperatorTextConcatenateNormalizeArguments, "unit/OperatorTextConcatenateNormalizeArguments");
    norm!(success_unit_OperatorTextConcatenateRhsEmpty, "unit/OperatorTextConcatenateRhsEmpty");
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
}
