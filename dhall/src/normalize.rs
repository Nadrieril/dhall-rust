#![allow(non_snake_case)]
use std::collections::BTreeMap;
use std::rc::Rc;

use dhall_core::context::Context;
use dhall_core::{
    rc, shift, shift0, Builtin, Const, ExprF, Integer, InterpolatedText,
    InterpolatedTextContents, Label, Natural, SubExpr, V, X,
};
use dhall_generator as dhall;

use crate::expr::{Normalized, PartiallyNormalized, Type, Typed};

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
        self.partially_normalize().normalize()
    }
    pub(crate) fn partially_normalize(self) -> PartiallyNormalized<'a> {
        PartiallyNormalized(
            normalize_whnf(
                NormalizationContext::from_typecheck_ctx(&self.2),
                self.0,
            ),
            self.1,
            self.3,
        )
    }
    /// Pretends this expression is normalized. Use with care.
    #[allow(dead_code)]
    pub fn skip_normalize(self) -> Normalized<'a> {
        Normalized(
            self.0.unroll().squash_embed(|e| e.0.clone()),
            self.1,
            self.3,
        )
    }
}

impl<'a> PartiallyNormalized<'a> {
    pub(crate) fn normalize(self) -> Normalized<'a> {
        Normalized(self.0.normalize_to_expr(), self.1, self.2)
    }
    pub(crate) fn shift(&self, delta: isize, var: &V<Label>) -> Self {
        let mut e = self.0.clone();
        e.shift(delta, var);
        PartiallyNormalized(
            e,
            self.1.as_ref().map(|x| x.shift(delta, var)),
            self.2,
        )
    }
    pub(crate) fn subst_shift(
        &self,
        var: &V<Label>,
        val: &PartiallyNormalized<'static>,
    ) -> Self {
        PartiallyNormalized(
            self.0.subst_shift(var, val),
            self.1.as_ref().map(|x| x.subst_shift(var, val)),
            self.2,
        )
    }
    pub(crate) fn into_whnf(self) -> Value<WHNF> {
        self.0
    }
}

fn shift_mut<N, E>(delta: isize, var: &V<Label>, in_expr: &mut SubExpr<N, E>) {
    let new_expr = shift(delta, var, &in_expr);
    std::mem::replace(in_expr, new_expr);
}

fn apply_builtin(b: Builtin, args: Vec<Value<WHNF>>) -> Value<WHNF> {
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
                    v = cons.clone().app(x.normalize_whnf()).app(v);
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
                just.app(x.normalize_whnf())
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
    Expr(Value<WHNF>),
    Skip(V<Label>),
}

impl EnvItem {
    fn shift0(&self, delta: isize, x: &Label) -> Self {
        use EnvItem::*;
        match self {
            Expr(e) => {
                let mut e = e.clone();
                e.shift(delta, &V(x.clone(), 0));
                Expr(e)
            }
            Skip(var) => Skip(var.shift0(delta, x)),
        }
    }
    pub(crate) fn subst_shift(
        &self,
        var: &V<Label>,
        val: &PartiallyNormalized<'static>,
    ) -> Self {
        use EnvItem::*;
        match self {
            Expr(e) => Expr(e.subst_shift(var, val)),
            Skip(v) if v == var => Expr(val.clone().into_whnf()),
            Skip(v) => Skip(v.shift(-1, var)),
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct NormalizationContext(Rc<Context<Label, EnvItem>>);

impl NormalizationContext {
    fn new() -> Self {
        NormalizationContext(Rc::new(Context::new()))
    }
    fn insert(&self, x: &Label, e: Value<WHNF>) -> Self {
        NormalizationContext(Rc::new(
            self.0.insert(x.clone(), EnvItem::Expr(e)),
        ))
    }
    fn skip(&self, x: &Label) -> Self {
        NormalizationContext(Rc::new(
            self.0
                .map(|_, e| e.shift0(1, x))
                .insert(x.clone(), EnvItem::Skip(V(x.clone(), 0))),
        ))
    }
    fn lookup(&self, var: &V<Label>) -> Value<WHNF> {
        let V(x, n) = var;
        match self.0.lookup(x, *n) {
            Some(EnvItem::Expr(e)) => e.clone(),
            Some(EnvItem::Skip(newvar)) => Value::Var(newvar.clone()),
            None => Value::Var(var.clone()),
        }
    }
    fn from_typecheck_ctx(tc_ctx: &crate::typecheck::TypecheckContext) -> Self {
        use crate::typecheck::EnvItem::*;
        let mut ctx = Context::new();
        for (k, vs) in tc_ctx.0.iter_keys() {
            for v in vs.iter() {
                let new_item = match v {
                    Type(var, _) => EnvItem::Skip(var.clone()),
                    Value(e) => EnvItem::Expr(normalize_whnf(
                        NormalizationContext::new(),
                        e.as_expr().embed_absurd(),
                    )),
                };
                ctx = ctx.insert(k.clone(), new_item);
            }
        }
        NormalizationContext(Rc::new(ctx))
    }

    fn subst_shift(
        &self,
        var: &V<Label>,
        val: &PartiallyNormalized<'static>,
    ) -> Self {
        NormalizationContext(Rc::new(
            self.0.map(|_, e| e.subst_shift(var, val)),
        ))
    }
}

pub(crate) type WHNF = ();
pub(crate) type NF = X;

/// A semantic value. `Form` should be either `WHNF` or `NF`.
/// `NF` stands for Normal Form and indicates that all subexpressions are normalized.
/// `WHNF` stands for Weak Head Normal-Form and indicates that subexpressions may not be normalized.
///
/// Weak Head Normal-Form means that the expression is normalized as
/// little as possible, but just enough to know the first constructor of the normal form. This is
/// identical to normal form for simple types like integers, but for e.g. a record literal
/// this means knowing just the field names.
#[derive(Debug, Clone)]
pub(crate) enum Value<Form> {
    /// Closures
    Lam(Label, Thunk<Form>, Thunk<Form>),
    AppliedBuiltin(Builtin, Vec<Value<Form>>),
    /// `λ(x: a) -> Some x`
    OptionalSomeClosure(TypeThunk<Form>),
    /// `λ(x : a) -> λ(xs : List a) -> [ x ] # xs`
    /// `λ(xs : List a) -> [ x ] # xs`
    ListConsClosure(TypeThunk<Form>, Option<Thunk<Form>>),
    /// `λ(x : Natural) -> x + 1`
    NaturalSuccClosure,
    Pi(Label, TypeThunk<Form>, TypeThunk<Form>),

    Var(V<Label>),
    Const(Const),
    BoolLit(bool),
    NaturalLit(Natural),
    IntegerLit(Integer),
    EmptyOptionalLit(TypeThunk<Form>),
    NEOptionalLit(Thunk<Form>),
    EmptyListLit(TypeThunk<Form>),
    NEListLit(Vec<Thunk<Form>>),
    RecordLit(BTreeMap<Label, Thunk<Form>>),
    RecordType(BTreeMap<Label, TypeThunk<Form>>),
    UnionType(BTreeMap<Label, Option<TypeThunk<Form>>>),
    UnionConstructor(Label, BTreeMap<Label, Option<TypeThunk<Form>>>),
    UnionLit(Label, Thunk<Form>, BTreeMap<Label, Option<TypeThunk<Form>>>),
    TextLit(Vec<InterpolatedTextContents<Thunk<Form>>>),
    /// This must not contain a value captured by one of the variants above.
    Expr(OutputSubExpr),
}

impl Value<NF> {
    /// Convert the value back to a (normalized) syntactic expression
    pub(crate) fn normalize_to_expr(self) -> OutputSubExpr {
        match self {
            Value::Lam(x, t, e) => rc(ExprF::Lam(
                x.clone(),
                t.to_nf().normalize_to_expr(),
                e.to_nf().normalize_to_expr(),
            )),
            Value::AppliedBuiltin(b, args) => {
                let mut e = rc(ExprF::Builtin(b));
                for v in args {
                    e = rc(ExprF::App(e, v.normalize_to_expr()));
                }
                e
            }
            Value::OptionalSomeClosure(n) => {
                let a = n.to_nf().normalize_to_expr();
                dhall::subexpr!(λ(x: a) -> Some x)
            }
            Value::ListConsClosure(n, None) => {
                let a = n.to_nf().normalize_to_expr();
                // Avoid accidental capture of the new `x` variable
                let a1 = shift0(1, &"x".into(), &a);
                dhall::subexpr!(λ(x : a) -> λ(xs : List a1) -> [ x ] # xs)
            }
            Value::ListConsClosure(n, Some(v)) => {
                let v = v.to_nf().normalize_to_expr();
                let a = n.to_nf().normalize_to_expr();
                // Avoid accidental capture of the new `xs` variable
                let v = shift0(1, &"xs".into(), &v);
                dhall::subexpr!(λ(xs : List a) -> [ v ] # xs)
            }
            Value::NaturalSuccClosure => {
                dhall::subexpr!(λ(x : Natural) -> x + 1)
            }
            Value::Pi(x, t, e) => rc(ExprF::Pi(
                x,
                t.to_nf().normalize_to_expr(),
                e.to_nf().normalize_to_expr(),
            )),
            Value::Var(v) => rc(ExprF::Var(v)),
            Value::Const(c) => rc(ExprF::Const(c)),
            Value::BoolLit(b) => rc(ExprF::BoolLit(b)),
            Value::NaturalLit(n) => rc(ExprF::NaturalLit(n)),
            Value::IntegerLit(n) => rc(ExprF::IntegerLit(n)),
            Value::EmptyOptionalLit(n) => rc(ExprF::App(
                rc(ExprF::Builtin(Builtin::OptionalNone)),
                n.to_nf().normalize_to_expr(),
            )),
            Value::NEOptionalLit(n) => {
                rc(ExprF::SomeLit(n.to_nf().normalize_to_expr()))
            }
            Value::EmptyListLit(n) => {
                rc(ExprF::EmptyListLit(n.to_nf().normalize_to_expr()))
            }
            Value::NEListLit(elts) => rc(ExprF::NEListLit(
                elts.into_iter()
                    .map(|n| n.to_nf().normalize_to_expr())
                    .collect(),
            )),
            Value::RecordLit(kvs) => rc(ExprF::RecordLit(
                kvs.into_iter()
                    .map(|(k, v)| (k, v.to_nf().normalize_to_expr()))
                    .collect(),
            )),
            Value::RecordType(kts) => rc(ExprF::RecordType(
                kts.into_iter()
                    .map(|(k, v)| (k, v.to_nf().normalize_to_expr()))
                    .collect(),
            )),
            Value::UnionType(kts) => rc(ExprF::UnionType(
                kts.into_iter()
                    .map(|(k, v)| (k, v.map(|v| v.to_nf().normalize_to_expr())))
                    .collect(),
            )),
            Value::UnionConstructor(l, kts) => {
                let kts = kts
                    .into_iter()
                    .map(|(k, v)| (k, v.map(|v| v.to_nf().normalize_to_expr())))
                    .collect();
                rc(ExprF::Field(rc(ExprF::UnionType(kts)), l))
            }
            Value::UnionLit(l, v, kts) => rc(ExprF::UnionLit(
                l,
                v.to_nf().normalize_to_expr(),
                kts.into_iter()
                    .map(|(k, v)| (k, v.map(|v| v.to_nf().normalize_to_expr())))
                    .collect(),
            )),
            Value::TextLit(elts) => {
                fn normalize_textlit(
                    elts: Vec<InterpolatedTextContents<Thunk<NF>>>,
                ) -> InterpolatedText<OutputSubExpr> {
                    elts.into_iter()
                        .flat_map(|contents| {
                            use InterpolatedTextContents::{Expr, Text};
                            let new_interpolated = match contents {
                                Expr(n) => match n.to_nf() {
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
                                Text(s) => InterpolatedText::from(s),
                            };
                            new_interpolated.into_iter()
                        })
                        .collect()
                }

                rc(ExprF::TextLit(normalize_textlit(elts)))
            }
            Value::Expr(e) => e,
        }
    }
}

impl Value<WHNF> {
    pub(crate) fn normalize_to_expr(self) -> OutputSubExpr {
        self.normalize().normalize_to_expr()
    }

    pub(crate) fn normalize(&self) -> Value<NF> {
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
            Value::Expr(e) => Value::Expr(e.clone()),
        }
    }

    /// Apply to a value
    pub(crate) fn app(self, val: Value<WHNF>) -> Value<WHNF> {
        match (self, val) {
            (Value::Lam(x, _, e), val) => {
                let val =
                    PartiallyNormalized(val, None, std::marker::PhantomData);
                e.subst_shift(&V(x, 0), &val).normalize_whnf()
            }
            (Value::AppliedBuiltin(b, mut args), val) => {
                args.push(val);
                apply_builtin(b, args)
            }
            (Value::OptionalSomeClosure(_), val) => {
                Value::NEOptionalLit(Thunk::from_whnf(val))
            }
            (Value::ListConsClosure(t, None), val) => {
                Value::ListConsClosure(t, Some(Thunk::from_whnf(val)))
            }
            (Value::ListConsClosure(_, Some(x)), Value::EmptyListLit(_)) => {
                Value::NEListLit(vec![x])
            }
            (Value::ListConsClosure(_, Some(x)), Value::NEListLit(mut xs)) => {
                xs.insert(0, x);
                Value::NEListLit(xs)
            }
            (Value::NaturalSuccClosure, Value::NaturalLit(n)) => {
                Value::NaturalLit(n + 1)
            }
            (Value::UnionConstructor(l, kts), val) => {
                Value::UnionLit(l, Thunk::from_whnf(val), kts)
            }
            // Can't do anything useful, convert to expr
            (f, a) => Value::Expr(rc(ExprF::App(
                f.normalize_to_expr(),
                a.normalize_to_expr(),
            ))),
        }
    }

    pub(crate) fn from_builtin(b: Builtin) -> Value<WHNF> {
        Value::AppliedBuiltin(b, vec![])
    }

    fn shift(&mut self, delta: isize, var: &V<Label>) {
        match self {
            Value::Var(v) => {
                std::mem::replace(v, v.shift(delta, var));
            }
            Value::NaturalSuccClosure
            | Value::Const(_)
            | Value::BoolLit(_)
            | Value::NaturalLit(_)
            | Value::IntegerLit(_) => {}
            Value::EmptyOptionalLit(tth)
            | Value::OptionalSomeClosure(tth)
            | Value::EmptyListLit(tth) => {
                tth.shift(delta, var);
            }
            Value::NEOptionalLit(th) => {
                th.shift(delta, var);
            }
            Value::Lam(x, t, e) => {
                t.shift(delta, var);
                e.shift(delta, &var.shift0(1, x));
            }
            Value::AppliedBuiltin(_, args) => {
                for x in args.iter_mut() {
                    x.shift(delta, var);
                }
            }
            Value::ListConsClosure(t, v) => {
                t.shift(delta, var);
                for x in v.iter_mut() {
                    x.shift(delta, var);
                }
            }
            Value::Pi(x, t, e) => {
                t.shift(delta, var);
                e.shift(delta, &var.shift0(1, x));
            }
            Value::NEListLit(elts) => {
                for x in elts.iter_mut() {
                    x.shift(delta, var);
                }
            }
            Value::RecordLit(kvs) => {
                for x in kvs.values_mut() {
                    x.shift(delta, var);
                }
            }
            Value::RecordType(kvs) => {
                for x in kvs.values_mut() {
                    x.shift(delta, var);
                }
            }
            Value::UnionType(kts) | Value::UnionConstructor(_, kts) => {
                for x in kts.values_mut().flat_map(|opt| opt) {
                    x.shift(delta, var);
                }
            }
            Value::UnionLit(_, v, kts) => {
                v.shift(delta, var);
                for x in kts.values_mut().flat_map(|opt| opt) {
                    x.shift(delta, var);
                }
            }
            Value::TextLit(elts) => {
                for x in elts.iter_mut() {
                    use InterpolatedTextContents::{Expr, Text};
                    match x {
                        Expr(n) => n.shift(delta, var),
                        Text(_) => {}
                    }
                }
            }
            Value::Expr(e) => shift_mut(delta, var, e),
        }
    }

    pub(crate) fn subst_shift(
        &self,
        var: &V<Label>,
        val: &PartiallyNormalized<'static>,
    ) -> Self {
        match self {
            Value::Lam(x, t, e) => Value::Lam(
                x.clone(),
                t.subst_shift(var, val),
                e.subst_shift(&var.shift0(1, x), val),
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
                e.subst_shift(&var.shift0(1, x), val),
            ),
            Value::Var(v) if v == var => val.clone().into_whnf(),
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
            Value::Expr(e) => Value::Expr(
                e.subst_shift(var, &val.clone().normalize().as_expr()),
            ),
        }
    }
}

/// Contains either a (partially) normalized value or a
/// non-normalized value alongside a normalization context.
#[derive(Debug, Clone)]
pub(crate) enum Thunk<Form> {
    Value(Box<Value<Form>>),
    Unnormalized(Form, NormalizationContext, InputSubExpr),
}

impl Thunk<WHNF> {
    fn new(ctx: NormalizationContext, e: InputSubExpr) -> Thunk<WHNF> {
        Thunk::Unnormalized((), ctx, e)
    }

    fn from_whnf(v: Value<WHNF>) -> Thunk<WHNF> {
        Thunk::Value(Box::new(v))
    }

    pub(crate) fn normalize_whnf(&self) -> Value<WHNF> {
        match self {
            Thunk::Value(v) => (**v).clone(),
            Thunk::Unnormalized(_, ctx, e) => {
                normalize_whnf(ctx.clone(), e.clone())
            }
        }
    }

    fn normalize(&self) -> Thunk<NF> {
        Thunk::Value(Box::new(self.normalize_whnf().normalize()))
    }

    fn shift(&mut self, delta: isize, var: &V<Label>) {
        match self {
            Thunk::Value(v) => v.shift(delta, var),
            Thunk::Unnormalized(_, _, e) => shift_mut(delta, var, e),
        }
    }

    pub(crate) fn subst_shift(
        &self,
        var: &V<Label>,
        val: &PartiallyNormalized<'static>,
    ) -> Self {
        match self {
            Thunk::Value(v) => Thunk::Value(Box::new(v.subst_shift(var, val))),
            Thunk::Unnormalized(marker, ctx, e) => Thunk::Unnormalized(
                marker.clone(),
                ctx.subst_shift(var, val),
                e.clone(),
            ),
        }
    }
}

impl Thunk<NF> {
    pub(crate) fn to_nf(&self) -> Value<NF> {
        match self {
            Thunk::Value(v) => (**v).clone(),
            Thunk::Unnormalized(m, _, _) => match *m {},
        }
    }
}

/// A thunk in type position.
#[derive(Debug, Clone)]
pub(crate) enum TypeThunk<Form> {
    Thunk(Thunk<Form>),
    Type(Type<'static>),
}

impl TypeThunk<WHNF> {
    fn new(ctx: NormalizationContext, e: InputSubExpr) -> TypeThunk<WHNF> {
        TypeThunk::from_thunk(Thunk::new(ctx, e))
    }

    fn from_whnf(v: Value<WHNF>) -> TypeThunk<WHNF> {
        TypeThunk::from_thunk(Thunk::from_whnf(v))
    }

    fn from_thunk(th: Thunk<WHNF>) -> TypeThunk<WHNF> {
        TypeThunk::Thunk(th)
    }

    pub(crate) fn from_type(t: Type<'static>) -> TypeThunk<WHNF> {
        TypeThunk::Type(t)
    }

    fn normalize(&self) -> TypeThunk<NF> {
        match self {
            TypeThunk::Thunk(th) => TypeThunk::Thunk(th.normalize()),
            TypeThunk::Type(t) => TypeThunk::Type(t.clone()),
        }
    }

    fn shift(&mut self, delta: isize, var: &V<Label>) {
        match self {
            TypeThunk::Thunk(th) => th.shift(delta, var),
            TypeThunk::Type(t) => {
                let shifted = t.shift(delta, var);
                std::mem::replace(t, shifted);
            }
        }
    }

    pub(crate) fn subst_shift(
        &self,
        var: &V<Label>,
        val: &PartiallyNormalized<'static>,
    ) -> Self {
        match self {
            TypeThunk::Thunk(th) => TypeThunk::Thunk(th.subst_shift(var, val)),
            TypeThunk::Type(t) => TypeThunk::Type(t.subst_shift(var, val)),
        }
    }
}

impl TypeThunk<NF> {
    pub(crate) fn to_nf(&self) -> Value<NF> {
        match self {
            TypeThunk::Thunk(th) => th.to_nf(),
            // TODO: let's hope for the best with the unwrap
            TypeThunk::Type(t) => t
                .clone()
                .partially_normalize()
                .unwrap()
                .into_whnf()
                .normalize(),
        }
    }
}

/// Reduces the imput expression to Value. See doc on `Value` for details.
fn normalize_whnf(
    ctx: NormalizationContext,
    expr: InputSubExpr,
) -> Value<WHNF> {
    match expr.as_ref() {
        ExprF::Var(v) => ctx.lookup(&v),
        ExprF::Annot(x, _) => normalize_whnf(ctx, x.clone()),
        ExprF::Note(_, e) => normalize_whnf(ctx, e.clone()),
        // TODO: wasteful to retraverse everything
        ExprF::Embed(e) => {
            normalize_whnf(NormalizationContext::new(), e.0.embed_absurd())
        }
        ExprF::Let(x, _, r, b) => {
            let r = normalize_whnf(ctx.clone(), r.clone());
            normalize_whnf(ctx.insert(x, r), b.clone())
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
            let expr: ExprF<Value<WHNF>, Label, X, X> = expr
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
fn normalize_last_layer(expr: ExprF<Value<WHNF>, Label, X, X>) -> Value<WHNF> {
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
            Some(r) => r.normalize_whnf(),
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
                    Some(h) => return h.normalize_whnf(),
                    None => UnionConstructor(l, kts),
                },
                UnionLit(l, v, kts) => match handlers.remove(&l) {
                    Some(h) => {
                        let h = h.normalize_whnf();
                        let v = v.normalize_whnf();
                        return h.app(v);
                    }
                    None => UnionLit(l, v, kts),
                },
                e => e,
            };
            // Couldn't do anything useful, so just normalize subexpressions
            Expr(rc(ExprF::Merge(
                RecordLit(handlers).normalize_to_expr(),
                e.normalize_to_expr(),
                t.map(<Value<WHNF>>::normalize_to_expr),
            )))
        }
        // Couldn't do anything useful, so just normalize subexpressions
        expr => {
            Expr(rc(expr.map_ref_simple(|e| e.clone().normalize_to_expr())))
        }
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
