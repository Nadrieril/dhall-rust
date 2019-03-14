#![allow(non_snake_case)]
use dhall_core::core::*;
use dhall_generator::dhall_expr;
use std::fmt;

/// Reduce an expression to its weak head normal form, i.e. normalize
/// just enough to get the first constructor of the final expression
/// Is identical to normalize on primitive types, but not on more complex
/// types like functions and records.
/// This allows normalization to be lazy.
pub fn normalize_whnf<S, A>(e: &Expr<S, A>) -> Expr<S, A>
where
    S: Clone + fmt::Debug,
    A: Clone + fmt::Debug,
{
    use dhall_core::BinOp::*;
    use dhall_core::Builtin::*;
    use dhall_core::Expr::*;
    match e {
        Let(f, _, r, b) => {
            let vf0 = &V(f.clone(), 0);
            let r2 = shift::<_, S, _>(1, vf0, r);
            let b2 = subst::<_, S, _>(vf0, &r2, b);
            let b3 = shift::<_, S, _>(-1, vf0, &b2);
            normalize_whnf(&b3)
        }
        Annot(x, _) => normalize_whnf(x),
        Note(_, e) => normalize_whnf(e),
        App(f, a) => match (normalize_whnf(f), a) {
            (Lam(x, _, b), a) => {
                // Beta reduce
                let vx0 = &V(x, 0);
                let a2 = shift::<S, S, A>(1, vx0, a);
                let b2 = subst::<S, S, A>(vx0, &a2, &b);
                let b3 = shift::<S, S, A>(-1, vx0, &b2);
                normalize_whnf(&b3)
            }
            (Builtin(b), a) => match (b, normalize_whnf(a)) {
                (OptionalSome, a) => OptionalLit(None, vec![a]),
                (OptionalNone, a) => OptionalLit(Some(bx(a)), vec![]),
                (NaturalIsZero, NaturalLit(n)) => BoolLit(n == 0),
                (NaturalEven, NaturalLit(n)) => BoolLit(n % 2 == 0),
                (NaturalOdd, NaturalLit(n)) => BoolLit(n % 2 != 0),
                (NaturalToInteger, NaturalLit(n)) => IntegerLit(n as isize),
                (NaturalShow, NaturalLit(n)) => TextLit(n.to_string().into()),

                (b, App(f, x)) => match (b, normalize_whnf(&f), x) {
                    // fold/build fusion for `Natural`
                    (NaturalBuild, Builtin(NaturalFold), x) => {
                        normalize_whnf(&x)
                    }
                    (NaturalFold, Builtin(NaturalBuild), x) => {
                        normalize_whnf(&x)
                    }
                    (b, f, x) => app(Builtin(b), app(f, *x)),
                },
                (b, a) => app(Builtin(b), a),
            },
            (App(f, x), y) => match (normalize_whnf(&f), x, y) {
                // TODO: use whnf
                (Builtin(b), x, y) => match (b, x, normalize::<S, S, A>(&y)) {
                    (ListLength, _, ListLit(_, ys)) => NaturalLit(ys.len()),
                    (ListHead, _, ListLit(t, ys)) => {
                        OptionalLit(t, ys.into_iter().take(1).collect())
                    }
                    (ListLast, _, ListLit(t, ys)) => OptionalLit(
                        t,
                        ys.into_iter().last().into_iter().collect(),
                    ),
                    (ListReverse, _, ListLit(t, ys)) => {
                        let mut xs = ys;
                        xs.reverse();
                        ListLit(t, xs)
                    }

                    // fold/build fusion for `List`
                    (
                        ListBuild,
                        _,
                        App(box App(box Builtin(ListFold), _), box e2),
                    ) => normalize_whnf(&e2),
                    (
                        ListFold,
                        _,
                        App(box App(box Builtin(ListBuild), _), box e2),
                    ) => normalize_whnf(&e2),

                    // fold/build fusion for `Optional`
                    (
                        OptionalBuild,
                        _,
                        App(box App(box Builtin(OptionalFold), _), box e2),
                    ) => normalize_whnf(&e2),
                    (
                        OptionalFold,
                        _,
                        App(box App(box Builtin(OptionalBuild), _), box e2),
                    ) => normalize_whnf(&e2),

                    (ListBuild, a0, k) => {
                        let k = bx(k);
                        let a1 = bx(shift(1, &V("a".into(), 0), &a0));
                        normalize_whnf(
                            &dhall_expr!(k (List a0) (λ(a : a0) -> λ(as : List a1) -> [ a ] # as) ([] : List a0)),
                        )
                    }
                    (OptionalBuild, a0, g) => {
                        let g = bx(g);
                        normalize_whnf(
                            &dhall_expr!((g (Optional a0)) (λ(x: a0) -> [x] :  Optional a0) ([] :  Optional a0)),
                        )
                    }
                    (b, x, y) => app(App(bx(Builtin(b)), x), y),
                },
                (App(f, x), y, z) => match (normalize_whnf(&f), x, y, z) {
                    (App(f, x), y, z, w) => {
                        match (normalize_whnf(&f), x, y, z, w) {
                            (App(f, x), y, z, w, t) => match (
                                normalize_whnf(&f),
                                x,
                                normalize_whnf(&y),
                                z,
                                w,
                                t,
                            ) {
                                (
                                    Builtin(ListFold),
                                    _,
                                    ListLit(_, xs),
                                    _,
                                    cons,
                                    nil,
                                ) => {
                                    let e2: Expr<_, _> = xs
                                        .into_iter()
                                        .rev()
                                        .fold((**nil).clone(), |acc, x| {
                                            let x = bx(x);
                                            let acc = bx(acc);
                                            dhall_expr!(cons x acc)
                                        });
                                    normalize_whnf(&e2)
                                }
                                (
                                    Builtin(OptionalFold),
                                    _,
                                    OptionalLit(_, xs),
                                    _,
                                    just,
                                    nothing,
                                ) => {
                                    let e2: Expr<_, _> = xs.into_iter().fold(
                                        (**nothing).clone(),
                                        |_, y| {
                                            let y = bx(y);
                                            dhall_expr!(just y)
                                        },
                                    );
                                    normalize_whnf(&e2)
                                }
                                (f, x, y, z, w, t) => app(
                                    App(
                                        bx(App(
                                            bx(App(bx(App(bx(f), x)), bx(y))),
                                            z,
                                        )),
                                        w,
                                    ),
                                    (**t).clone(),
                                ),
                            },
                            (f, x, y, z, w) => app(
                                App(bx(App(bx(App(bx(f), x)), y)), z),
                                (**w).clone(),
                            ),
                        }
                    }
                    (f, x, y, z) => {
                        app(App(bx(App(bx(f), x)), y), (**z).clone())
                    }
                },
                (f, x, y) => app(App(bx(f), x), (**y).clone()),
            },
            (f, a) => app(f, (**a).clone()),
        },
        BoolIf(b, t, f) => match normalize_whnf(b) {
            BoolLit(true) => normalize_whnf(t),
            BoolLit(false) => normalize_whnf(f),
            b2 => BoolIf(bx(b2), t.clone(), f.clone()),
        },
        OptionalLit(t, es) => {
            if !es.is_empty() {
                OptionalLit(None, es.clone())
            } else {
                OptionalLit(t.clone(), es.clone())
            }
        }
        BinOp(o, x, y) => match (o, normalize_whnf(&x), normalize_whnf(&y)) {
            (BoolAnd, BoolLit(x), BoolLit(y)) => BoolLit(x && y),
            (BoolOr, BoolLit(x), BoolLit(y)) => BoolLit(x || y),
            (BoolEQ, BoolLit(x), BoolLit(y)) => BoolLit(x == y),
            (BoolNE, BoolLit(x), BoolLit(y)) => BoolLit(x != y),
            (NaturalPlus, NaturalLit(x), NaturalLit(y)) => NaturalLit(x + y),
            (NaturalTimes, NaturalLit(x), NaturalLit(y)) => NaturalLit(x * y),
            (TextAppend, TextLit(x), TextLit(y)) => TextLit(x + y),
            (ListAppend, ListLit(t1, xs), ListLit(t2, ys)) => {
                // Drop type annotation if the result is nonempty
                let t = if xs.is_empty() && ys.is_empty() {
                    t1.or(t2)
                } else {
                    None
                };
                let xs = xs.into_iter();
                let ys = ys.into_iter();
                ListLit(t, xs.chain(ys).collect())
            }
            (o, x, y) => BinOp(*o, bx(x), bx(y)),
        },
        Field(e, x) => match (normalize_whnf(&e), x) {
            (RecordLit(kvs), x) => match kvs.get(&x) {
                Some(r) => normalize_whnf(r),
                None => Field(bx(RecordLit(kvs)), x.clone()),
            },
            (e, x) => Field(bx(e), x.clone()),
        },
        e => e.clone(),
    }
}

/// Reduce an expression to its normal form, performing beta reduction
///
/// `normalize` does not type-check the expression.  You may want to type-check
/// expressions before normalizing them since normalization can convert an
/// ill-typed expression into a well-typed expression.
///
/// However, `normalize` will not fail if the expression is ill-typed and will
/// leave ill-typed sub-expressions unevaluated.
///
pub fn normalize<S, T, A>(e: &Expr<S, A>) -> Expr<T, A>
where
    S: Clone + fmt::Debug,
    T: Clone + fmt::Debug,
    A: Clone + fmt::Debug,
{
    normalize_whnf(e).map_shallow(
        normalize,
        |_| unreachable!(),
        |x| x.clone(),
        |x| x.clone(),
    )
}
