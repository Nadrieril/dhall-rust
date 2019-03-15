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
        App(f, args) => match (normalize_whnf(f), args.as_slice()) {
            (f, []) => f,
            (App(f, args1), args2) => normalize_whnf(&App(
                f.clone(),
                args1.iter().chain(args2.iter()).cloned().collect(),
            )),
            (Lam(ref x, _, ref b), [a, rest..]) => {
                // Beta reduce
                let vx0 = &V(x.clone(), 0);
                let a2 = shift::<S, S, A>(1, vx0, a);
                let b2 = subst::<S, S, A>(vx0, &a2, &b);
                let b3 = shift::<S, S, A>(-1, vx0, &b2);
                normalize_whnf(&App(bx(b3), rest.to_vec()))
            }
            // TODO: this is more normalization than needed
            (Builtin(b), args) => match (
                b,
                args.iter()
                    .map(normalize_whnf)
                    .collect::<Vec<_>>()
                    .as_slice(),
            ) {
                (OptionalSome, [a]) => OptionalLit(None, Some(bx(a.clone()))),
                (OptionalNone, [a]) => OptionalLit(Some(bx(a.clone())), None),
                (NaturalIsZero, [NaturalLit(n)]) => BoolLit(*n == 0),
                (NaturalEven, [NaturalLit(n)]) => BoolLit(*n % 2 == 0),
                (NaturalOdd, [NaturalLit(n)]) => BoolLit(*n % 2 != 0),
                (NaturalToInteger, [NaturalLit(n)]) => IntegerLit(*n as isize),
                (NaturalShow, [NaturalLit(n)]) => TextLit(n.to_string().into()),
                (ListLength, [_, ListLit(_, ys)]) => NaturalLit(ys.len()),
                (ListHead, [_, ListLit(t, ys)]) => {
                    OptionalLit(t.clone(), ys.iter().cloned().map(bx).next())
                }
                (ListLast, [_, ListLit(t, ys)]) => {
                    OptionalLit(t.clone(), ys.iter().cloned().map(bx).last())
                }
                (ListReverse, [_, ListLit(t, ys)]) => {
                    let xs = ys.iter().rev().cloned().collect();
                    ListLit(t.clone(), xs)
                }
                (ListBuild, [a0, g]) => {
                    // fold/build fusion
                    let g = match g {
                        App(f, args) => match (&**f, args.as_slice()) {
                            (Builtin(ListFold), [_, x, rest..]) => {
                                return normalize_whnf(&App(
                                    bx(x.clone()),
                                    rest.to_vec(),
                                ))
                            }
                            (f, args) => app(f.clone(), args.to_vec()),
                        },
                        g => g.clone(),
                    };
                    let g = bx(g);
                    let a0 = bx(a0.clone());
                    let a1 = bx(shift(1, &V("a".into(), 0), &a0));
                    normalize_whnf(
                        &dhall_expr!(g (List a0) (λ(a : a0) -> λ(as : List a1) -> [ a ] # as) ([] : List a0)),
                    )
                }
                (OptionalBuild, [a0, g]) => {
                    // fold/build fusion
                    let g = match g {
                        App(f, args) => match (&**f, args.as_slice()) {
                            (Builtin(OptionalFold), [_, x, rest..]) => {
                                return normalize_whnf(&App(
                                    bx(x.clone()),
                                    rest.to_vec(),
                                ))
                            }
                            (f, args) => app(f.clone(), args.to_vec()),
                        },
                        g => g.clone(),
                    };
                    let g = bx(g);
                    let a0 = bx(a0.clone());
                    normalize_whnf(
                        &dhall_expr!((g (Optional a0)) (λ(x: a0) -> [x] :  Optional a0) ([] :  Optional a0)),
                    )
                }
                (ListFold, [_, ListLit(_, xs), _, cons, nil]) => {
                    let e2: Expr<_, _> =
                        xs.into_iter().rev().fold((*nil).clone(), |acc, x| {
                            let x = bx((x).clone());
                            let acc = bx((acc).clone());
                            let cons = bx((cons).clone());
                            dhall_expr!(cons x acc)
                        });
                    normalize_whnf(&e2)
                }
                // // fold/build fusion
                // (ListFold, [_, App(box Builtin(ListBuild), [_, x, rest..]), rest..]) => {
                //     normalize_whnf(&App(bx(x.clone()), rest.to_vec()))
                // }
                (OptionalFold, [_, OptionalLit(_, Some(x)), _, just, _]) => {
                    let x = bx((**x).clone());
                    let just = bx(just.clone());
                    normalize_whnf(&dhall_expr!(just x))
                }
                (OptionalFold, [_, OptionalLit(_, None), _, _, nothing]) => {
                    (*nothing).clone()
                }
                // // fold/build fusion
                // (OptionalFold, [_, App(box Builtin(OptionalBuild), [_, x, rest..]), rest..]) => {
                //     normalize_whnf(&App(bx(x.clone()), rest.to_vec()))
                // }
                (NaturalBuild, [App(f, args)]) => {
                    match (&**f, args.as_slice()) {
                        // fold/build fusion
                        (Builtin(NaturalFold), [x, rest..]) => {
                            normalize_whnf(&App(bx(x.clone()), rest.to_vec()))
                        }
                        (f, args) => app(
                            Builtin(NaturalBuild),
                            vec![app(f.clone(), args.to_vec())],
                        ),
                    }
                }
                (NaturalFold, [App(f, args)]) => {
                    match (&**f, args.as_slice()) {
                        // fold/build fusion
                        (Builtin(NaturalBuild), [x, rest..]) => {
                            normalize_whnf(&App(bx(x.clone()), rest.to_vec()))
                        }
                        (f, args) => app(
                            Builtin(NaturalFold),
                            vec![app(f.clone(), args.to_vec())],
                        ),
                    }
                }
                (b, args) => App(bx(Builtin(b)), args.to_vec()),
            },
            (f, args) => App(bx(f), args.to_vec()),
        },
        BoolIf(b, t, f) => match normalize_whnf(b) {
            BoolLit(true) => normalize_whnf(t),
            BoolLit(false) => normalize_whnf(f),
            b2 => BoolIf(bx(b2), t.clone(), f.clone()),
        },
        OptionalLit(t, es) => {
            if !es.is_none() {
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
