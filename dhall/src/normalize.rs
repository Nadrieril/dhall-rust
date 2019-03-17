#![allow(non_snake_case)]
use dhall_core::core::*;
use dhall_generator::dhall_expr;
use std::fmt;
use std::rc::Rc;

/// Reduce an expression to its weak head normal form, i.e. normalize
/// just enough to get the first constructor of the final expression
/// Is identical to normalize on primitive types, but not on more complex
/// types like functions and records.
/// This allows normalization to be lazy.
pub fn normalize_whnf<S, A>(e: &SubExpr<S, A>) -> SubExpr<S, A>
where
    S: fmt::Debug,
    A: fmt::Debug,
{
    use dhall_core::BinOp::*;
    use dhall_core::Builtin::*;
    use dhall_core::Expr::*;
    rc(match e.as_ref() {
        Let(f, _, r, b) => {
            let vf0 = &V(f.clone(), 0);
            let r2 = shift(1, vf0, r);
            let b2 = subst(vf0, &r2, b);
            let b3 = shift(-1, vf0, &b2);
            return normalize_whnf(&b3);
        }
        Annot(x, _) => return normalize_whnf(x),
        Note(_, e) => return normalize_whnf(e),
        App(f, args) => {
            let f = normalize_whnf(f);
            match (f.as_ref(), args.as_slice()) {
                (_, []) => return f,
                (App(f, args1), args2) => {
                    return normalize_whnf(&rc(App(
                        f.clone(),
                        args1.iter().chain(args2.iter()).cloned().collect(),
                    )))
                }
                (Lam(ref x, _, ref b), [a, rest..]) => {
                    // Beta reduce
                    let vx0 = &V(x.clone(), 0);
                    let a2 = shift(1, vx0, a);
                    let b2 = subst(vx0, &a2, &b);
                    let b3 = shift(-1, vx0, &b2);
                    return normalize_whnf(&rc(App(b3, rest.to_vec())));
                }
                // TODO: this is more normalization than needed
                (Builtin(b), args) => {
                    let args = args
                        .iter()
                        .map(|x| normalize_whnf(x))
                        .collect::<Vec<Rc<Expr<_, _>>>>();

                    match (
                        b,
                        args.iter()
                            .map(Rc::as_ref)
                            .collect::<Vec<_>>()
                            .as_slice(),
                    ) {
                        (OptionalSome, [_]) => {
                            OptionalLit(None, Some(Rc::clone(&args[0])))
                        }
                        (OptionalNone, [_]) => {
                            OptionalLit(Some(Rc::clone(&args[0])), None)
                        }
                        (NaturalIsZero, [NaturalLit(n)]) => BoolLit(*n == 0),
                        (NaturalEven, [NaturalLit(n)]) => BoolLit(*n % 2 == 0),
                        (NaturalOdd, [NaturalLit(n)]) => BoolLit(*n % 2 != 0),
                        (NaturalToInteger, [NaturalLit(n)]) => {
                            IntegerLit(*n as isize)
                        }
                        (NaturalShow, [NaturalLit(n)]) => {
                            TextLit(n.to_string().into())
                        }
                        (ListLength, [_, ListLit(_, ys)]) => {
                            NaturalLit(ys.len())
                        }
                        (ListHead, [_, ListLit(t, ys)]) => {
                            OptionalLit(t.clone(), ys.iter().cloned().next())
                        }
                        (ListLast, [_, ListLit(t, ys)]) => {
                            OptionalLit(t.clone(), ys.iter().cloned().last())
                        }
                        (ListReverse, [_, ListLit(t, ys)]) => {
                            let xs = ys.iter().rev().cloned().collect();
                            ListLit(t.clone(), xs)
                        }
                        (ListBuild, [_, _]) => {
                            // fold/build fusion
                            let g = Rc::clone(&args[1]);
                            let g = match g.as_ref() {
                                App(f, args) => {
                                    match (f.as_ref(), args.as_slice()) {
                                        (Builtin(ListFold), [_, x, rest..]) => {
                                            return normalize_whnf(&rc(App(
                                                x.clone(),
                                                rest.to_vec(),
                                            )))
                                        }
                                        (_, args) => {
                                            rc(App(f.clone(), args.to_vec()))
                                        }
                                    }
                                }
                                _ => g,
                            };
                            let a0 = Rc::clone(&args[0]);
                            let a1 = shift(1, &V("a".into(), 0), &a0);
                            return normalize_whnf(
                                &dhall_expr!(g (List a0) (λ(a : a0) -> λ(as : List a1) -> [ a ] # as) ([] : List a0)),
                            );
                        }
                        (OptionalBuild, [_, _]) => {
                            // fold/build fusion
                            let g = Rc::clone(&args[1]);
                            let g = match g.as_ref() {
                                App(f, args) => {
                                    match (f.as_ref(), args.as_slice()) {
                                        (
                                            Builtin(OptionalFold),
                                            [_, x, rest..],
                                        ) => {
                                            return normalize_whnf(&rc(App(
                                                x.clone(),
                                                rest.to_vec(),
                                            )))
                                        }
                                        (_, args) => {
                                            rc(App(f.clone(), args.to_vec()))
                                        }
                                    }
                                }
                                _ => g,
                            };
                            let a0 = Rc::clone(&args[0]);
                            return normalize_whnf(
                                &dhall_expr!((g (Optional a0)) (λ(x: a0) -> [x] :  Optional a0) ([] :  Optional a0)),
                            );
                        }
                        (ListFold, [_, ListLit(_, xs), _, _, _]) => {
                            let e2: Rc<Expr<_, _>> = xs.iter().rev().fold(
                                Rc::clone(&args[4]),
                                |acc, x| {
                                    let x = x.clone();
                                    let acc = acc.clone();
                                    let cons = Rc::clone(&args[3]);
                                    dhall_expr!(cons x acc)
                                },
                            );
                            return normalize_whnf(&e2);
                        }
                        // // fold/build fusion
                        // (ListFold, [_, App(box Builtin(ListBuild), [_, x, rest..]), rest..]) => {
                        //     normalize_whnf(&App(bx(x.clone()), rest.to_vec()))
                        // }
                        (
                            OptionalFold,
                            [_, OptionalLit(_, Some(x)), _, _, _],
                        ) => {
                            let x = x.clone();
                            let just = Rc::clone(&args[3]);
                            return normalize_whnf(&dhall_expr!(just x));
                        }
                        (
                            OptionalFold,
                            [_, OptionalLit(_, None), _, _, _],
                        ) => return Rc::clone(&args[4]),
                        // // fold/build fusion
                        // (OptionalFold, [_, App(box Builtin(OptionalBuild), [_, x, rest..]), rest..]) => {
                        //     normalize_whnf(&App(bx(x.clone()), rest.to_vec()))
                        // }
                        (NaturalBuild, [App(f, args)]) => {
                            match (f.as_ref(), args.as_slice()) {
                                // fold/build fusion
                                (Builtin(NaturalFold), [x, rest..]) => {
                                    return normalize_whnf(&rc(App(
                                        x.clone(),
                                        rest.to_vec(),
                                    )))
                                }
                                (_, args) => app(
                                    Builtin(NaturalBuild),
                                    vec![bx(App(f.clone(), args.to_vec()))],
                                ),
                            }
                        }
                        (NaturalFold, [App(f, args)]) => {
                            match (f.as_ref(), args.as_slice()) {
                                // fold/build fusion
                                (Builtin(NaturalBuild), [x, rest..]) => {
                                    return normalize_whnf(&rc(App(
                                        x.clone(),
                                        rest.to_vec(),
                                    )))
                                }
                                (_, args) => app(
                                    Builtin(NaturalFold),
                                    vec![bx(App(f.clone(), args.to_vec()))],
                                ),
                            }
                        }
                        (b, _) => App(rc(Builtin(*b)), args),
                    }
                }
                (_, args) => App(f, args.to_vec()),
            }
        }
        BoolIf(b, t, f) => {
            let b = normalize_whnf(b);
            match b.as_ref() {
                BoolLit(true) => return normalize_whnf(t),
                BoolLit(false) => return normalize_whnf(f),
                _ => BoolIf(b, t.clone(), f.clone()),
            }
        }
        OptionalLit(t, es) => {
            if !es.is_none() {
                OptionalLit(None, es.clone())
            } else {
                OptionalLit(t.clone(), es.clone())
            }
        }
        BinOp(o, x, y) => {
            let x = normalize_whnf(x);
            let y = normalize_whnf(y);
            match (o, x.as_ref(), y.as_ref()) {
                (BoolAnd, BoolLit(x), BoolLit(y)) => BoolLit(*x && *y),
                (BoolOr, BoolLit(x), BoolLit(y)) => BoolLit(*x || *y),
                (BoolEQ, BoolLit(x), BoolLit(y)) => BoolLit(x == y),
                (BoolNE, BoolLit(x), BoolLit(y)) => BoolLit(x != y),
                (NaturalPlus, NaturalLit(x), NaturalLit(y)) => {
                    NaturalLit(x + y)
                }
                (NaturalTimes, NaturalLit(x), NaturalLit(y)) => {
                    NaturalLit(x * y)
                }
                // TODO: interpolation
                (TextAppend, TextLit(x), TextLit(y)) => {
                    TextLit(x + y)
                }
                (ListAppend, ListLit(t1, xs), ListLit(t2, ys)) => {
                    let t1: Option<Rc<_>> = t1.as_ref().map(Rc::clone);
                    let t2: Option<Rc<_>> = t2.as_ref().map(Rc::clone);
                    // Drop type annotation if the result is nonempty
                    let t = if xs.is_empty() && ys.is_empty() {
                        t1.or(t2)
                    } else {
                        None
                    };
                    let xs = xs.into_iter().cloned();
                    let ys = ys.into_iter().cloned();
                    ListLit(t, xs.chain(ys).collect())
                }
                (o, _, _) => BinOp(*o, x, y),
            }
        }
        Field(e, x) => {
            let e = normalize_whnf(e);
            match (e.as_ref(), x) {
                (RecordLit(kvs), x) => match kvs.get(&x) {
                    Some(r) => return normalize_whnf(r),
                    None => Field(e, x.clone()),
                },
                (_, x) => Field(e, x.clone()),
            }
        }
        _ => return Rc::clone(e),
    })
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
pub fn normalize<S, T, A>(e: SubExpr<S, A>) -> SubExpr<T, A>
where
    S: Clone + fmt::Debug,
    T: Clone + fmt::Debug,
    A: Clone + fmt::Debug,
{
    rc(normalize_whnf(&e).map_shallow_rc(
        |x| normalize(Rc::clone(x)),
        |_| unreachable!(),
        |x| x.clone(),
        |x| x.clone(),
    ))
}
