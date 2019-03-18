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
    match e.as_ref() {
        Let(f, _, r, b) => {
            let vf0 = &V(f.clone(), 0);
            let r2 = shift(1, vf0, r);
            let b2 = subst(vf0, &r2, b);
            let b3 = shift(-1, vf0, &b2);
            normalize_whnf(&b3)
        }
        Annot(x, _) => normalize_whnf(x),
        Note(_, e) => normalize_whnf(e),
        App(f, args) => {
            let f = normalize_whnf(f);
            match (f.as_ref(), args.as_slice()) {
                (_, []) => f,
                (App(f, args1), args2) => normalize_whnf(&rc(App(
                    f.clone(),
                    args1.iter().chain(args2.iter()).cloned().collect(),
                ))),
                (Lam(ref x, _, ref b), [a, rest..]) => {
                    // Beta reduce
                    let vx0 = &V(x.clone(), 0);
                    let a2 = shift(1, vx0, a);
                    let b2 = subst(vx0, &a2, &b);
                    let b3 = shift(-1, vx0, &b2);
                    normalize_whnf(&rc(App(b3, rest.to_vec())))
                }
                (Builtin(b), _) => {
                    // How many arguments for each builtin, and which argument
                    // is the important one for pattern-matching
                    let (len_consumption, arg_to_eval) = match b {
                        OptionalSome => (1, None),
                        OptionalNone => (1, None),
                        NaturalIsZero => (1, Some(0)),
                        NaturalEven => (1, Some(0)),
                        NaturalOdd => (1, Some(0)),
                        NaturalToInteger => (1, Some(0)),
                        NaturalShow => (1, Some(0)),
                        ListLength => (2, Some(1)),
                        ListHead => (2, Some(1)),
                        ListLast => (2, Some(1)),
                        ListReverse => (2, Some(1)),
                        ListBuild => (2, Some(1)),
                        OptionalBuild => (2, Some(1)),
                        ListFold => (5, Some(1)),
                        OptionalFold => (5, Some(1)),
                        NaturalBuild => (1, Some(0)),
                        NaturalFold => (1, Some(0)),
                        _ => (0, None),
                    };
                    let mut args = args.to_vec();
                    if len_consumption > args.len() {
                        return rc(App(f, args));
                    }
                    if let Some(i) = arg_to_eval {
                        args[i] = Rc::clone(&normalize_whnf(&args[i]));
                    }
                    let evaled_arg = arg_to_eval.map(|i| args[i].as_ref());

                    let ret = match (b, evaled_arg, args.as_slice()) {
                        (OptionalSome, _, [x, ..]) => {
                            rc(OptionalLit(None, Some(Rc::clone(x))))
                        }
                        (OptionalNone, _, [t, ..]) => {
                            rc(OptionalLit(Some(Rc::clone(t)), None))
                        }
                        (NaturalIsZero, Some(NaturalLit(n)), _) => {
                            rc(BoolLit(*n == 0))
                        }
                        (NaturalEven, Some(NaturalLit(n)), _) => {
                            rc(BoolLit(*n % 2 == 0))
                        }
                        (NaturalOdd, Some(NaturalLit(n)), _) => {
                            rc(BoolLit(*n % 2 != 0))
                        }
                        (NaturalToInteger, Some(NaturalLit(n)), _) => {
                            rc(IntegerLit(*n as isize))
                        }
                        (NaturalShow, Some(NaturalLit(n)), _) => {
                            rc(TextLit(n.to_string().into()))
                        }
                        (ListLength, Some(ListLit(_, ys)), _) => {
                            rc(NaturalLit(ys.len()))
                        }
                        (ListHead, Some(ListLit(t, ys)), _) => rc(OptionalLit(
                            t.clone(),
                            ys.iter().cloned().next(),
                        )),
                        (ListLast, Some(ListLit(t, ys)), _) => rc(OptionalLit(
                            t.clone(),
                            ys.iter().cloned().last(),
                        )),
                        (ListReverse, Some(ListLit(t, ys)), _) => {
                            let xs = ys.iter().rev().cloned().collect();
                            rc(ListLit(t.clone(), xs))
                        }
                        (ListBuild, _, [a0, g, ..]) => {
                            loop {
                                if let App(f2, args2) = g.as_ref() {
                                    if let (
                                        Builtin(ListFold),
                                        [_, x, rest..],
                                    ) = (f2.as_ref(), args2.as_slice())
                                    {
                                        // fold/build fusion
                                        break rc(App(
                                            x.clone(),
                                            rest.to_vec(),
                                        ));
                                    }
                                };
                                let a0 = Rc::clone(a0);
                                let a1 = shift(1, &V("a".into(), 0), &a0);
                                break dhall_expr!(g (List a0) (λ(a : a0) -> λ(as : List a1) -> [ a ] # as) ([] : List a0));
                            }
                        }
                        (OptionalBuild, _, [a0, g, ..]) => {
                            loop {
                                if let App(f2, args2) = g.as_ref() {
                                    if let (
                                        Builtin(OptionalFold),
                                        [_, x, rest..],
                                    ) = (f2.as_ref(), args2.as_slice())
                                    {
                                        // fold/build fusion
                                        break rc(App(
                                            x.clone(),
                                            rest.to_vec(),
                                        ));
                                    }
                                };
                                let a0 = Rc::clone(a0);
                                break dhall_expr!((g (Optional a0)) (λ(x: a0) -> [x] :  Optional a0) ([] :  Optional a0));
                            }
                        }
                        (
                            ListFold,
                            Some(ListLit(_, xs)),
                            [_, _, _, cons, nil, ..],
                        ) => xs.iter().rev().fold(Rc::clone(nil), |acc, x| {
                            let x = x.clone();
                            let acc = acc.clone();
                            let cons = Rc::clone(cons);
                            dhall_expr!(cons x acc)
                        }),
                        // // fold/build fusion
                        // (ListFold, [_, App(box Builtin(ListBuild), [_, x, rest..]), rest..]) => {
                        //     normalize_whnf(&App(bx(x.clone()), rest.to_vec()))
                        // }
                        (
                            OptionalFold,
                            Some(OptionalLit(_, Some(x))),
                            [_, _, _, just, _, ..],
                        ) => {
                            let x = x.clone();
                            let just = Rc::clone(just);
                            dhall_expr!(just x)
                        }
                        (
                            OptionalFold,
                            Some(OptionalLit(_, None)),
                            [_, _, _, _, nothing, ..],
                        ) => Rc::clone(nothing),
                        // // fold/build fusion
                        // (OptionalFold, [_, App(box Builtin(OptionalBuild), [_, x, rest..]), rest..]) => {
                        //     normalize_whnf(&App(bx(x.clone()), rest.to_vec()))
                        // }
                        (NaturalBuild, Some(App(f2, args2)), _) => {
                            match (f2.as_ref(), args2.as_slice()) {
                                // fold/build fusion
                                (Builtin(NaturalFold), [x, rest..]) => {
                                    rc(App(x.clone(), rest.to_vec()))
                                }
                                _ => return rc(App(f, args)),
                            }
                        }
                        (NaturalFold, Some(App(f2, args2)), _) => {
                            match (f2.as_ref(), args2.as_slice()) {
                                // fold/build fusion
                                (Builtin(NaturalBuild), [x, rest..]) => {
                                    rc(App(x.clone(), rest.to_vec()))
                                }
                                _ => return rc(App(f, args)),
                            }
                        }
                        (b, _, _) => return rc(App(rc(Builtin(*b)), args)),
                    };
                    normalize_whnf(&rc(Expr::App(
                        ret,
                        args.split_off(len_consumption),
                    )))
                }
                (_, args) => rc(App(f, args.to_vec())),
            }
        }
        BoolIf(b, t, f) => {
            let b = normalize_whnf(b);
            match b.as_ref() {
                BoolLit(true) => normalize_whnf(t),
                BoolLit(false) => normalize_whnf(f),
                _ => rc(BoolIf(b, t.clone(), f.clone())),
            }
        }
        OptionalLit(t, es) => {
            if !es.is_none() {
                rc(OptionalLit(None, es.clone()))
            } else {
                rc(OptionalLit(t.clone(), es.clone()))
            }
        }
        BinOp(o, x, y) => {
            let x = normalize_whnf(x);
            let y = normalize_whnf(y);
            rc(match (o, x.as_ref(), y.as_ref()) {
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
                (TextAppend, TextLit(x), TextLit(y)) => TextLit(x + y),
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
            })
        }
        Field(e, x) => {
            let e = normalize_whnf(e);
            match (e.as_ref(), x) {
                (RecordLit(kvs), x) => match kvs.get(&x) {
                    Some(r) => normalize_whnf(r),
                    None => rc(Field(e, x.clone())),
                },
                (_, x) => rc(Field(e, x.clone())),
            }
        }
        _ => Rc::clone(e),
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
pub fn normalize<S, A>(e: SubExpr<S, A>) -> SubExpr<S, A>
where
    S: fmt::Debug,
    A: fmt::Debug,
{
    map_subexpr_rc(&normalize_whnf(&e), |x| normalize(Rc::clone(x)))
}
