#![allow(non_snake_case)]
use dhall_core::*;
use dhall_generator::dhall_expr;
use std::fmt;
use std::rc::Rc;

fn apply_builtin<S, A>(
    b: Builtin,
    mut args: Vec<SubExpr<S, A>>,
) -> SubExpr<S, A>
where
    S: fmt::Debug,
    A: fmt::Debug,
{
    use dhall_core::Builtin::*;
    use dhall_core::Expr::*;
    let f = rc(Builtin(b));
    // How many arguments a builtin needs, and which argument
    // should be normalized and pattern-matched
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
        ListIndexed => (2, Some(1)),
        ListBuild => (2, Some(1)),
        OptionalBuild => (2, Some(1)),
        ListFold => (5, Some(1)),
        OptionalFold => (5, Some(1)),
        NaturalBuild => (1, Some(0)),
        NaturalFold => (4, Some(0)),
        _ => (0, None),
    };
    // Abort if not enough arguments present
    if len_consumption > args.len() {
        return rc(App(f, args));
    }
    // Normalize the important argument
    if let Some(i) = arg_to_eval {
        args[i] = Rc::clone(&normalize_whnf(&args[i]));
    }
    let evaled_arg = arg_to_eval.map(|i| args[i].as_ref());

    let ret = match (b, evaled_arg, args.as_slice()) {
        (OptionalSome, _, [x, ..]) => rc(NEOptionalLit(Rc::clone(x))),
        (OptionalNone, _, [t, ..]) => rc(EmptyOptionalLit(Rc::clone(t))),
        (NaturalIsZero, Some(NaturalLit(n)), _) => rc(BoolLit(*n == 0)),
        (NaturalEven, Some(NaturalLit(n)), _) => rc(BoolLit(*n % 2 == 0)),
        (NaturalOdd, Some(NaturalLit(n)), _) => rc(BoolLit(*n % 2 != 0)),
        (NaturalToInteger, Some(NaturalLit(n)), _) => {
            rc(IntegerLit(*n as isize))
        }
        (NaturalShow, Some(NaturalLit(n)), _) => {
            rc(TextLit(n.to_string().into()))
        }
        (ListLength, Some(EmptyListLit(_)), _) => rc(NaturalLit(0)),
        (ListLength, Some(NEListLit(ys)), _) => rc(NaturalLit(ys.len())),
        (ListHead, Some(EmptyListLit(t)), _) => rc(EmptyOptionalLit(t.clone())),
        (ListHead, Some(NEListLit(ys)), _) => {
            rc(NEOptionalLit(ys.first().unwrap().clone()))
        }
        (ListLast, Some(EmptyListLit(t)), _) => rc(EmptyOptionalLit(t.clone())),
        (ListLast, Some(NEListLit(ys)), _) => {
            rc(NEOptionalLit(ys.last().unwrap().clone()))
        }
        (ListReverse, Some(EmptyListLit(t)), _) => rc(EmptyListLit(t.clone())),
        (ListReverse, Some(NEListLit(ys)), _) => {
            let ys = ys.iter().rev().cloned().collect();
            rc(NEListLit(ys))
        }
        (ListIndexed, Some(EmptyListLit(t)), _) => {
            let t = Rc::clone(t);
            dhall_expr!([] : List ({ index : Natural, value : t }))
        }
        (ListIndexed, Some(NEListLit(xs)), _) => {
            let xs = xs
                .iter()
                .cloned()
                .enumerate()
                .map(|(i, e)| {
                    let i = rc(NaturalLit(i));
                    dhall_expr!({ index = i, value = e })
                })
                .collect();
            rc(NEListLit(xs))
        }
        (ListBuild, _, [a0, g, ..]) => {
            loop {
                if let App(f2, args2) = g.as_ref() {
                    if let (Builtin(ListFold), [_, x, rest..]) =
                        (f2.as_ref(), args2.as_slice())
                    {
                        // fold/build fusion
                        break rc(App(x.clone(), rest.to_vec()));
                    }
                };
                let a0 = Rc::clone(a0);
                let a1 = shift(1, &V("a".into(), 0), &a0);
                // TODO: use Embed to avoid reevaluating g
                break dhall_expr!(g (List a0) (λ(a : a0) -> λ(as : List a1) -> [ a ] # as) ([] : List a0));
            }
        }
        (OptionalBuild, _, [a0, g, ..]) => {
            loop {
                if let App(f2, args2) = g.as_ref() {
                    if let (Builtin(OptionalFold), [_, x, rest..]) =
                        (f2.as_ref(), args2.as_slice())
                    {
                        // fold/build fusion
                        break rc(App(x.clone(), rest.to_vec()));
                    }
                };
                let a0 = Rc::clone(a0);
                // TODO: use Embed to avoid reevaluating g
                break dhall_expr!((g (Optional a0)) (λ(x: a0) -> Some x) (None a0));
            }
        }
        (ListFold, Some(EmptyListLit(_)), [_, _, _, _, nil, ..]) => {
            Rc::clone(nil)
        }
        (ListFold, Some(NEListLit(xs)), [_, _, _, cons, nil, ..]) => {
            xs.iter().rev().fold(Rc::clone(nil), |acc, x| {
                let x = x.clone();
                let acc = acc.clone();
                let cons = Rc::clone(cons);
                dhall_expr!(cons x acc)
            })
        }
        // // fold/build fusion
        // (ListFold, [_, App(box Builtin(ListBuild), [_, x, rest..]), rest..]) => {
        //     normalize_whnf(&App(bx(x.clone()), rest.to_vec()))
        // }
        (OptionalFold, Some(NEOptionalLit(x)), [_, _, _, just, _, ..]) => {
            let x = x.clone();
            let just = Rc::clone(just);
            dhall_expr!(just x)
        }
        (
            OptionalFold,
            Some(EmptyOptionalLit(_)),
            [_, _, _, _, nothing, ..],
        ) => Rc::clone(nothing),
        // // fold/build fusion
        // (OptionalFold, [_, App(box Builtin(OptionalBuild), [_, x, rest..]), rest..]) => {
        //     normalize_whnf(&App(bx(x.clone()), rest.to_vec()))
        // }
        (NaturalBuild, _, [g, ..]) => {
            loop {
                if let App(f2, args2) = g.as_ref() {
                    if let (Builtin(NaturalFold), [x, rest..]) =
                        (f2.as_ref(), args2.as_slice())
                    {
                        // fold/build fusion
                        break rc(App(x.clone(), rest.to_vec()));
                    }
                };
                // TODO: use Embed to avoid reevaluating g
                break dhall_expr!(g Natural (λ(x : Natural) -> x + 1) 0);
            }
        }
        (NaturalFold, Some(NaturalLit(0)), [_, _, _, zero]) => Rc::clone(zero),
        (NaturalFold, Some(NaturalLit(n)), [_, t, succ, zero]) => {
            let fold = rc(Builtin(NaturalFold));
            let n = rc(NaturalLit(n - 1));
            let t = Rc::clone(t);
            let succ = Rc::clone(succ);
            let zero = Rc::clone(zero);
            dhall_expr!(succ (fold n t succ zero))
        }
        // (NaturalFold, Some(App(f2, args2)), _) => {
        //     match (f2.as_ref(), args2.as_slice()) {
        //         // fold/build fusion
        //         (Builtin(NaturalBuild), [x, rest..]) => {
        //             rc(App(x.clone(), rest.to_vec()))
        //         }
        //         _ => return rc(App(f, args)),
        //     }
        // }
        _ => return rc(App(f, args)),
    };
    // Put the remaining arguments back and eval again. In most cases
    // ret will not be of a form that can be applied, so this won't go very deep.
    // In lots of cases, there are no remaining args so this cann will just return ret.
    normalize_whnf(&rc(Expr::App(ret, args.split_off(len_consumption))))
}

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
    use dhall_core::Expr::*;
    match e.as_ref() {
        Let(f, _, r, b) => {
            let vf0 = &V(f.clone(), 0);
            let r2 = shift(1, vf0, r);
            // TODO: use a context
            let b2 = subst(vf0, &r2, b);
            // TODO: add tests sensitive to shift errors before
            // trying anything
            let b3 = shift(-1, vf0, &b2);
            normalize_whnf(&b3)
        }
        Annot(x, _) => normalize_whnf(x),
        Note(_, e) => normalize_whnf(e),
        App(f, args) => {
            let f = normalize_whnf(f);
            match (f.as_ref(), args.as_slice()) {
                (_, []) => f,
                // TODO: use Embed to avoid reevaluating f
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
                (Builtin(b), _) => apply_builtin(*b, args.to_vec()),
                _ => rc(App(f, args.to_vec())),
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
        // TODO: interpolation
        // TextLit(t) =>
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
                (TextAppend, TextLit(x), TextLit(y)) => TextLit(x + y),
                (ListAppend, EmptyListLit(t), EmptyListLit(_)) => {
                    EmptyListLit(Rc::clone(t))
                }
                (ListAppend, EmptyListLit(_), _) => return y,
                (ListAppend, _, EmptyListLit(_)) => return x,
                (ListAppend, NEListLit(xs), NEListLit(ys)) => {
                    let xs = xs.into_iter().cloned();
                    let ys = ys.into_iter().cloned();
                    NEListLit(xs.chain(ys).collect())
                }
                (o, _, _) => BinOp(*o, x, y),
            })
        }
        Merge(x, y, t) => {
            let x = normalize_whnf(x);
            let y = normalize_whnf(y);
            match (x.as_ref(), y.as_ref()) {
                (RecordLit(handlers), UnionLit(k, v, _)) => {
                    match handlers.get(&k) {
                        Some(h) => {
                            normalize_whnf(&rc(App(h.clone(), vec![v.clone()])))
                        }
                        None => rc(Merge(x, y, t.clone())),
                    }
                }
                _ => rc(Merge(x, y, t.clone())),
            }
        }
        Field(e, l) => {
            let e = normalize_whnf(e);
            match e.as_ref() {
                RecordLit(kvs) => match kvs.get(&l) {
                    Some(r) => normalize_whnf(r),
                    None => rc(Field(e, l.clone())),
                },
                _ => rc(Field(e, l.clone())),
            }
        }
        Projection(_, ls) if ls.is_empty() => {
            rc(RecordLit(std::collections::BTreeMap::new()))
        }
        Projection(e, ls) => {
            let e = normalize_whnf(e);
            match e.as_ref() {
                RecordLit(kvs) => rc(RecordLit(
                    ls.iter()
                        .filter_map(|l| {
                            kvs.get(l).map(|x| (l.clone(), x.clone()))
                        })
                        .collect(),
                )),
                _ => rc(Projection(e, ls.clone())),
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
