#![allow(non_snake_case)]
use dhall_core::*;
use dhall_generator::dhall_expr;
use std::fmt;

fn apply_builtin<S, A>(b: Builtin, args: &Vec<Expr<S, A>>) -> WhatNext<S, A>
where
    S: fmt::Debug + Clone,
    A: fmt::Debug + Clone,
{
    use dhall_core::Builtin::*;
    use dhall_core::ExprF::*;
    use WhatNext::*;
    let (ret, rest) = match (b, args.as_slice()) {
        (OptionalSome, [x, rest..]) => (rc(NEOptionalLit(x.roll())), rest),
        (OptionalNone, [t, rest..]) => (rc(EmptyOptionalLit(t.roll())), rest),
        (NaturalIsZero, [NaturalLit(n), rest..]) => {
            (rc(BoolLit(*n == 0)), rest)
        }
        (NaturalEven, [NaturalLit(n), rest..]) => {
            (rc(BoolLit(*n % 2 == 0)), rest)
        }
        (NaturalOdd, [NaturalLit(n), rest..]) => {
            (rc(BoolLit(*n % 2 != 0)), rest)
        }
        (NaturalToInteger, [NaturalLit(n), rest..]) => {
            (rc(IntegerLit(*n as isize)), rest)
        }
        (NaturalShow, [NaturalLit(n), rest..]) => {
            (rc(TextLit(n.to_string().into())), rest)
        }
        (ListLength, [_, EmptyListLit(_), rest..]) => (rc(NaturalLit(0)), rest),
        (ListLength, [_, NEListLit(ys), rest..]) => {
            (rc(NaturalLit(ys.len())), rest)
        }
        (ListHead, [_, EmptyListLit(t), rest..]) => {
            (rc(EmptyOptionalLit(t.clone())), rest)
        }
        (ListHead, [_, NEListLit(ys), rest..]) => {
            (rc(NEOptionalLit(ys.first().unwrap().clone())), rest)
        }
        (ListLast, [_, EmptyListLit(t), rest..]) => {
            (rc(EmptyOptionalLit(t.clone())), rest)
        }
        (ListLast, [_, NEListLit(ys), rest..]) => {
            (rc(NEOptionalLit(ys.last().unwrap().clone())), rest)
        }
        (ListReverse, [_, EmptyListLit(t), rest..]) => {
            (rc(EmptyListLit(t.clone())), rest)
        }
        (ListReverse, [_, NEListLit(ys), rest..]) => {
            let ys = ys.iter().rev().cloned().collect();
            (rc(NEListLit(ys)), rest)
        }
        (ListIndexed, [_, EmptyListLit(t), rest..]) => (
            dhall_expr!([] : List ({ index : Natural, value : t })),
            rest,
        ),
        (ListIndexed, [_, NEListLit(xs), rest..]) => {
            let xs = xs
                .iter()
                .cloned()
                .enumerate()
                .map(|(i, e)| {
                    let i = rc(NaturalLit(i));
                    dhall_expr!({ index = i, value = e })
                })
                .collect();
            (rc(NEListLit(xs)), rest)
        }
        (ListBuild, [a0, g, rest..]) => {
            loop {
                if let App(f2, args2) = g {
                    if let (Builtin(ListFold), [_, x, rest_inner..]) =
                        (f2.as_ref(), args2.as_slice())
                    {
                        // fold/build fusion
                        break (rc(App(x.clone(), rest_inner.to_vec())), rest);
                    }
                };
                let a0 = a0.roll();
                let a1 = shift(1, &V("a".into(), 0), &a0);
                let g = g.roll();
                break (
                    dhall_expr!(
                        g
                        (List a0)
                        (λ(x : a0) -> λ(xs : List a1) -> [ x ] # xs)
                        ([] : List a0)
                    ),
                    rest,
                );
            }
        }
        (OptionalBuild, [a0, g, rest..]) => {
            loop {
                if let App(f2, args2) = g {
                    if let (Builtin(OptionalFold), [_, x, rest_inner..]) =
                        (f2.as_ref(), args2.as_slice())
                    {
                        // fold/build fusion
                        break (rc(App(x.clone(), rest_inner.to_vec())), rest);
                    }
                };
                let a0 = a0.roll();
                let g = g.roll();
                break (
                    dhall_expr!(
                        g
                        (Optional a0)
                        (λ(x: a0) -> Some x)
                        (None a0)
                    ),
                    rest,
                );
            }
        }
        (ListFold, [_, EmptyListLit(_), _, _, nil, rest..]) => {
            (nil.roll(), rest)
        }
        (ListFold, [_, NEListLit(xs), _, cons, nil, rest..]) => (
            xs.iter().rev().fold(nil.roll(), |acc, x| {
                let x = x.clone();
                let acc = acc.clone();
                let cons = cons.roll();
                dhall_expr!(cons x acc)
            }),
            rest,
        ),
        // // fold/build fusion
        // (ListFold, [_, App(box Builtin(ListBuild), [_, x, rest..]), rest..]) => {
        //     normalize_ref(&App(bx(x.clone()), rest.to_vec()))
        // }
        (OptionalFold, [_, NEOptionalLit(x), _, just, _, rest..]) => {
            let x = x.clone();
            let just = just.roll();
            (dhall_expr!(just x), rest)
        }
        (OptionalFold, [_, EmptyOptionalLit(_), _, _, nothing, rest..]) => {
            (nothing.roll(), rest)
        }
        // // fold/build fusion
        // (OptionalFold, [_, App(box Builtin(OptionalBuild), [_, x, rest..]), rest..]) => {
        //     normalize_ref(&App(bx(x.clone()), rest.to_vec()))
        // }
        (NaturalBuild, [g, rest..]) => {
            loop {
                if let App(f2, args2) = g {
                    if let (Builtin(NaturalFold), [x, rest_inner..]) =
                        (f2.as_ref(), args2.as_slice())
                    {
                        // fold/build fusion
                        break (rc(App(x.clone(), rest_inner.to_vec())), rest);
                    }
                };
                let g = g.roll();
                break (
                    dhall_expr!(g Natural (λ(x : Natural) -> x + 1) 0),
                    rest,
                );
            }
        }
        (NaturalFold, [NaturalLit(0), _, _, zero, rest..]) => {
            (zero.roll(), rest)
        }
        (NaturalFold, [NaturalLit(n), t, succ, zero, rest..]) => {
            let fold = rc(Builtin(NaturalFold));
            let n = rc(NaturalLit(n - 1));
            let t = t.roll();
            let succ = succ.roll();
            let zero = zero.roll();
            (dhall_expr!(succ (fold n t succ zero)), rest)
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
        _ => return DoneAsIs,
    };
    // Put the remaining arguments back and eval again. In most cases
    // ret will not be of a form that can be applied, so this won't go very deep.
    // In lots of cases, there are no remaining args so this cann will just return ret.
    let rest: Vec<SubExpr<S, A>> = rest.iter().map(ExprF::roll).collect();
    Continue(ExprF::App(ret, rest))
}

// Small enum to help with being DRY
enum WhatNext<'a, S, A> {
    // Recurse on this expression
    Continue(Expr<S, A>),
    ContinueSub(SubExpr<S, A>),
    // The following expression is the normal form
    Done(Expr<S, A>),
    DoneRef(&'a Expr<S, A>),
    DoneRefSub(&'a SubExpr<S, A>),
    // The current expression is already in normal form
    DoneAsIs,
}

pub fn normalize_ref<S, A>(expr: &Expr<S, A>) -> Expr<S, A>
where
    S: fmt::Debug + Clone,
    A: fmt::Debug + Clone,
{
    use dhall_core::BinOp::*;
    use dhall_core::ExprF::*;
    // Recursively normalize all subexpressions
    let expr: ExprF<Expr<S, A>, Label, S, A> =
        expr.map_ref_simple(|e| normalize_ref(e.as_ref()));

    use WhatNext::*;
    let what_next = match &expr {
        Let(f, _, r, b) => {
            let vf0 = &V(f.clone(), 0);
            // TODO: use a context
            ContinueSub(subst_shift(vf0, &r.roll(), &b.roll()))
        }
        Annot(x, _) => DoneRef(x),
        Note(_, e) => DoneRef(e),
        App(f, args) if args.is_empty() => DoneRef(f),
        App(App(f, args1), args2) => Continue(App(
            f.clone(),
            args1
                .iter()
                .cloned()
                .chain(args2.iter().map(ExprF::roll))
                .collect(),
        )),
        App(Builtin(b), args) => apply_builtin(*b, args),
        App(Lam(x, _, b), args) => {
            let mut iter = args.iter();
            // We know args is nonempty
            let a = iter.next().unwrap();
            // Beta reduce
            let vx0 = &V(x.clone(), 0);
            let b2 = subst_shift(vx0, &a.roll(), &b);
            Continue(App(b2, iter.map(ExprF::roll).collect()))
        }
        BoolIf(BoolLit(true), t, _) => DoneRef(t),
        BoolIf(BoolLit(false), _, f) => DoneRef(f),
        // TODO: interpolation
        // TextLit(t) =>
        BinOp(BoolAnd, BoolLit(x), BoolLit(y)) => Done(BoolLit(*x && *y)),
        BinOp(BoolOr, BoolLit(x), BoolLit(y)) => Done(BoolLit(*x || *y)),
        BinOp(BoolEQ, BoolLit(x), BoolLit(y)) => Done(BoolLit(x == y)),
        BinOp(BoolNE, BoolLit(x), BoolLit(y)) => Done(BoolLit(x != y)),
        BinOp(NaturalPlus, NaturalLit(x), NaturalLit(y)) => {
            Done(NaturalLit(x + y))
        }
        BinOp(NaturalTimes, NaturalLit(x), NaturalLit(y)) => {
            Done(NaturalLit(x * y))
        }
        BinOp(TextAppend, TextLit(x), TextLit(y)) => Done(TextLit(x + y)),
        BinOp(ListAppend, EmptyListLit(t), EmptyListLit(_)) => {
            Done(EmptyListLit(SubExpr::clone(t)))
        }
        BinOp(ListAppend, EmptyListLit(_), y) => DoneRef(y),
        BinOp(ListAppend, x, EmptyListLit(_)) => DoneRef(x),
        BinOp(ListAppend, NEListLit(xs), NEListLit(ys)) => {
            let xs = xs.into_iter().cloned();
            let ys = ys.into_iter().cloned();
            Done(NEListLit(xs.chain(ys).collect()))
        }
        Merge(RecordLit(handlers), UnionLit(k, v, _), _) => {
            match handlers.get(&k) {
                Some(h) => Continue(App(h.clone(), vec![v.clone()])),
                None => DoneAsIs,
            }
        }
        Field(RecordLit(kvs), l) => match kvs.get(&l) {
            Some(r) => DoneRefSub(r),
            None => DoneAsIs,
        },
        Projection(_, ls) if ls.is_empty() => {
            Done(RecordLit(std::collections::BTreeMap::new()))
        }
        Projection(RecordLit(kvs), ls) => Done(RecordLit(
            ls.iter()
                .filter_map(|l| kvs.get(l).map(|x| (l.clone(), x.clone())))
                .collect(),
        )),
        _ => DoneAsIs,
    };

    match what_next {
        Continue(e) => normalize_ref(&e),
        ContinueSub(e) => normalize_ref(e.as_ref()),
        Done(e) => e,
        DoneRef(e) => e.clone(),
        DoneRefSub(e) => e.unroll(),
        DoneAsIs => expr.map_ref_simple(ExprF::roll),
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
    S: fmt::Debug + Clone,
    A: fmt::Debug + Clone,
{
    normalize_ref(e.as_ref()).roll()
}
