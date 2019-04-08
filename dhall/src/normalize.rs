#![allow(non_snake_case)]
use crate::expr::*;
use dhall_core::*;
use dhall_generator::dhall_expr;
use std::fmt;

impl Typed {
    pub fn normalize(self) -> Normalized {
        Normalized(normalize(self.0), self.1)
    }
    /// Pretends this expression is normalized. Use with care.
    pub fn skip_normalize(self) -> Normalized {
        Normalized(self.0, self.1)
    }
}

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

fn normalize_ref<S, A>(expr: &Expr<S, A>) -> Expr<S, A>
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
fn normalize<S, A>(e: SubExpr<S, A>) -> SubExpr<S, A>
where
    S: fmt::Debug + Clone,
    A: fmt::Debug + Clone,
{
    normalize_ref(e.as_ref()).roll()
}

#[cfg(test)]
mod tests {
    #![rustfmt::skip]

    macro_rules! norm {
        ($name:ident, $path:expr) => {
            make_spec_test!(Normalization, $name, $path);
        };
    }

    norm!(spec_success_haskell_tutorial_access_0, "haskell-tutorial/access/0");
    // norm!(spec_success_haskell_tutorial_access_1, "haskell-tutorial/access/1");
    // norm!(spec_success_haskell_tutorial_combineTypes_0, "haskell-tutorial/combineTypes/0");
    // norm!(spec_success_haskell_tutorial_combineTypes_1, "haskell-tutorial/combineTypes/1");
    // norm!(spec_success_haskell_tutorial_prefer_0, "haskell-tutorial/prefer/0");
    norm!(spec_success_haskell_tutorial_projection_0, "haskell-tutorial/projection/0");


    norm!(spec_success_prelude_Bool_and_0, "prelude/Bool/and/0");
    norm!(spec_success_prelude_Bool_and_1, "prelude/Bool/and/1");
    norm!(spec_success_prelude_Bool_build_0, "prelude/Bool/build/0");
    norm!(spec_success_prelude_Bool_build_1, "prelude/Bool/build/1");
    norm!(spec_success_prelude_Bool_even_0, "prelude/Bool/even/0");
    norm!(spec_success_prelude_Bool_even_1, "prelude/Bool/even/1");
    norm!(spec_success_prelude_Bool_even_2, "prelude/Bool/even/2");
    norm!(spec_success_prelude_Bool_even_3, "prelude/Bool/even/3");
    norm!(spec_success_prelude_Bool_fold_0, "prelude/Bool/fold/0");
    norm!(spec_success_prelude_Bool_fold_1, "prelude/Bool/fold/1");
    norm!(spec_success_prelude_Bool_not_0, "prelude/Bool/not/0");
    norm!(spec_success_prelude_Bool_not_1, "prelude/Bool/not/1");
    norm!(spec_success_prelude_Bool_odd_0, "prelude/Bool/odd/0");
    norm!(spec_success_prelude_Bool_odd_1, "prelude/Bool/odd/1");
    norm!(spec_success_prelude_Bool_odd_2, "prelude/Bool/odd/2");
    norm!(spec_success_prelude_Bool_odd_3, "prelude/Bool/odd/3");
    norm!(spec_success_prelude_Bool_or_0, "prelude/Bool/or/0");
    norm!(spec_success_prelude_Bool_or_1, "prelude/Bool/or/1");
    norm!(spec_success_prelude_Bool_show_0, "prelude/Bool/show/0");
    norm!(spec_success_prelude_Bool_show_1, "prelude/Bool/show/1");
    // norm!(spec_success_prelude_Double_show_0, "prelude/Double/show/0");
    // norm!(spec_success_prelude_Double_show_1, "prelude/Double/show/1");
    // norm!(spec_success_prelude_Integer_show_0, "prelude/Integer/show/0");
    // norm!(spec_success_prelude_Integer_show_1, "prelude/Integer/show/1");
    // norm!(spec_success_prelude_Integer_toDouble_0, "prelude/Integer/toDouble/0");
    // norm!(spec_success_prelude_Integer_toDouble_1, "prelude/Integer/toDouble/1");
    norm!(spec_success_prelude_List_all_0, "prelude/List/all/0");
    norm!(spec_success_prelude_List_all_1, "prelude/List/all/1");
    norm!(spec_success_prelude_List_any_0, "prelude/List/any/0");
    norm!(spec_success_prelude_List_any_1, "prelude/List/any/1");
    norm!(spec_success_prelude_List_build_0, "prelude/List/build/0");
    norm!(spec_success_prelude_List_build_1, "prelude/List/build/1");
    norm!(spec_success_prelude_List_concat_0, "prelude/List/concat/0");
    norm!(spec_success_prelude_List_concat_1, "prelude/List/concat/1");
    norm!(spec_success_prelude_List_concatMap_0, "prelude/List/concatMap/0");
    norm!(spec_success_prelude_List_concatMap_1, "prelude/List/concatMap/1");
    norm!(spec_success_prelude_List_filter_0, "prelude/List/filter/0");
    norm!(spec_success_prelude_List_filter_1, "prelude/List/filter/1");
    norm!(spec_success_prelude_List_fold_0, "prelude/List/fold/0");
    norm!(spec_success_prelude_List_fold_1, "prelude/List/fold/1");
    norm!(spec_success_prelude_List_fold_2, "prelude/List/fold/2");
    norm!(spec_success_prelude_List_generate_0, "prelude/List/generate/0");
    norm!(spec_success_prelude_List_generate_1, "prelude/List/generate/1");
    norm!(spec_success_prelude_List_head_0, "prelude/List/head/0");
    norm!(spec_success_prelude_List_head_1, "prelude/List/head/1");
    norm!(spec_success_prelude_List_indexed_0, "prelude/List/indexed/0");
    norm!(spec_success_prelude_List_indexed_1, "prelude/List/indexed/1");
    norm!(spec_success_prelude_List_iterate_0, "prelude/List/iterate/0");
    norm!(spec_success_prelude_List_iterate_1, "prelude/List/iterate/1");
    norm!(spec_success_prelude_List_last_0, "prelude/List/last/0");
    norm!(spec_success_prelude_List_last_1, "prelude/List/last/1");
    norm!(spec_success_prelude_List_length_0, "prelude/List/length/0");
    norm!(spec_success_prelude_List_length_1, "prelude/List/length/1");
    norm!(spec_success_prelude_List_map_0, "prelude/List/map/0");
    norm!(spec_success_prelude_List_map_1, "prelude/List/map/1");
    norm!(spec_success_prelude_List_null_0, "prelude/List/null/0");
    norm!(spec_success_prelude_List_null_1, "prelude/List/null/1");
    norm!(spec_success_prelude_List_replicate_0, "prelude/List/replicate/0");
    norm!(spec_success_prelude_List_replicate_1, "prelude/List/replicate/1");
    norm!(spec_success_prelude_List_reverse_0, "prelude/List/reverse/0");
    norm!(spec_success_prelude_List_reverse_1, "prelude/List/reverse/1");
    norm!(spec_success_prelude_List_shifted_0, "prelude/List/shifted/0");
    norm!(spec_success_prelude_List_shifted_1, "prelude/List/shifted/1");
    norm!(spec_success_prelude_List_unzip_0, "prelude/List/unzip/0");
    norm!(spec_success_prelude_List_unzip_1, "prelude/List/unzip/1");
    norm!(spec_success_prelude_Natural_build_0, "prelude/Natural/build/0");
    norm!(spec_success_prelude_Natural_build_1, "prelude/Natural/build/1");
    norm!(spec_success_prelude_Natural_enumerate_0, "prelude/Natural/enumerate/0");
    norm!(spec_success_prelude_Natural_enumerate_1, "prelude/Natural/enumerate/1");
    norm!(spec_success_prelude_Natural_even_0, "prelude/Natural/even/0");
    norm!(spec_success_prelude_Natural_even_1, "prelude/Natural/even/1");
    norm!(spec_success_prelude_Natural_fold_0, "prelude/Natural/fold/0");
    norm!(spec_success_prelude_Natural_fold_1, "prelude/Natural/fold/1");
    norm!(spec_success_prelude_Natural_fold_2, "prelude/Natural/fold/2");
    norm!(spec_success_prelude_Natural_isZero_0, "prelude/Natural/isZero/0");
    norm!(spec_success_prelude_Natural_isZero_1, "prelude/Natural/isZero/1");
    norm!(spec_success_prelude_Natural_odd_0, "prelude/Natural/odd/0");
    norm!(spec_success_prelude_Natural_odd_1, "prelude/Natural/odd/1");
    norm!(spec_success_prelude_Natural_product_0, "prelude/Natural/product/0");
    norm!(spec_success_prelude_Natural_product_1, "prelude/Natural/product/1");
    norm!(spec_success_prelude_Natural_show_0, "prelude/Natural/show/0");
    norm!(spec_success_prelude_Natural_show_1, "prelude/Natural/show/1");
    norm!(spec_success_prelude_Natural_sum_0, "prelude/Natural/sum/0");
    norm!(spec_success_prelude_Natural_sum_1, "prelude/Natural/sum/1");
    // norm!(spec_success_prelude_Natural_toDouble_0, "prelude/Natural/toDouble/0");
    // norm!(spec_success_prelude_Natural_toDouble_1, "prelude/Natural/toDouble/1");
    norm!(spec_success_prelude_Natural_toInteger_0, "prelude/Natural/toInteger/0");
    norm!(spec_success_prelude_Natural_toInteger_1, "prelude/Natural/toInteger/1");
    norm!(spec_success_prelude_Optional_all_0, "prelude/Optional/all/0");
    norm!(spec_success_prelude_Optional_all_1, "prelude/Optional/all/1");
    norm!(spec_success_prelude_Optional_any_0, "prelude/Optional/any/0");
    norm!(spec_success_prelude_Optional_any_1, "prelude/Optional/any/1");
    norm!(spec_success_prelude_Optional_build_0, "prelude/Optional/build/0");
    norm!(spec_success_prelude_Optional_build_1, "prelude/Optional/build/1");
    norm!(spec_success_prelude_Optional_concat_0, "prelude/Optional/concat/0");
    norm!(spec_success_prelude_Optional_concat_1, "prelude/Optional/concat/1");
    norm!(spec_success_prelude_Optional_concat_2, "prelude/Optional/concat/2");
    norm!(spec_success_prelude_Optional_filter_0, "prelude/Optional/filter/0");
    norm!(spec_success_prelude_Optional_filter_1, "prelude/Optional/filter/1");
    norm!(spec_success_prelude_Optional_fold_0, "prelude/Optional/fold/0");
    norm!(spec_success_prelude_Optional_fold_1, "prelude/Optional/fold/1");
    norm!(spec_success_prelude_Optional_head_0, "prelude/Optional/head/0");
    norm!(spec_success_prelude_Optional_head_1, "prelude/Optional/head/1");
    norm!(spec_success_prelude_Optional_head_2, "prelude/Optional/head/2");
    norm!(spec_success_prelude_Optional_last_0, "prelude/Optional/last/0");
    norm!(spec_success_prelude_Optional_last_1, "prelude/Optional/last/1");
    norm!(spec_success_prelude_Optional_last_2, "prelude/Optional/last/2");
    norm!(spec_success_prelude_Optional_length_0, "prelude/Optional/length/0");
    norm!(spec_success_prelude_Optional_length_1, "prelude/Optional/length/1");
    norm!(spec_success_prelude_Optional_map_0, "prelude/Optional/map/0");
    norm!(spec_success_prelude_Optional_map_1, "prelude/Optional/map/1");
    norm!(spec_success_prelude_Optional_null_0, "prelude/Optional/null/0");
    norm!(spec_success_prelude_Optional_null_1, "prelude/Optional/null/1");
    norm!(spec_success_prelude_Optional_toList_0, "prelude/Optional/toList/0");
    norm!(spec_success_prelude_Optional_toList_1, "prelude/Optional/toList/1");
    norm!(spec_success_prelude_Optional_unzip_0, "prelude/Optional/unzip/0");
    norm!(spec_success_prelude_Optional_unzip_1, "prelude/Optional/unzip/1");
    norm!(spec_success_prelude_Text_concat_0, "prelude/Text/concat/0");
    norm!(spec_success_prelude_Text_concat_1, "prelude/Text/concat/1");
    // norm!(spec_success_prelude_Text_concatMap_0, "prelude/Text/concatMap/0");
    norm!(spec_success_prelude_Text_concatMap_1, "prelude/Text/concatMap/1");
    // norm!(spec_success_prelude_Text_concatMapSep_0, "prelude/Text/concatMapSep/0");
    // norm!(spec_success_prelude_Text_concatMapSep_1, "prelude/Text/concatMapSep/1");
    // norm!(spec_success_prelude_Text_concatSep_0, "prelude/Text/concatSep/0");
    // norm!(spec_success_prelude_Text_concatSep_1, "prelude/Text/concatSep/1");
    // norm!(spec_success_prelude_Text_show_0, "prelude/Text/show/0");
    // norm!(spec_success_prelude_Text_show_1, "prelude/Text/show/1");



    // norm!(spec_success_remoteSystems, "remoteSystems");
    // norm!(spec_success_simple_doubleShow, "simple/doubleShow");
    // norm!(spec_success_simple_integerShow, "simple/integerShow");
    // norm!(spec_success_simple_integerToDouble, "simple/integerToDouble");
    // norm!(spec_success_simple_letlet, "simple/letlet");
    norm!(spec_success_simple_listBuild, "simple/listBuild");
    norm!(spec_success_simple_multiLine, "simple/multiLine");
    norm!(spec_success_simple_naturalBuild, "simple/naturalBuild");
    norm!(spec_success_simple_naturalPlus, "simple/naturalPlus");
    norm!(spec_success_simple_naturalShow, "simple/naturalShow");
    norm!(spec_success_simple_naturalToInteger, "simple/naturalToInteger");
    norm!(spec_success_simple_optionalBuild, "simple/optionalBuild");
    norm!(spec_success_simple_optionalBuildFold, "simple/optionalBuildFold");
    norm!(spec_success_simple_optionalFold, "simple/optionalFold");
    // norm!(spec_success_simple_sortOperator, "simple/sortOperator");
    // norm!(spec_success_simplifications_and, "simplifications/and");
    // norm!(spec_success_simplifications_eq, "simplifications/eq");
    // norm!(spec_success_simplifications_ifThenElse, "simplifications/ifThenElse");
    // norm!(spec_success_simplifications_ne, "simplifications/ne");
    // norm!(spec_success_simplifications_or, "simplifications/or");


    norm!(spec_success_unit_Bool, "unit/Bool");
    norm!(spec_success_unit_Double, "unit/Double");
    norm!(spec_success_unit_DoubleLiteral, "unit/DoubleLiteral");
    norm!(spec_success_unit_DoubleShow, "unit/DoubleShow");
    // norm!(spec_success_unit_DoubleShowValue, "unit/DoubleShowValue");
    norm!(spec_success_unit_FunctionApplicationCapture, "unit/FunctionApplicationCapture");
    norm!(spec_success_unit_FunctionApplicationNoSubstitute, "unit/FunctionApplicationNoSubstitute");
    norm!(spec_success_unit_FunctionApplicationNormalizeArguments, "unit/FunctionApplicationNormalizeArguments");
    norm!(spec_success_unit_FunctionApplicationSubstitute, "unit/FunctionApplicationSubstitute");
    norm!(spec_success_unit_FunctionNormalizeArguments, "unit/FunctionNormalizeArguments");
    norm!(spec_success_unit_FunctionTypeNormalizeArguments, "unit/FunctionTypeNormalizeArguments");
    // norm!(spec_success_unit_IfAlternativesIdentical, "unit/IfAlternativesIdentical");
    norm!(spec_success_unit_IfFalse, "unit/IfFalse");
    norm!(spec_success_unit_IfNormalizePredicateAndBranches, "unit/IfNormalizePredicateAndBranches");
    // norm!(spec_success_unit_IfTrivial, "unit/IfTrivial");
    norm!(spec_success_unit_IfTrue, "unit/IfTrue");
    norm!(spec_success_unit_Integer, "unit/Integer");
    norm!(spec_success_unit_IntegerNegative, "unit/IntegerNegative");
    norm!(spec_success_unit_IntegerPositive, "unit/IntegerPositive");
    // norm!(spec_success_unit_IntegerShow_12, "unit/IntegerShow-12");
    // norm!(spec_success_unit_IntegerShow12, "unit/IntegerShow12");
    norm!(spec_success_unit_IntegerShow, "unit/IntegerShow");
    // norm!(spec_success_unit_IntegerToDouble_12, "unit/IntegerToDouble-12");
    // norm!(spec_success_unit_IntegerToDouble12, "unit/IntegerToDouble12");
    norm!(spec_success_unit_IntegerToDouble, "unit/IntegerToDouble");
    norm!(spec_success_unit_Kind, "unit/Kind");
    norm!(spec_success_unit_Let, "unit/Let");
    norm!(spec_success_unit_LetWithType, "unit/LetWithType");
    norm!(spec_success_unit_List, "unit/List");
    norm!(spec_success_unit_ListBuild, "unit/ListBuild");
    norm!(spec_success_unit_ListBuildFoldFusion, "unit/ListBuildFoldFusion");
    norm!(spec_success_unit_ListBuildImplementation, "unit/ListBuildImplementation");
    norm!(spec_success_unit_ListFold, "unit/ListFold");
    norm!(spec_success_unit_ListFoldEmpty, "unit/ListFoldEmpty");
    norm!(spec_success_unit_ListFoldOne, "unit/ListFoldOne");
    norm!(spec_success_unit_ListHead, "unit/ListHead");
    norm!(spec_success_unit_ListHeadEmpty, "unit/ListHeadEmpty");
    norm!(spec_success_unit_ListHeadOne, "unit/ListHeadOne");
    norm!(spec_success_unit_ListIndexed, "unit/ListIndexed");
    norm!(spec_success_unit_ListIndexedEmpty, "unit/ListIndexedEmpty");
    norm!(spec_success_unit_ListIndexedOne, "unit/ListIndexedOne");
    norm!(spec_success_unit_ListLast, "unit/ListLast");
    norm!(spec_success_unit_ListLastEmpty, "unit/ListLastEmpty");
    norm!(spec_success_unit_ListLastOne, "unit/ListLastOne");
    norm!(spec_success_unit_ListLength, "unit/ListLength");
    norm!(spec_success_unit_ListLengthEmpty, "unit/ListLengthEmpty");
    norm!(spec_success_unit_ListLengthOne, "unit/ListLengthOne");
    norm!(spec_success_unit_ListNormalizeElements, "unit/ListNormalizeElements");
    norm!(spec_success_unit_ListNormalizeTypeAnnotation, "unit/ListNormalizeTypeAnnotation");
    norm!(spec_success_unit_ListReverse, "unit/ListReverse");
    norm!(spec_success_unit_ListReverseEmpty, "unit/ListReverseEmpty");
    norm!(spec_success_unit_ListReverseTwo, "unit/ListReverseTwo");
    // norm!(spec_success_unit_Merge, "unit/Merge");
    norm!(spec_success_unit_MergeNormalizeArguments, "unit/MergeNormalizeArguments");
    norm!(spec_success_unit_MergeWithType, "unit/MergeWithType");
    norm!(spec_success_unit_MergeWithTypeNormalizeArguments, "unit/MergeWithTypeNormalizeArguments");
    norm!(spec_success_unit_Natural, "unit/Natural");
    norm!(spec_success_unit_NaturalBuild, "unit/NaturalBuild");
    norm!(spec_success_unit_NaturalBuildFoldFusion, "unit/NaturalBuildFoldFusion");
    norm!(spec_success_unit_NaturalBuildImplementation, "unit/NaturalBuildImplementation");
    norm!(spec_success_unit_NaturalEven, "unit/NaturalEven");
    norm!(spec_success_unit_NaturalEvenOne, "unit/NaturalEvenOne");
    norm!(spec_success_unit_NaturalEvenZero, "unit/NaturalEvenZero");
    norm!(spec_success_unit_NaturalFold, "unit/NaturalFold");
    norm!(spec_success_unit_NaturalFoldOne, "unit/NaturalFoldOne");
    norm!(spec_success_unit_NaturalFoldZero, "unit/NaturalFoldZero");
    norm!(spec_success_unit_NaturalIsZero, "unit/NaturalIsZero");
    norm!(spec_success_unit_NaturalIsZeroOne, "unit/NaturalIsZeroOne");
    norm!(spec_success_unit_NaturalIsZeroZero, "unit/NaturalIsZeroZero");
    norm!(spec_success_unit_NaturalLiteral, "unit/NaturalLiteral");
    norm!(spec_success_unit_NaturalOdd, "unit/NaturalOdd");
    norm!(spec_success_unit_NaturalOddOne, "unit/NaturalOddOne");
    norm!(spec_success_unit_NaturalOddZero, "unit/NaturalOddZero");
    norm!(spec_success_unit_NaturalShow, "unit/NaturalShow");
    norm!(spec_success_unit_NaturalShowOne, "unit/NaturalShowOne");
    norm!(spec_success_unit_NaturalToInteger, "unit/NaturalToInteger");
    norm!(spec_success_unit_NaturalToIntegerOne, "unit/NaturalToIntegerOne");
    norm!(spec_success_unit_None, "unit/None");
    norm!(spec_success_unit_NoneNatural, "unit/NoneNatural");
    // norm!(spec_success_unit_OperatorAndEquivalentArguments, "unit/OperatorAndEquivalentArguments");
    // norm!(spec_success_unit_OperatorAndLhsFalse, "unit/OperatorAndLhsFalse");
    // norm!(spec_success_unit_OperatorAndLhsTrue, "unit/OperatorAndLhsTrue");
    // norm!(spec_success_unit_OperatorAndNormalizeArguments, "unit/OperatorAndNormalizeArguments");
    // norm!(spec_success_unit_OperatorAndRhsFalse, "unit/OperatorAndRhsFalse");
    // norm!(spec_success_unit_OperatorAndRhsTrue, "unit/OperatorAndRhsTrue");
    // norm!(spec_success_unit_OperatorEqualEquivalentArguments, "unit/OperatorEqualEquivalentArguments");
    // norm!(spec_success_unit_OperatorEqualLhsTrue, "unit/OperatorEqualLhsTrue");
    // norm!(spec_success_unit_OperatorEqualNormalizeArguments, "unit/OperatorEqualNormalizeArguments");
    // norm!(spec_success_unit_OperatorEqualRhsTrue, "unit/OperatorEqualRhsTrue");
    norm!(spec_success_unit_OperatorListConcatenateLhsEmpty, "unit/OperatorListConcatenateLhsEmpty");
    norm!(spec_success_unit_OperatorListConcatenateListList, "unit/OperatorListConcatenateListList");
    norm!(spec_success_unit_OperatorListConcatenateNormalizeArguments, "unit/OperatorListConcatenateNormalizeArguments");
    norm!(spec_success_unit_OperatorListConcatenateRhsEmpty, "unit/OperatorListConcatenateRhsEmpty");
    // norm!(spec_success_unit_OperatorNotEqualEquivalentArguments, "unit/OperatorNotEqualEquivalentArguments");
    // norm!(spec_success_unit_OperatorNotEqualLhsFalse, "unit/OperatorNotEqualLhsFalse");
    // norm!(spec_success_unit_OperatorNotEqualNormalizeArguments, "unit/OperatorNotEqualNormalizeArguments");
    // norm!(spec_success_unit_OperatorNotEqualRhsFalse, "unit/OperatorNotEqualRhsFalse");
    // norm!(spec_success_unit_OperatorOrEquivalentArguments, "unit/OperatorOrEquivalentArguments");
    // norm!(spec_success_unit_OperatorOrLhsFalse, "unit/OperatorOrLhsFalse");
    // norm!(spec_success_unit_OperatorOrLhsTrue, "unit/OperatorOrLhsTrue");
    // norm!(spec_success_unit_OperatorOrNormalizeArguments, "unit/OperatorOrNormalizeArguments");
    // norm!(spec_success_unit_OperatorOrRhsFalse, "unit/OperatorOrRhsFalse");
    // norm!(spec_success_unit_OperatorOrRhsTrue, "unit/OperatorOrRhsTrue");
    // norm!(spec_success_unit_OperatorPlusLhsZero, "unit/OperatorPlusLhsZero");
    // norm!(spec_success_unit_OperatorPlusNormalizeArguments, "unit/OperatorPlusNormalizeArguments");
    norm!(spec_success_unit_OperatorPlusOneAndOne, "unit/OperatorPlusOneAndOne");
    // norm!(spec_success_unit_OperatorPlusRhsZero, "unit/OperatorPlusRhsZero");
    // norm!(spec_success_unit_OperatorTextConcatenateLhsEmpty, "unit/OperatorTextConcatenateLhsEmpty");
    // norm!(spec_success_unit_OperatorTextConcatenateNormalizeArguments, "unit/OperatorTextConcatenateNormalizeArguments");
    // norm!(spec_success_unit_OperatorTextConcatenateRhsEmpty, "unit/OperatorTextConcatenateRhsEmpty");
    norm!(spec_success_unit_OperatorTextConcatenateTextText, "unit/OperatorTextConcatenateTextText");
    // norm!(spec_success_unit_OperatorTimesLhsOne, "unit/OperatorTimesLhsOne");
    // norm!(spec_success_unit_OperatorTimesLhsZero, "unit/OperatorTimesLhsZero");
    // norm!(spec_success_unit_OperatorTimesNormalizeArguments, "unit/OperatorTimesNormalizeArguments");
    // norm!(spec_success_unit_OperatorTimesRhsOne, "unit/OperatorTimesRhsOne");
    // norm!(spec_success_unit_OperatorTimesRhsZero, "unit/OperatorTimesRhsZero");
    norm!(spec_success_unit_OperatorTimesTwoAndTwo, "unit/OperatorTimesTwoAndTwo");
    norm!(spec_success_unit_Optional, "unit/Optional");
    norm!(spec_success_unit_OptionalBuild, "unit/OptionalBuild");
    norm!(spec_success_unit_OptionalBuildFoldFusion, "unit/OptionalBuildFoldFusion");
    norm!(spec_success_unit_OptionalBuildImplementation, "unit/OptionalBuildImplementation");
    norm!(spec_success_unit_OptionalFold, "unit/OptionalFold");
    norm!(spec_success_unit_OptionalFoldNone, "unit/OptionalFoldNone");
    norm!(spec_success_unit_OptionalFoldSome, "unit/OptionalFoldSome");
    norm!(spec_success_unit_Record, "unit/Record");
    norm!(spec_success_unit_RecordEmpty, "unit/RecordEmpty");
    norm!(spec_success_unit_RecordProjection, "unit/RecordProjection");
    norm!(spec_success_unit_RecordProjectionEmpty, "unit/RecordProjectionEmpty");
    norm!(spec_success_unit_RecordProjectionNormalizeArguments, "unit/RecordProjectionNormalizeArguments");
    norm!(spec_success_unit_RecordSelection, "unit/RecordSelection");
    norm!(spec_success_unit_RecordSelectionNormalizeArguments, "unit/RecordSelectionNormalizeArguments");
    norm!(spec_success_unit_RecordType, "unit/RecordType");
    norm!(spec_success_unit_RecordTypeEmpty, "unit/RecordTypeEmpty");
    // norm!(spec_success_unit_RecursiveRecordMergeCollision, "unit/RecursiveRecordMergeCollision");
    // norm!(spec_success_unit_RecursiveRecordMergeLhsEmpty, "unit/RecursiveRecordMergeLhsEmpty");
    // norm!(spec_success_unit_RecursiveRecordMergeNoCollision, "unit/RecursiveRecordMergeNoCollision");
    // norm!(spec_success_unit_RecursiveRecordMergeNormalizeArguments, "unit/RecursiveRecordMergeNormalizeArguments");
    // norm!(spec_success_unit_RecursiveRecordMergeRhsEmpty, "unit/RecursiveRecordMergeRhsEmpty");
    // norm!(spec_success_unit_RecursiveRecordTypeMergeCollision, "unit/RecursiveRecordTypeMergeCollision");
    // norm!(spec_success_unit_RecursiveRecordTypeMergeLhsEmpty, "unit/RecursiveRecordTypeMergeLhsEmpty");
    // norm!(spec_success_unit_RecursiveRecordTypeMergeNoCollision, "unit/RecursiveRecordTypeMergeNoCollision");
    // norm!(spec_success_unit_RecursiveRecordTypeMergeNormalizeArguments, "unit/RecursiveRecordTypeMergeNormalizeArguments");
    // norm!(spec_success_unit_RecursiveRecordTypeMergeRhsEmpty, "unit/RecursiveRecordTypeMergeRhsEmpty");
    // norm!(spec_success_unit_RightBiasedRecordMergeCollision, "unit/RightBiasedRecordMergeCollision");
    // norm!(spec_success_unit_RightBiasedRecordMergeLhsEmpty, "unit/RightBiasedRecordMergeLhsEmpty");
    // norm!(spec_success_unit_RightBiasedRecordMergeNoCollision, "unit/RightBiasedRecordMergeNoCollision");
    // norm!(spec_success_unit_RightBiasedRecordMergeNormalizeArguments, "unit/RightBiasedRecordMergeNormalizeArguments");
    // norm!(spec_success_unit_RightBiasedRecordMergeRhsEmpty, "unit/RightBiasedRecordMergeRhsEmpty");
    norm!(spec_success_unit_SomeNormalizeArguments, "unit/SomeNormalizeArguments");
    norm!(spec_success_unit_Sort, "unit/Sort");
    norm!(spec_success_unit_Text, "unit/Text");
    // norm!(spec_success_unit_TextInterpolate, "unit/TextInterpolate");
    norm!(spec_success_unit_TextLiteral, "unit/TextLiteral");
    norm!(spec_success_unit_TextNormalizeInterpolations, "unit/TextNormalizeInterpolations");
    norm!(spec_success_unit_TextShow, "unit/TextShow");
    // norm!(spec_success_unit_TextShowAllEscapes, "unit/TextShowAllEscapes");
    norm!(spec_success_unit_True, "unit/True");
    norm!(spec_success_unit_Type, "unit/Type");
    norm!(spec_success_unit_TypeAnnotation, "unit/TypeAnnotation");
    // norm!(spec_success_unit_UnionNormalizeAlternatives, "unit/UnionNormalizeAlternatives");
    norm!(spec_success_unit_UnionNormalizeArguments, "unit/UnionNormalizeArguments");
    // norm!(spec_success_unit_UnionProjectConstructor, "unit/UnionProjectConstructor");
    norm!(spec_success_unit_UnionProjectConstructorNormalizeArguments, "unit/UnionProjectConstructorNormalizeArguments");
    // norm!(spec_success_unit_UnionSortAlternatives, "unit/UnionSortAlternatives");
    // norm!(spec_success_unit_UnionType, "unit/UnionType");
    norm!(spec_success_unit_UnionTypeEmpty, "unit/UnionTypeEmpty");
    // norm!(spec_success_unit_UnionTypeNormalizeArguments, "unit/UnionTypeNormalizeArguments");
    norm!(spec_success_unit_Variable, "unit/Variable");
}
