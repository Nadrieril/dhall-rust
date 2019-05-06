use std::collections::BTreeMap;

use dhall_syntax::{BinOp, Builtin, ExprF, InterpolatedTextContents, Label, X};

use crate::core::context::NormalizationContext;
use crate::core::thunk::{Thunk, TypeThunk};
use crate::core::value::Value;
use crate::phase::{NormalizedSubExpr, ResolvedSubExpr, Typed};

pub(crate) type InputSubExpr = ResolvedSubExpr;
pub(crate) type OutputSubExpr = NormalizedSubExpr;

pub(crate) fn apply_builtin(b: Builtin, args: Vec<Thunk>) -> Value {
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

pub(crate) fn apply_any(f: Thunk, a: Thunk) -> Value {
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

pub(crate) fn squash_textlit(
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
pub(crate) fn normalize_whnf(
    ctx: NormalizationContext,
    expr: InputSubExpr,
) -> Value {
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

pub(crate) fn normalize_one_layer(expr: ExprF<Thunk, Label, X>) -> Value {
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
                        _ if e1 == e2 => RetThunkRef(e1),
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
                (BoolAnd, _, _) if x == y => RetThunkRef(x),
                (BoolOr, BoolLit(true), _) => RetValue(BoolLit(true)),
                (BoolOr, _, BoolLit(true)) => RetValue(BoolLit(true)),
                (BoolOr, BoolLit(false), _) => RetThunkRef(y),
                (BoolOr, _, BoolLit(false)) => RetThunkRef(x),
                (BoolOr, _, _) if x == y => RetThunkRef(x),
                (BoolEQ, BoolLit(true), _) => RetThunkRef(y),
                (BoolEQ, _, BoolLit(true)) => RetThunkRef(x),
                (BoolEQ, BoolLit(x), BoolLit(y)) => RetValue(BoolLit(x == y)),
                (BoolEQ, _, _) if x == y => RetValue(BoolLit(true)),
                (BoolNE, BoolLit(false), _) => RetThunkRef(y),
                (BoolNE, _, BoolLit(false)) => RetThunkRef(x),
                (BoolNE, BoolLit(x), BoolLit(y)) => RetValue(BoolLit(x != y)),
                (BoolNE, _, _) if x == y => RetValue(BoolLit(false)),

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
                    squash_textlit(x.iter().chain(y.iter()).cloned()),
                )),
                (TextAppend, TextLit(x), _) => {
                    use std::iter::once;
                    let y = InterpolatedTextContents::Expr(y.clone());
                    RetValue(TextLit(squash_textlit(
                        x.iter().cloned().chain(once(y)),
                    )))
                }
                (TextAppend, _, TextLit(y)) => {
                    use std::iter::once;
                    let x = InterpolatedTextContents::Expr(x.clone());
                    RetValue(TextLit(squash_textlit(
                        once(x).chain(y.iter().cloned()),
                    )))
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
    norm!(success_simplifications_and, "simplifications/and");
    norm!(success_simplifications_eq, "simplifications/eq");
    norm!(success_simplifications_ifThenElse, "simplifications/ifThenElse");
    norm!(success_simplifications_ne, "simplifications/ne");
    norm!(success_simplifications_or, "simplifications/or");

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
    norm!(success_unit_IfAlternativesIdentical, "unit/IfAlternativesIdentical");
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
    norm!(success_unit_OperatorAndEquivalentArguments, "unit/OperatorAndEquivalentArguments");
    norm!(success_unit_OperatorAndLhsFalse, "unit/OperatorAndLhsFalse");
    norm!(success_unit_OperatorAndLhsTrue, "unit/OperatorAndLhsTrue");
    norm!(success_unit_OperatorAndNormalizeArguments, "unit/OperatorAndNormalizeArguments");
    norm!(success_unit_OperatorAndRhsFalse, "unit/OperatorAndRhsFalse");
    norm!(success_unit_OperatorAndRhsTrue, "unit/OperatorAndRhsTrue");
    norm!(success_unit_OperatorEqualEquivalentArguments, "unit/OperatorEqualEquivalentArguments");
    norm!(success_unit_OperatorEqualLhsTrue, "unit/OperatorEqualLhsTrue");
    norm!(success_unit_OperatorEqualNormalizeArguments, "unit/OperatorEqualNormalizeArguments");
    norm!(success_unit_OperatorEqualRhsTrue, "unit/OperatorEqualRhsTrue");
    norm!(success_unit_OperatorListConcatenateLhsEmpty, "unit/OperatorListConcatenateLhsEmpty");
    norm!(success_unit_OperatorListConcatenateListList, "unit/OperatorListConcatenateListList");
    norm!(success_unit_OperatorListConcatenateNormalizeArguments, "unit/OperatorListConcatenateNormalizeArguments");
    norm!(success_unit_OperatorListConcatenateRhsEmpty, "unit/OperatorListConcatenateRhsEmpty");
    norm!(success_unit_OperatorNotEqualEquivalentArguments, "unit/OperatorNotEqualEquivalentArguments");
    norm!(success_unit_OperatorNotEqualLhsFalse, "unit/OperatorNotEqualLhsFalse");
    norm!(success_unit_OperatorNotEqualNormalizeArguments, "unit/OperatorNotEqualNormalizeArguments");
    norm!(success_unit_OperatorNotEqualRhsFalse, "unit/OperatorNotEqualRhsFalse");
    norm!(success_unit_OperatorOrEquivalentArguments, "unit/OperatorOrEquivalentArguments");
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
