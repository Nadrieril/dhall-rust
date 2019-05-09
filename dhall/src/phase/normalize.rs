use std::collections::HashMap;

use dhall_syntax::{
    BinOp, Builtin, ExprF, InterpolatedText, InterpolatedTextContents,
    NaiveDouble, X,
};

use crate::core::context::NormalizationContext;
use crate::core::thunk::{Thunk, TypeThunk};
use crate::core::value::Value;
use crate::core::var::Subst;
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
        (IntegerShow, [n, r..]) => match &*n.as_value() {
            IntegerLit(n) => {
                let s = if *n < 0 {
                    n.to_string()
                } else {
                    format!("+{}", n)
                };
                Ok((r, TextLit(vec![InterpolatedTextContents::Text(s)])))
            }
            _ => Err(()),
        },
        (IntegerToDouble, [n, r..]) => match &*n.as_value() {
            IntegerLit(n) => Ok((r, DoubleLit(NaiveDouble::from(*n as f64)))),
            _ => Err(()),
        },
        (DoubleShow, [n, r..]) => match &*n.as_value() {
            DoubleLit(n) => Ok((
                r,
                TextLit(vec![InterpolatedTextContents::Text(n.to_string())]),
            )),
            _ => Err(()),
        },
        (TextShow, [v, r..]) => match &*v.as_value() {
            TextLit(elts) => {
                match elts.as_slice() {
                    // If there are no interpolations (invariants ensure that when there are no
                    // interpolations, there is a single Text item) in the literal.
                    [InterpolatedTextContents::Text(s)] => {
                        // Printing InterpolatedText takes care of all the escaping
                        let txt: InterpolatedText<X> = std::iter::once(
                            InterpolatedTextContents::Text(s.clone()),
                        )
                        .collect();
                        let s = txt.to_string();
                        Ok((
                            r,
                            TextLit(vec![InterpolatedTextContents::Text(s)]),
                        ))
                    }
                    _ => Err(()),
                }
            }
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
                let mut kts = HashMap::new();
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
                        let mut kvs = HashMap::new();
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
    let expr: ExprF<Thunk, X> =
        expr.as_ref().map_ref_with_special_handling_of_binders(
            |e| Thunk::new(ctx.clone(), e.clone()),
            |x, e| Thunk::new(ctx.skip(x), e.clone()),
            |_| unreachable!(),
        );

    normalize_one_layer(expr)
}

// Small helper enum to avoid repetition
enum Ret<'a> {
    RetValue(Value),
    RetThunk(Thunk),
    RetThunkRef(&'a Thunk),
    RetExpr(ExprF<Thunk, X>),
}

fn merge_maps<K, V>(
    map1: &HashMap<K, V>,
    map2: &HashMap<K, V>,
    mut f: impl FnMut(&V, &V) -> V,
) -> HashMap<K, V>
where
    K: std::hash::Hash + Eq + Clone,
    V: Clone,
{
    let mut kvs = HashMap::new();
    for (x, v2) in map2 {
        let newv = if let Some(v1) = map1.get(x) {
            f(v1, v2)
        } else {
            v2.clone()
        };
        kvs.insert(x.clone(), newv);
    }
    for (x, v1) in map1 {
        // Insert only if key not already present
        kvs.entry(x.clone()).or_insert_with(|| v1.clone());
    }
    kvs
}

fn apply_binop<'a>(o: BinOp, x: &'a Thunk, y: &'a Thunk) -> Option<Ret<'a>> {
    use BinOp::{
        BoolAnd, BoolEQ, BoolNE, BoolOr, ListAppend, NaturalPlus, NaturalTimes,
        RecursiveRecordMerge, RecursiveRecordTypeMerge, RightBiasedRecordMerge,
        TextAppend,
    };
    use Ret::{RetThunkRef, RetValue};
    use Value::{
        BoolLit, EmptyListLit, NEListLit, NaturalLit, RecordLit, RecordType,
        TextLit,
    };
    let x_borrow = x.as_value();
    let y_borrow = y.as_value();
    Some(match (o, &*x_borrow, &*y_borrow) {
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
        (ListAppend, NEListLit(xs), NEListLit(ys)) => {
            RetValue(NEListLit(xs.iter().chain(ys.iter()).cloned().collect()))
        }

        (TextAppend, TextLit(x), _) if x.is_empty() => RetThunkRef(y),
        (TextAppend, _, TextLit(y)) if y.is_empty() => RetThunkRef(x),
        (TextAppend, TextLit(x), TextLit(y)) => {
            RetValue(TextLit(squash_textlit(x.iter().chain(y.iter()).cloned())))
        }
        (TextAppend, TextLit(x), _) => {
            use std::iter::once;
            let y = InterpolatedTextContents::Expr(y.clone());
            RetValue(TextLit(squash_textlit(x.iter().cloned().chain(once(y)))))
        }
        (TextAppend, _, TextLit(y)) => {
            use std::iter::once;
            let x = InterpolatedTextContents::Expr(x.clone());
            RetValue(TextLit(squash_textlit(once(x).chain(y.iter().cloned()))))
        }

        (RightBiasedRecordMerge, _, RecordLit(kvs)) if kvs.is_empty() => {
            RetThunkRef(x)
        }
        (RightBiasedRecordMerge, RecordLit(kvs), _) if kvs.is_empty() => {
            RetThunkRef(y)
        }
        (RightBiasedRecordMerge, RecordLit(kvs1), RecordLit(kvs2)) => {
            let mut kvs = kvs2.clone();
            for (x, v) in kvs1 {
                // Insert only if key not already present
                kvs.entry(x.clone()).or_insert_with(|| v.clone());
            }
            RetValue(RecordLit(kvs))
        }

        (RecursiveRecordMerge, _, RecordLit(kvs)) if kvs.is_empty() => {
            RetThunkRef(x)
        }
        (RecursiveRecordMerge, RecordLit(kvs), _) if kvs.is_empty() => {
            RetThunkRef(y)
        }
        (RecursiveRecordMerge, RecordLit(kvs1), RecordLit(kvs2)) => {
            let kvs = merge_maps(kvs1, kvs2, |v1, v2| {
                Thunk::from_partial_expr(ExprF::BinOp(
                    RecursiveRecordMerge,
                    v1.clone(),
                    v2.clone(),
                ))
            });
            RetValue(RecordLit(kvs))
        }

        (RecursiveRecordTypeMerge, _, RecordType(kvs)) if kvs.is_empty() => {
            RetThunkRef(x)
        }
        (RecursiveRecordTypeMerge, RecordType(kvs), _) if kvs.is_empty() => {
            RetThunkRef(y)
        }
        (RecursiveRecordTypeMerge, RecordType(kvs1), RecordType(kvs2)) => {
            let kvs = merge_maps(kvs1, kvs2, |v1, v2| {
                TypeThunk::from_thunk(Thunk::from_partial_expr(ExprF::BinOp(
                    RecursiveRecordTypeMerge,
                    v1.to_thunk(),
                    v2.to_thunk(),
                )))
            });
            RetValue(RecordType(kvs))
        }

        _ => return None,
    })
}

pub(crate) fn normalize_one_layer(expr: ExprF<Thunk, X>) -> Value {
    use Ret::{RetExpr, RetThunk, RetThunkRef, RetValue};
    use Value::{
        BoolLit, DoubleLit, EmptyListLit, EmptyOptionalLit, IntegerLit, Lam,
        NEListLit, NEOptionalLit, NaturalLit, Pi, RecordLit, RecordType,
        TextLit, UnionConstructor, UnionLit, UnionType,
    };

    let ret = match expr {
        ExprF::Embed(_) => unreachable!(),
        ExprF::Var(_) => unreachable!(),
        ExprF::Annot(x, _) => RetThunk(x),
        ExprF::Lam(x, t, e) => {
            RetValue(Lam(x.into(), TypeThunk::from_thunk(t), e))
        }
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
        ExprF::DoubleLit(n) => RetValue(DoubleLit(n)),
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
        ExprF::BinOp(o, ref x, ref y) => match apply_binop(o, x, y) {
            Some(ret) => ret,
            None => RetExpr(expr),
        },

        ExprF::Projection(_, ls) if ls.is_empty() => {
            RetValue(RecordLit(HashMap::new()))
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
