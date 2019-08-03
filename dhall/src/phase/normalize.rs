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

pub type InputSubExpr = ResolvedSubExpr;
pub type OutputSubExpr = NormalizedSubExpr;

#[allow(clippy::cognitive_complexity)]
pub fn apply_builtin(b: Builtin, args: Vec<Thunk>) -> Value {
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
                if !args.is_empty() {
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

pub fn apply_any(f: Thunk, a: Thunk) -> Value {
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

pub fn squash_textlit(
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
pub fn normalize_whnf(ctx: NormalizationContext, expr: InputSubExpr) -> Value {
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
    Value(Value),
    Thunk(Thunk),
    ThunkRef(&'a Thunk),
    Expr(ExprF<Thunk, X>),
}

pub(crate) fn merge_maps<K, V>(
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
    use Value::{
        BoolLit, EmptyListLit, NEListLit, NaturalLit, RecordLit, RecordType,
        TextLit,
    };
    let x_borrow = x.as_value();
    let y_borrow = y.as_value();
    Some(match (o, &*x_borrow, &*y_borrow) {
        (BoolAnd, BoolLit(true), _) => Ret::ThunkRef(y),
        (BoolAnd, _, BoolLit(true)) => Ret::ThunkRef(x),
        (BoolAnd, BoolLit(false), _) => Ret::Value(BoolLit(false)),
        (BoolAnd, _, BoolLit(false)) => Ret::Value(BoolLit(false)),
        (BoolAnd, _, _) if x == y => Ret::ThunkRef(x),
        (BoolOr, BoolLit(true), _) => Ret::Value(BoolLit(true)),
        (BoolOr, _, BoolLit(true)) => Ret::Value(BoolLit(true)),
        (BoolOr, BoolLit(false), _) => Ret::ThunkRef(y),
        (BoolOr, _, BoolLit(false)) => Ret::ThunkRef(x),
        (BoolOr, _, _) if x == y => Ret::ThunkRef(x),
        (BoolEQ, BoolLit(true), _) => Ret::ThunkRef(y),
        (BoolEQ, _, BoolLit(true)) => Ret::ThunkRef(x),
        (BoolEQ, BoolLit(x), BoolLit(y)) => Ret::Value(BoolLit(x == y)),
        (BoolEQ, _, _) if x == y => Ret::Value(BoolLit(true)),
        (BoolNE, BoolLit(false), _) => Ret::ThunkRef(y),
        (BoolNE, _, BoolLit(false)) => Ret::ThunkRef(x),
        (BoolNE, BoolLit(x), BoolLit(y)) => Ret::Value(BoolLit(x != y)),
        (BoolNE, _, _) if x == y => Ret::Value(BoolLit(false)),

        (NaturalPlus, NaturalLit(0), _) => Ret::ThunkRef(y),
        (NaturalPlus, _, NaturalLit(0)) => Ret::ThunkRef(x),
        (NaturalPlus, NaturalLit(x), NaturalLit(y)) => {
            Ret::Value(NaturalLit(x + y))
        }
        (NaturalTimes, NaturalLit(0), _) => Ret::Value(NaturalLit(0)),
        (NaturalTimes, _, NaturalLit(0)) => Ret::Value(NaturalLit(0)),
        (NaturalTimes, NaturalLit(1), _) => Ret::ThunkRef(y),
        (NaturalTimes, _, NaturalLit(1)) => Ret::ThunkRef(x),
        (NaturalTimes, NaturalLit(x), NaturalLit(y)) => {
            Ret::Value(NaturalLit(x * y))
        }

        (ListAppend, EmptyListLit(_), _) => Ret::ThunkRef(y),
        (ListAppend, _, EmptyListLit(_)) => Ret::ThunkRef(x),
        (ListAppend, NEListLit(xs), NEListLit(ys)) => {
            Ret::Value(NEListLit(xs.iter().chain(ys.iter()).cloned().collect()))
        }

        (TextAppend, TextLit(x), _) if x.is_empty() => Ret::ThunkRef(y),
        (TextAppend, _, TextLit(y)) if y.is_empty() => Ret::ThunkRef(x),
        (TextAppend, TextLit(x), TextLit(y)) => Ret::Value(TextLit(
            squash_textlit(x.iter().chain(y.iter()).cloned()),
        )),
        (TextAppend, TextLit(x), _) => {
            use std::iter::once;
            let y = InterpolatedTextContents::Expr(y.clone());
            Ret::Value(TextLit(squash_textlit(
                x.iter().cloned().chain(once(y)),
            )))
        }
        (TextAppend, _, TextLit(y)) => {
            use std::iter::once;
            let x = InterpolatedTextContents::Expr(x.clone());
            Ret::Value(TextLit(squash_textlit(
                once(x).chain(y.iter().cloned()),
            )))
        }

        (RightBiasedRecordMerge, _, RecordLit(kvs)) if kvs.is_empty() => {
            Ret::ThunkRef(x)
        }
        (RightBiasedRecordMerge, RecordLit(kvs), _) if kvs.is_empty() => {
            Ret::ThunkRef(y)
        }
        (RightBiasedRecordMerge, RecordLit(kvs1), RecordLit(kvs2)) => {
            let mut kvs = kvs2.clone();
            for (x, v) in kvs1 {
                // Insert only if key not already present
                kvs.entry(x.clone()).or_insert_with(|| v.clone());
            }
            Ret::Value(RecordLit(kvs))
        }

        (RecursiveRecordMerge, _, RecordLit(kvs)) if kvs.is_empty() => {
            Ret::ThunkRef(x)
        }
        (RecursiveRecordMerge, RecordLit(kvs), _) if kvs.is_empty() => {
            Ret::ThunkRef(y)
        }
        (RecursiveRecordMerge, RecordLit(kvs1), RecordLit(kvs2)) => {
            let kvs = merge_maps(kvs1, kvs2, |v1, v2| {
                Thunk::from_partial_expr(ExprF::BinOp(
                    RecursiveRecordMerge,
                    v1.clone(),
                    v2.clone(),
                ))
            });
            Ret::Value(RecordLit(kvs))
        }

        (RecursiveRecordTypeMerge, _, RecordType(kvs)) if kvs.is_empty() => {
            Ret::ThunkRef(x)
        }
        (RecursiveRecordTypeMerge, RecordType(kvs), _) if kvs.is_empty() => {
            Ret::ThunkRef(y)
        }
        (RecursiveRecordTypeMerge, RecordType(kvs1), RecordType(kvs2)) => {
            let kvs = merge_maps(kvs1, kvs2, |v1, v2| {
                TypeThunk::from_thunk(Thunk::from_partial_expr(ExprF::BinOp(
                    RecursiveRecordTypeMerge,
                    v1.to_thunk(),
                    v2.to_thunk(),
                )))
            });
            Ret::Value(RecordType(kvs))
        }

        _ => return None,
    })
}

pub fn normalize_one_layer(expr: ExprF<Thunk, X>) -> Value {
    use Value::{
        BoolLit, DoubleLit, EmptyListLit, EmptyOptionalLit, IntegerLit, Lam,
        NEListLit, NEOptionalLit, NaturalLit, Pi, RecordLit, RecordType,
        TextLit, UnionConstructor, UnionLit, UnionType,
    };

    let ret = match expr {
        ExprF::Embed(_) => unreachable!(),
        ExprF::Var(_) => unreachable!(),
        ExprF::Annot(x, _) => Ret::Thunk(x),
        ExprF::Lam(x, t, e) => {
            Ret::Value(Lam(x.into(), TypeThunk::from_thunk(t), e))
        }
        ExprF::Pi(x, t, e) => Ret::Value(Pi(
            x.into(),
            TypeThunk::from_thunk(t),
            TypeThunk::from_thunk(e),
        )),
        ExprF::Let(x, _, v, b) => {
            let v = Typed::from_thunk_untyped(v);
            Ret::Thunk(b.subst_shift(&x.into(), &v))
        }
        ExprF::App(v, a) => Ret::Value(v.app_thunk(a)),
        ExprF::Builtin(b) => Ret::Value(Value::from_builtin(b)),
        ExprF::Const(c) => Ret::Value(Value::Const(c)),
        ExprF::BoolLit(b) => Ret::Value(BoolLit(b)),
        ExprF::NaturalLit(n) => Ret::Value(NaturalLit(n)),
        ExprF::IntegerLit(n) => Ret::Value(IntegerLit(n)),
        ExprF::DoubleLit(n) => Ret::Value(DoubleLit(n)),
        ExprF::OldOptionalLit(None, t) => {
            Ret::Value(EmptyOptionalLit(TypeThunk::from_thunk(t)))
        }
        ExprF::OldOptionalLit(Some(e), _) => Ret::Value(NEOptionalLit(e)),
        ExprF::SomeLit(e) => Ret::Value(NEOptionalLit(e)),
        ExprF::EmptyListLit(t) => {
            Ret::Value(EmptyListLit(TypeThunk::from_thunk(t)))
        }
        ExprF::NEListLit(elts) => {
            Ret::Value(NEListLit(elts.into_iter().collect()))
        }
        ExprF::RecordLit(kvs) => {
            Ret::Value(RecordLit(kvs.into_iter().collect()))
        }
        ExprF::RecordType(kts) => Ret::Value(RecordType(
            kts.into_iter()
                .map(|(k, t)| (k, TypeThunk::from_thunk(t)))
                .collect(),
        )),
        ExprF::UnionLit(l, x, kts) => Ret::Value(UnionLit(
            l,
            x,
            kts.into_iter()
                .map(|(k, t)| (k, t.map(|t| TypeThunk::from_thunk(t))))
                .collect(),
        )),
        ExprF::UnionType(kts) => Ret::Value(UnionType(
            kts.into_iter()
                .map(|(k, t)| (k, t.map(|t| TypeThunk::from_thunk(t))))
                .collect(),
        )),
        ExprF::TextLit(elts) => {
            use InterpolatedTextContents::Expr;
            let elts: Vec<_> = squash_textlit(elts.into_iter());
            // Simplify bare interpolation
            if let [Expr(th)] = elts.as_slice() {
                Ret::Thunk(th.clone())
            } else {
                Ret::Value(TextLit(elts))
            }
        }
        ExprF::BoolIf(ref b, ref e1, ref e2) => {
            let b_borrow = b.as_value();
            match &*b_borrow {
                BoolLit(true) => Ret::ThunkRef(e1),
                BoolLit(false) => Ret::ThunkRef(e2),
                _ => {
                    let e1_borrow = e1.as_value();
                    let e2_borrow = e2.as_value();
                    match (&*e1_borrow, &*e2_borrow) {
                        // Simplify `if b then True else False`
                        (BoolLit(true), BoolLit(false)) => Ret::ThunkRef(b),
                        _ if e1 == e2 => Ret::ThunkRef(e1),
                        _ => {
                            drop(b_borrow);
                            drop(e1_borrow);
                            drop(e2_borrow);
                            Ret::Expr(expr)
                        }
                    }
                }
            }
        }
        ExprF::BinOp(o, ref x, ref y) => match apply_binop(o, x, y) {
            Some(ret) => ret,
            None => Ret::Expr(expr),
        },

        ExprF::Projection(_, ls) if ls.is_empty() => {
            Ret::Value(RecordLit(HashMap::new()))
        }
        ExprF::Projection(ref v, ref ls) => {
            let v_borrow = v.as_value();
            match &*v_borrow {
                RecordLit(kvs) => Ret::Value(RecordLit(
                    ls.iter()
                        .filter_map(|l| {
                            kvs.get(l).map(|x| (l.clone(), x.clone()))
                        })
                        .collect(),
                )),
                _ => {
                    drop(v_borrow);
                    Ret::Expr(expr)
                }
            }
        }
        ExprF::Field(ref v, ref l) => {
            let v_borrow = v.as_value();
            match &*v_borrow {
                RecordLit(kvs) => match kvs.get(l) {
                    Some(r) => Ret::Thunk(r.clone()),
                    None => {
                        drop(v_borrow);
                        Ret::Expr(expr)
                    }
                },
                UnionType(kts) => {
                    Ret::Value(UnionConstructor(l.clone(), kts.clone()))
                }
                _ => {
                    drop(v_borrow);
                    Ret::Expr(expr)
                }
            }
        }

        ExprF::Merge(ref handlers, ref variant, _) => {
            let handlers_borrow = handlers.as_value();
            let variant_borrow = variant.as_value();
            match (&*handlers_borrow, &*variant_borrow) {
                (RecordLit(kvs), UnionConstructor(l, _)) => match kvs.get(l) {
                    Some(h) => Ret::Thunk(h.clone()),
                    None => {
                        drop(handlers_borrow);
                        drop(variant_borrow);
                        Ret::Expr(expr)
                    }
                },
                (RecordLit(kvs), UnionLit(l, v, _)) => match kvs.get(l) {
                    Some(h) => Ret::Value(h.app_thunk(v.clone())),
                    None => {
                        drop(handlers_borrow);
                        drop(variant_borrow);
                        Ret::Expr(expr)
                    }
                },
                _ => {
                    drop(handlers_borrow);
                    drop(variant_borrow);
                    Ret::Expr(expr)
                }
            }
        }
    };

    match ret {
        Ret::Value(v) => v,
        Ret::Thunk(th) => th.to_value(),
        Ret::ThunkRef(th) => th.to_value(),
        Ret::Expr(expr) => Value::PartialExpr(expr),
    }
}
