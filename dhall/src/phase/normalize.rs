use std::collections::HashMap;

use dhall_syntax::{
    BinOp, Builtin, ExprF, InterpolatedText, InterpolatedTextContents, Label,
    NaiveDouble,
};

use crate::core::value::{Value, VoVF};
use crate::core::valuef::ValueF;
use crate::core::var::{Shift, Subst};
use crate::phase::Normalized;

// Small helper enum to avoid repetition
enum Ret<'a> {
    ValueF(ValueF),
    Value(Value),
    ValueRef(&'a Value),
    Expr(ExprF<Value, Normalized>),
}

impl<'a> Ret<'a> {
    fn into_vovf_whnf(self) -> VoVF {
        match self {
            Ret::ValueF(v) => v.into_vovf_whnf(),
            Ret::Value(v) => v.into_vovf(),
            Ret::ValueRef(v) => v.clone().into_vovf(),
            Ret::Expr(expr) => ValueF::PartialExpr(expr).into_vovf_whnf(),
        }
    }
}

// Ad-hoc macro to help construct closures
macro_rules! make_closure {
    (#$var:ident) => { $var.clone() };
    (var($var:ident, $n:expr)) => {{
        let var = crate::core::var::AlphaVar::from_var_and_alpha(
            Label::from(stringify!($var)).into(),
            $n
        );
        ValueF::Var(var).into_value_untyped()
    }};
    // Warning: assumes that $ty, as a dhall value, has type `Type`
    (λ($var:ident : $($ty:tt)*) -> $($rest:tt)*) => {
        ValueF::Lam(
            Label::from(stringify!($var)).into(),
            make_closure!($($ty)*),
            make_closure!($($rest)*),
        ).into_value_untyped()
    };
    (Natural) => {
        Value::from_builtin(Builtin::Natural)
    };
    (List $($rest:tt)*) => {
        Value::from_builtin(Builtin::List)
            .app(make_closure!($($rest)*))
    };
    (Some($($rest:tt)*)) => {
        ValueF::NEOptionalLit(make_closure!($($rest)*))
            .into_value_untyped()
    };
    (1 + $($rest:tt)*) => {
        ValueF::PartialExpr(ExprF::BinOp(
            dhall_syntax::BinOp::NaturalPlus,
            make_closure!($($rest)*),
            Value::from_valuef_and_type(
                ValueF::NaturalLit(1),
                make_closure!(Natural)
            ),
        )).into_value_with_type(
            make_closure!(Natural)
        )
    };
    ([ $($head:tt)* ] # $($tail:tt)*) => {
        ValueF::PartialExpr(ExprF::BinOp(
            dhall_syntax::BinOp::ListAppend,
            ValueF::NEListLit(vec![make_closure!($($head)*)])
                .into_value_untyped(),
            make_closure!($($tail)*),
        )).into_value_untyped()
    };
}

#[allow(clippy::cognitive_complexity)]
pub(crate) fn apply_builtin(b: Builtin, args: Vec<Value>) -> VoVF {
    use dhall_syntax::Builtin::*;
    use ValueF::*;

    // Return Ok((unconsumed args, returned value)), or Err(()) if value could not be produced.
    let ret = match (b, args.as_slice()) {
        (OptionalNone, [t, r..]) => {
            Ok((r, Ret::ValueF(EmptyOptionalLit(t.clone()))))
        }
        (NaturalIsZero, [n, r..]) => match &*n.as_whnf() {
            NaturalLit(n) => Ok((r, Ret::ValueF(BoolLit(*n == 0)))),
            _ => Err(()),
        },
        (NaturalEven, [n, r..]) => match &*n.as_whnf() {
            NaturalLit(n) => Ok((r, Ret::ValueF(BoolLit(*n % 2 == 0)))),
            _ => Err(()),
        },
        (NaturalOdd, [n, r..]) => match &*n.as_whnf() {
            NaturalLit(n) => Ok((r, Ret::ValueF(BoolLit(*n % 2 != 0)))),
            _ => Err(()),
        },
        (NaturalToInteger, [n, r..]) => match &*n.as_whnf() {
            NaturalLit(n) => Ok((r, Ret::ValueF(IntegerLit(*n as isize)))),
            _ => Err(()),
        },
        (NaturalShow, [n, r..]) => match &*n.as_whnf() {
            NaturalLit(n) => Ok((
                r,
                Ret::ValueF(TextLit(vec![InterpolatedTextContents::Text(
                    n.to_string(),
                )])),
            )),
            _ => Err(()),
        },
        (NaturalSubtract, [a, b, r..]) => {
            match (&*a.as_whnf(), &*b.as_whnf()) {
                (NaturalLit(a), NaturalLit(b)) => Ok((
                    r,
                    Ret::ValueF(NaturalLit(if b > a { b - a } else { 0 })),
                )),
                (NaturalLit(0), _) => Ok((r, Ret::ValueRef(b))),
                (_, NaturalLit(0)) => Ok((r, Ret::ValueF(NaturalLit(0)))),
                _ if a == b => Ok((r, Ret::ValueF(NaturalLit(0)))),
                _ => Err(()),
            }
        }
        (IntegerShow, [n, r..]) => match &*n.as_whnf() {
            IntegerLit(n) => {
                let s = if *n < 0 {
                    n.to_string()
                } else {
                    format!("+{}", n)
                };
                Ok((
                    r,
                    Ret::ValueF(TextLit(vec![InterpolatedTextContents::Text(
                        s,
                    )])),
                ))
            }
            _ => Err(()),
        },
        (IntegerToDouble, [n, r..]) => match &*n.as_whnf() {
            IntegerLit(n) => {
                Ok((r, Ret::ValueF(DoubleLit(NaiveDouble::from(*n as f64)))))
            }
            _ => Err(()),
        },
        (DoubleShow, [n, r..]) => match &*n.as_whnf() {
            DoubleLit(n) => Ok((
                r,
                Ret::ValueF(TextLit(vec![InterpolatedTextContents::Text(
                    n.to_string(),
                )])),
            )),
            _ => Err(()),
        },
        (TextShow, [v, r..]) => match &*v.as_whnf() {
            TextLit(elts) => {
                match elts.as_slice() {
                    // Empty string literal.
                    [] => {
                        // Printing InterpolatedText takes care of all the escaping
                        let txt: InterpolatedText<Normalized> =
                            std::iter::empty().collect();
                        let s = txt.to_string();
                        Ok((
                            r,
                            Ret::ValueF(TextLit(vec![
                                InterpolatedTextContents::Text(s),
                            ])),
                        ))
                    }
                    // If there are no interpolations (invariants ensure that when there are no
                    // interpolations, there is a single Text item) in the literal.
                    [InterpolatedTextContents::Text(s)] => {
                        // Printing InterpolatedText takes care of all the escaping
                        let txt: InterpolatedText<Normalized> =
                            std::iter::once(InterpolatedTextContents::Text(
                                s.clone(),
                            ))
                            .collect();
                        let s = txt.to_string();
                        Ok((
                            r,
                            Ret::ValueF(TextLit(vec![
                                InterpolatedTextContents::Text(s),
                            ])),
                        ))
                    }
                    _ => Err(()),
                }
            }
            _ => Err(()),
        },
        (ListLength, [_, l, r..]) => match &*l.as_whnf() {
            EmptyListLit(_) => Ok((r, Ret::ValueF(NaturalLit(0)))),
            NEListLit(xs) => Ok((r, Ret::ValueF(NaturalLit(xs.len())))),
            _ => Err(()),
        },
        (ListHead, [_, l, r..]) => match &*l.as_whnf() {
            EmptyListLit(n) => {
                Ok((r, Ret::ValueF(EmptyOptionalLit(n.clone()))))
            }
            NEListLit(xs) => Ok((
                r,
                Ret::ValueF(NEOptionalLit(xs.iter().next().unwrap().clone())),
            )),
            _ => Err(()),
        },
        (ListLast, [_, l, r..]) => match &*l.as_whnf() {
            EmptyListLit(n) => {
                Ok((r, Ret::ValueF(EmptyOptionalLit(n.clone()))))
            }
            NEListLit(xs) => Ok((
                r,
                Ret::ValueF(NEOptionalLit(
                    xs.iter().rev().next().unwrap().clone(),
                )),
            )),
            _ => Err(()),
        },
        (ListReverse, [_, l, r..]) => match &*l.as_whnf() {
            EmptyListLit(n) => Ok((r, Ret::ValueF(EmptyListLit(n.clone())))),
            NEListLit(xs) => Ok((
                r,
                Ret::ValueF(NEListLit(xs.iter().rev().cloned().collect())),
            )),
            _ => Err(()),
        },
        (ListIndexed, [_, l, r..]) => match &*l.as_whnf() {
            EmptyListLit(t) => {
                let mut kts = HashMap::new();
                kts.insert("index".into(), Value::from_builtin(Natural));
                kts.insert("value".into(), t.clone());
                Ok((
                    r,
                    Ret::ValueF(EmptyListLit(Value::from_valuef_untyped(
                        RecordType(kts),
                    ))),
                ))
            }
            NEListLit(xs) => {
                let xs = xs
                    .iter()
                    .enumerate()
                    .map(|(i, e)| {
                        let i = NaturalLit(i);
                        let mut kvs = HashMap::new();
                        kvs.insert(
                            "index".into(),
                            Value::from_valuef_untyped(i),
                        );
                        kvs.insert("value".into(), e.clone());
                        Value::from_valuef_untyped(RecordLit(kvs))
                    })
                    .collect();
                Ok((r, Ret::ValueF(NEListLit(xs))))
            }
            _ => Err(()),
        },
        (ListBuild, [t, f, r..]) => match &*f.as_whnf() {
            // fold/build fusion
            ValueF::AppliedBuiltin(ListFold, args) => {
                if args.len() >= 2 {
                    Ok((r, Ret::Value(args[1].clone())))
                } else {
                    // Do we really need to handle this case ?
                    unimplemented!()
                }
            }
            _ => {
                let list_t = Value::from_builtin(List).app(t.clone());
                Ok((
                    r,
                    Ret::Value(
                        f.app(list_t.clone())
                            .app({
                                // Move `t` under new `x` variable
                                let t1 = t.under_binder(Label::from("x"));
                                make_closure!(
                                    λ(x : #t) ->
                                    λ(xs : List #t1) ->
                                    [ var(x, 1) ] # var(xs, 0)
                                )
                            })
                            .app(
                                EmptyListLit(t.clone())
                                    .into_value_with_type(list_t),
                            ),
                    ),
                ))
            }
        },
        (ListFold, [_, l, _, cons, nil, r..]) => match &*l.as_whnf() {
            EmptyListLit(_) => Ok((r, Ret::ValueRef(nil))),
            NEListLit(xs) => {
                let mut v = nil.clone();
                for x in xs.iter().cloned().rev() {
                    v = cons.app(x).app(v);
                }
                Ok((r, Ret::Value(v)))
            }
            _ => Err(()),
        },
        (OptionalBuild, [t, f, r..]) => match &*f.as_whnf() {
            // fold/build fusion
            ValueF::AppliedBuiltin(OptionalFold, args) => {
                if args.len() >= 2 {
                    Ok((r, Ret::Value(args[1].clone())))
                } else {
                    // Do we really need to handle this case ?
                    unimplemented!()
                }
            }
            _ => {
                let optional_t = Value::from_builtin(Optional).app(t.clone());
                Ok((
                    r,
                    Ret::Value(
                        f.app(optional_t.clone())
                            .app(make_closure!(λ(x: #t) -> Some(var(x, 0))))
                            .app(
                                EmptyOptionalLit(t.clone())
                                    .into_value_with_type(optional_t),
                            ),
                    ),
                ))
            }
        },
        (OptionalFold, [_, v, _, just, nothing, r..]) => match &*v.as_whnf() {
            EmptyOptionalLit(_) => Ok((r, Ret::ValueRef(nothing))),
            NEOptionalLit(x) => Ok((r, Ret::Value(just.app(x.clone())))),
            _ => Err(()),
        },
        (NaturalBuild, [f, r..]) => match &*f.as_whnf() {
            // fold/build fusion
            ValueF::AppliedBuiltin(NaturalFold, args) => {
                if !args.is_empty() {
                    Ok((r, Ret::Value(args[0].clone())))
                } else {
                    // Do we really need to handle this case ?
                    unimplemented!()
                }
            }
            _ => Ok((
                r,
                Ret::Value(
                    f.app(Value::from_builtin(Natural))
                        .app(make_closure!(λ(x : Natural) -> 1 + var(x, 0)))
                        .app(NaturalLit(0).into_value_with_type(
                            Value::from_builtin(Natural),
                        )),
                ),
            )),
        },
        (NaturalFold, [n, t, succ, zero, r..]) => match &*n.as_whnf() {
            NaturalLit(0) => Ok((r, Ret::ValueRef(zero))),
            NaturalLit(n) => {
                let fold = Value::from_builtin(NaturalFold)
                    .app(
                        NaturalLit(n - 1)
                            .into_value_with_type(Value::from_builtin(Natural)),
                    )
                    .app(t.clone())
                    .app(succ.clone())
                    .app(zero.clone());
                Ok((r, Ret::Value(succ.app(fold))))
            }
            _ => Err(()),
        },
        _ => Err(()),
    };
    match ret {
        Ok((unconsumed_args, ret)) => {
            let mut v = ret.into_vovf_whnf();
            let n_consumed_args = args.len() - unconsumed_args.len();
            for x in args.into_iter().skip(n_consumed_args) {
                v = v.app(x);
            }
            v
        }
        Err(()) => AppliedBuiltin(b, args).into_vovf_whnf(),
    }
}

pub(crate) fn apply_any(f: Value, a: Value) -> VoVF {
    let fallback = |f: Value, a: Value| {
        ValueF::PartialExpr(ExprF::App(f, a)).into_vovf_whnf()
    };

    let f_borrow = f.as_whnf();
    match &*f_borrow {
        ValueF::Lam(x, _, e) => e.subst_shift(&x.into(), &a).into_vovf(),
        ValueF::AppliedBuiltin(b, args) => {
            use std::iter::once;
            let args = args.iter().cloned().chain(once(a.clone())).collect();
            apply_builtin(*b, args)
        }
        ValueF::UnionConstructor(l, kts) => {
            ValueF::UnionLit(l.clone(), a, kts.clone()).into_vovf_whnf()
        }
        _ => {
            drop(f_borrow);
            fallback(f, a)
        }
    }
}

pub(crate) fn squash_textlit(
    elts: impl Iterator<Item = InterpolatedTextContents<Value>>,
) -> Vec<InterpolatedTextContents<Value>> {
    use std::mem::replace;
    use InterpolatedTextContents::{Expr, Text};

    fn inner(
        elts: impl Iterator<Item = InterpolatedTextContents<Value>>,
        crnt_str: &mut String,
        ret: &mut Vec<InterpolatedTextContents<Value>>,
    ) {
        for contents in elts {
            match contents {
                Text(s) => crnt_str.push_str(&s),
                Expr(e) => {
                    let e_borrow = e.as_whnf();
                    match &*e_borrow {
                        ValueF::TextLit(elts2) => {
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

pub(crate) fn merge_maps<K, V, F, Err>(
    map1: &HashMap<K, V>,
    map2: &HashMap<K, V>,
    mut f: F,
) -> Result<HashMap<K, V>, Err>
where
    F: FnMut(&V, &V) -> Result<V, Err>,
    K: std::hash::Hash + Eq + Clone,
    V: Clone,
{
    let mut kvs = HashMap::new();
    for (x, v2) in map2 {
        let newv = if let Some(v1) = map1.get(x) {
            f(v1, v2)?
        } else {
            v2.clone()
        };
        kvs.insert(x.clone(), newv);
    }
    for (x, v1) in map1 {
        // Insert only if key not already present
        kvs.entry(x.clone()).or_insert_with(|| v1.clone());
    }
    Ok(kvs)
}

fn apply_binop<'a>(o: BinOp, x: &'a Value, y: &'a Value) -> Option<Ret<'a>> {
    use BinOp::{
        BoolAnd, BoolEQ, BoolNE, BoolOr, Equivalence, ListAppend, NaturalPlus,
        NaturalTimes, RecursiveRecordMerge, RecursiveRecordTypeMerge,
        RightBiasedRecordMerge, TextAppend,
    };
    use ValueF::{
        BoolLit, EmptyListLit, NEListLit, NaturalLit, RecordLit, TextLit,
    };
    let x_borrow = x.as_whnf();
    let y_borrow = y.as_whnf();
    Some(match (o, &*x_borrow, &*y_borrow) {
        (BoolAnd, BoolLit(true), _) => Ret::ValueRef(y),
        (BoolAnd, _, BoolLit(true)) => Ret::ValueRef(x),
        (BoolAnd, BoolLit(false), _) => Ret::ValueF(BoolLit(false)),
        (BoolAnd, _, BoolLit(false)) => Ret::ValueF(BoolLit(false)),
        (BoolAnd, _, _) if x == y => Ret::ValueRef(x),
        (BoolOr, BoolLit(true), _) => Ret::ValueF(BoolLit(true)),
        (BoolOr, _, BoolLit(true)) => Ret::ValueF(BoolLit(true)),
        (BoolOr, BoolLit(false), _) => Ret::ValueRef(y),
        (BoolOr, _, BoolLit(false)) => Ret::ValueRef(x),
        (BoolOr, _, _) if x == y => Ret::ValueRef(x),
        (BoolEQ, BoolLit(true), _) => Ret::ValueRef(y),
        (BoolEQ, _, BoolLit(true)) => Ret::ValueRef(x),
        (BoolEQ, BoolLit(x), BoolLit(y)) => Ret::ValueF(BoolLit(x == y)),
        (BoolEQ, _, _) if x == y => Ret::ValueF(BoolLit(true)),
        (BoolNE, BoolLit(false), _) => Ret::ValueRef(y),
        (BoolNE, _, BoolLit(false)) => Ret::ValueRef(x),
        (BoolNE, BoolLit(x), BoolLit(y)) => Ret::ValueF(BoolLit(x != y)),
        (BoolNE, _, _) if x == y => Ret::ValueF(BoolLit(false)),

        (NaturalPlus, NaturalLit(0), _) => Ret::ValueRef(y),
        (NaturalPlus, _, NaturalLit(0)) => Ret::ValueRef(x),
        (NaturalPlus, NaturalLit(x), NaturalLit(y)) => {
            Ret::ValueF(NaturalLit(x + y))
        }
        (NaturalTimes, NaturalLit(0), _) => Ret::ValueF(NaturalLit(0)),
        (NaturalTimes, _, NaturalLit(0)) => Ret::ValueF(NaturalLit(0)),
        (NaturalTimes, NaturalLit(1), _) => Ret::ValueRef(y),
        (NaturalTimes, _, NaturalLit(1)) => Ret::ValueRef(x),
        (NaturalTimes, NaturalLit(x), NaturalLit(y)) => {
            Ret::ValueF(NaturalLit(x * y))
        }

        (ListAppend, EmptyListLit(_), _) => Ret::ValueRef(y),
        (ListAppend, _, EmptyListLit(_)) => Ret::ValueRef(x),
        (ListAppend, NEListLit(xs), NEListLit(ys)) => Ret::ValueF(NEListLit(
            xs.iter().chain(ys.iter()).cloned().collect(),
        )),

        (TextAppend, TextLit(x), _) if x.is_empty() => Ret::ValueRef(y),
        (TextAppend, _, TextLit(y)) if y.is_empty() => Ret::ValueRef(x),
        (TextAppend, TextLit(x), TextLit(y)) => Ret::ValueF(TextLit(
            squash_textlit(x.iter().chain(y.iter()).cloned()),
        )),
        (TextAppend, TextLit(x), _) => {
            use std::iter::once;
            let y = InterpolatedTextContents::Expr(y.clone());
            Ret::ValueF(TextLit(squash_textlit(
                x.iter().cloned().chain(once(y)),
            )))
        }
        (TextAppend, _, TextLit(y)) => {
            use std::iter::once;
            let x = InterpolatedTextContents::Expr(x.clone());
            Ret::ValueF(TextLit(squash_textlit(
                once(x).chain(y.iter().cloned()),
            )))
        }

        (RightBiasedRecordMerge, _, RecordLit(kvs)) if kvs.is_empty() => {
            Ret::ValueRef(x)
        }
        (RightBiasedRecordMerge, RecordLit(kvs), _) if kvs.is_empty() => {
            Ret::ValueRef(y)
        }
        (RightBiasedRecordMerge, RecordLit(kvs1), RecordLit(kvs2)) => {
            let mut kvs = kvs2.clone();
            for (x, v) in kvs1 {
                // Insert only if key not already present
                kvs.entry(x.clone()).or_insert_with(|| v.clone());
            }
            Ret::ValueF(RecordLit(kvs))
        }

        (RecursiveRecordMerge, _, RecordLit(kvs)) if kvs.is_empty() => {
            Ret::ValueRef(x)
        }
        (RecursiveRecordMerge, RecordLit(kvs), _) if kvs.is_empty() => {
            Ret::ValueRef(y)
        }
        (RecursiveRecordMerge, RecordLit(kvs1), RecordLit(kvs2)) => {
            let kvs = merge_maps::<_, _, _, !>(kvs1, kvs2, |v1, v2| {
                Ok(Value::from_valuef_untyped(ValueF::PartialExpr(
                    ExprF::BinOp(RecursiveRecordMerge, v1.clone(), v2.clone()),
                )))
            })?;
            Ret::ValueF(RecordLit(kvs))
        }

        (RecursiveRecordTypeMerge, _, _) | (Equivalence, _, _) => {
            unreachable!("This case should have been handled in typecheck")
        }

        _ => return None,
    })
}

pub(crate) fn normalize_one_layer(expr: ExprF<Value, Normalized>) -> VoVF {
    use ValueF::{
        AppliedBuiltin, BoolLit, DoubleLit, EmptyListLit, IntegerLit,
        NEListLit, NEOptionalLit, NaturalLit, RecordLit, TextLit,
        UnionConstructor, UnionLit, UnionType,
    };

    let ret = match expr {
        ExprF::Import(_) => unreachable!(
            "There should remain no imports in a resolved expression"
        ),
        // Those cases have already been completely handled in the typechecking phase (using
        // `RetWhole`), so they won't appear here.
        ExprF::Lam(_, _, _)
        | ExprF::Pi(_, _, _)
        | ExprF::Let(_, _, _, _)
        | ExprF::Embed(_)
        | ExprF::Const(_)
        | ExprF::Builtin(_)
        | ExprF::Var(_)
        | ExprF::Annot(_, _)
        | ExprF::RecordType(_)
        | ExprF::UnionType(_) => {
            unreachable!("This case should have been handled in typecheck")
        }
        ExprF::Assert(_) => Ret::Expr(expr),
        ExprF::App(v, a) => Ret::Value(v.app(a)),
        ExprF::BoolLit(b) => Ret::ValueF(BoolLit(b)),
        ExprF::NaturalLit(n) => Ret::ValueF(NaturalLit(n)),
        ExprF::IntegerLit(n) => Ret::ValueF(IntegerLit(n)),
        ExprF::DoubleLit(n) => Ret::ValueF(DoubleLit(n)),
        ExprF::SomeLit(e) => Ret::ValueF(NEOptionalLit(e)),
        ExprF::EmptyListLit(ref t) => {
            // Check if the type is of the form `List x`
            let t_borrow = t.as_whnf();
            match &*t_borrow {
                AppliedBuiltin(Builtin::List, args) if args.len() == 1 => {
                    Ret::ValueF(EmptyListLit(args[0].clone()))
                }
                _ => {
                    drop(t_borrow);
                    Ret::Expr(expr)
                }
            }
        }
        ExprF::NEListLit(elts) => {
            Ret::ValueF(NEListLit(elts.into_iter().collect()))
        }
        ExprF::RecordLit(kvs) => {
            Ret::ValueF(RecordLit(kvs.into_iter().collect()))
        }
        ExprF::TextLit(elts) => {
            use InterpolatedTextContents::Expr;
            let elts: Vec<_> = squash_textlit(elts.into_iter());
            // Simplify bare interpolation
            if let [Expr(th)] = elts.as_slice() {
                Ret::Value(th.clone())
            } else {
                Ret::ValueF(TextLit(elts))
            }
        }
        ExprF::BoolIf(ref b, ref e1, ref e2) => {
            let b_borrow = b.as_whnf();
            match &*b_borrow {
                BoolLit(true) => Ret::ValueRef(e1),
                BoolLit(false) => Ret::ValueRef(e2),
                _ => {
                    let e1_borrow = e1.as_whnf();
                    let e2_borrow = e2.as_whnf();
                    match (&*e1_borrow, &*e2_borrow) {
                        // Simplify `if b then True else False`
                        (BoolLit(true), BoolLit(false)) => Ret::ValueRef(b),
                        _ if e1 == e2 => Ret::ValueRef(e1),
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

        ExprF::Projection(_, ref ls) if ls.is_empty() => {
            Ret::ValueF(RecordLit(HashMap::new()))
        }
        ExprF::Projection(ref v, ref ls) => {
            let v_borrow = v.as_whnf();
            match &*v_borrow {
                RecordLit(kvs) => Ret::ValueF(RecordLit(
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
            let v_borrow = v.as_whnf();
            match &*v_borrow {
                RecordLit(kvs) => match kvs.get(l) {
                    Some(r) => Ret::Value(r.clone()),
                    None => {
                        drop(v_borrow);
                        Ret::Expr(expr)
                    }
                },
                UnionType(kts) => {
                    Ret::ValueF(UnionConstructor(l.clone(), kts.clone()))
                }
                _ => {
                    drop(v_borrow);
                    Ret::Expr(expr)
                }
            }
        }

        ExprF::Merge(ref handlers, ref variant, _) => {
            let handlers_borrow = handlers.as_whnf();
            let variant_borrow = variant.as_whnf();
            match (&*handlers_borrow, &*variant_borrow) {
                (RecordLit(kvs), UnionConstructor(l, _)) => match kvs.get(l) {
                    Some(h) => Ret::Value(h.clone()),
                    None => {
                        drop(handlers_borrow);
                        drop(variant_borrow);
                        Ret::Expr(expr)
                    }
                },
                (RecordLit(kvs), UnionLit(l, v, _)) => match kvs.get(l) {
                    Some(h) => Ret::Value(h.app(v.clone())),
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

    ret.into_vovf_whnf()
}

/// Normalize a ValueF into WHNF
pub(crate) fn normalize_whnf(v: ValueF) -> VoVF {
    match v {
        ValueF::AppliedBuiltin(b, args) => apply_builtin(b, args),
        ValueF::PartialExpr(e) => normalize_one_layer(e),
        ValueF::TextLit(elts) => {
            ValueF::TextLit(squash_textlit(elts.into_iter())).into_vovf_whnf()
        }
        // All other cases are already in WHNF
        v => v.into_vovf_whnf(),
    }
}
