use std::collections::HashMap;
use std::convert::TryInto;

use crate::semantics::core::value::Value;
use crate::semantics::core::value::ValueKind;
use crate::semantics::core::var::{AlphaLabel, AlphaVar, Shift, Subst};
use crate::semantics::phase::Normalized;
use crate::syntax;
use crate::syntax::Const::Type;
use crate::syntax::{
    BinOp, Builtin, ExprKind, InterpolatedText, InterpolatedTextContents,
    Label, NaiveDouble,
};

// Ad-hoc macro to help construct closures
macro_rules! make_closure {
    (#$var:ident) => { $var.clone() };
    (var($var:ident, $n:expr, $($ty:tt)*)) => {{
        let var = AlphaVar::from_var_and_alpha(
            Label::from(stringify!($var)).into(),
            $n
        );
        ValueKind::Var(var)
            .into_value_with_type(make_closure!($($ty)*))
    }};
    // Warning: assumes that $ty, as a dhall value, has type `Type`
    (λ($var:ident : $($ty:tt)*) -> $($body:tt)*) => {{
        let var: AlphaLabel = Label::from(stringify!($var)).into();
        let ty = make_closure!($($ty)*);
        let body = make_closure!($($body)*);
        let body_ty = body.get_type_not_sort();
        let lam_ty = ValueKind::Pi(var.clone(), ty.clone(), body_ty)
            .into_value_with_type(Value::from_const(Type));
        ValueKind::Lam(var, ty, body).into_value_with_type(lam_ty)
    }};
    (Natural) => {
        Value::from_builtin(Builtin::Natural)
    };
    (List $($rest:tt)*) => {
        Value::from_builtin(Builtin::List)
            .app(make_closure!($($rest)*))
    };
    (Some($($rest:tt)*)) => {{
        let v = make_closure!($($rest)*);
        let v_type = v.get_type_not_sort();
        let opt_v_type = Value::from_builtin(Builtin::Optional).app(v_type);
        ValueKind::NEOptionalLit(v).into_value_with_type(opt_v_type)
    }};
    (1 + $($rest:tt)*) => {
        ValueKind::PartialExpr(ExprKind::BinOp(
            syntax::BinOp::NaturalPlus,
            make_closure!($($rest)*),
            Value::from_kind_and_type(
                ValueKind::NaturalLit(1),
                make_closure!(Natural)
            ),
        )).into_value_with_type(
            make_closure!(Natural)
        )
    };
    ([ $($head:tt)* ] # $($tail:tt)*) => {{
        let head = make_closure!($($head)*);
        let tail = make_closure!($($tail)*);
        let list_type = tail.get_type_not_sort();
        ValueKind::PartialExpr(ExprKind::BinOp(
            syntax::BinOp::ListAppend,
            ValueKind::NEListLit(vec![head])
                .into_value_with_type(list_type.clone()),
            tail,
        )).into_value_with_type(list_type)
    }};
}

#[allow(clippy::cognitive_complexity)]
pub(crate) fn apply_builtin(
    b: Builtin,
    args: Vec<Value>,
    ty: &Value,
) -> ValueKind {
    use syntax::Builtin::*;
    use ValueKind::*;

    // Small helper enum
    enum Ret<'a> {
        ValueKind(ValueKind),
        Value(Value),
        // For applications that can return a function, it's important to keep the remaining
        // arguments to apply them to the resulting function.
        ValueWithRemainingArgs(&'a [Value], Value),
        DoneAsIs,
    }

    let ret = match (b, args.as_slice()) {
        (OptionalNone, [t]) => Ret::ValueKind(EmptyOptionalLit(t.clone())),
        (NaturalIsZero, [n]) => match &*n.as_whnf() {
            NaturalLit(n) => Ret::ValueKind(BoolLit(*n == 0)),
            _ => Ret::DoneAsIs,
        },
        (NaturalEven, [n]) => match &*n.as_whnf() {
            NaturalLit(n) => Ret::ValueKind(BoolLit(*n % 2 == 0)),
            _ => Ret::DoneAsIs,
        },
        (NaturalOdd, [n]) => match &*n.as_whnf() {
            NaturalLit(n) => Ret::ValueKind(BoolLit(*n % 2 != 0)),
            _ => Ret::DoneAsIs,
        },
        (NaturalToInteger, [n]) => match &*n.as_whnf() {
            NaturalLit(n) => Ret::ValueKind(IntegerLit(*n as isize)),
            _ => Ret::DoneAsIs,
        },
        (NaturalShow, [n]) => {
            match &*n.as_whnf() {
                NaturalLit(n) => Ret::ValueKind(TextLit(vec![
                    InterpolatedTextContents::Text(n.to_string()),
                ])),
                _ => Ret::DoneAsIs,
            }
        }
        (NaturalSubtract, [a, b]) => match (&*a.as_whnf(), &*b.as_whnf()) {
            (NaturalLit(a), NaturalLit(b)) => {
                Ret::ValueKind(NaturalLit(if b > a { b - a } else { 0 }))
            }
            (NaturalLit(0), _) => Ret::Value(b.clone()),
            (_, NaturalLit(0)) => Ret::ValueKind(NaturalLit(0)),
            _ if a == b => Ret::ValueKind(NaturalLit(0)),
            _ => Ret::DoneAsIs,
        },
        (IntegerShow, [n]) => match &*n.as_whnf() {
            IntegerLit(n) => {
                let s = if *n < 0 {
                    n.to_string()
                } else {
                    format!("+{}", n)
                };
                Ret::ValueKind(TextLit(vec![InterpolatedTextContents::Text(s)]))
            }
            _ => Ret::DoneAsIs,
        },
        (IntegerToDouble, [n]) => match &*n.as_whnf() {
            IntegerLit(n) => {
                Ret::ValueKind(DoubleLit(NaiveDouble::from(*n as f64)))
            }
            _ => Ret::DoneAsIs,
        },
        (IntegerNegate, [n]) => match &*n.as_whnf() {
            IntegerLit(n) => Ret::ValueKind(IntegerLit(-n)),
            _ => Ret::DoneAsIs,
        },
        (IntegerClamp, [n]) => match &*n.as_whnf() {
            IntegerLit(n) => {
                Ret::ValueKind(NaturalLit((*n).try_into().unwrap_or(0)))
            }
            _ => Ret::DoneAsIs,
        },
        (DoubleShow, [n]) => {
            match &*n.as_whnf() {
                DoubleLit(n) => Ret::ValueKind(TextLit(vec![
                    InterpolatedTextContents::Text(n.to_string()),
                ])),
                _ => Ret::DoneAsIs,
            }
        }
        (TextShow, [v]) => match &*v.as_whnf() {
            TextLit(elts) => {
                match elts.as_slice() {
                    // Empty string literal.
                    [] => {
                        // Printing InterpolatedText takes care of all the escaping
                        let txt: InterpolatedText<Normalized> =
                            std::iter::empty().collect();
                        let s = txt.to_string();
                        Ret::ValueKind(TextLit(vec![
                            InterpolatedTextContents::Text(s),
                        ]))
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
                        Ret::ValueKind(TextLit(vec![
                            InterpolatedTextContents::Text(s),
                        ]))
                    }
                    _ => Ret::DoneAsIs,
                }
            }
            _ => Ret::DoneAsIs,
        },
        (ListLength, [_, l]) => match &*l.as_whnf() {
            EmptyListLit(_) => Ret::ValueKind(NaturalLit(0)),
            NEListLit(xs) => Ret::ValueKind(NaturalLit(xs.len())),
            _ => Ret::DoneAsIs,
        },
        (ListHead, [_, l]) => match &*l.as_whnf() {
            EmptyListLit(n) => Ret::ValueKind(EmptyOptionalLit(n.clone())),
            NEListLit(xs) => {
                Ret::ValueKind(NEOptionalLit(xs.iter().next().unwrap().clone()))
            }
            _ => Ret::DoneAsIs,
        },
        (ListLast, [_, l]) => match &*l.as_whnf() {
            EmptyListLit(n) => Ret::ValueKind(EmptyOptionalLit(n.clone())),
            NEListLit(xs) => Ret::ValueKind(NEOptionalLit(
                xs.iter().rev().next().unwrap().clone(),
            )),
            _ => Ret::DoneAsIs,
        },
        (ListReverse, [_, l]) => match &*l.as_whnf() {
            EmptyListLit(n) => Ret::ValueKind(EmptyListLit(n.clone())),
            NEListLit(xs) => {
                Ret::ValueKind(NEListLit(xs.iter().rev().cloned().collect()))
            }
            _ => Ret::DoneAsIs,
        },
        (ListIndexed, [_, l]) => {
            let l_whnf = l.as_whnf();
            match &*l_whnf {
                EmptyListLit(_) | NEListLit(_) => {
                    // Extract the type of the list elements
                    let t = match &*l_whnf {
                        EmptyListLit(t) => t.clone(),
                        NEListLit(xs) => xs[0].get_type_not_sort(),
                        _ => unreachable!(),
                    };

                    // Construct the returned record type: { index: Natural, value: t }
                    let mut kts = HashMap::new();
                    kts.insert("index".into(), Value::from_builtin(Natural));
                    kts.insert("value".into(), t.clone());
                    let t = Value::from_kind_and_type(
                        RecordType(kts),
                        Value::from_const(Type),
                    );

                    // Construct the new list, with added indices
                    let list = match &*l_whnf {
                        EmptyListLit(_) => EmptyListLit(t),
                        NEListLit(xs) => NEListLit(
                            xs.iter()
                                .enumerate()
                                .map(|(i, e)| {
                                    let mut kvs = HashMap::new();
                                    kvs.insert(
                                        "index".into(),
                                        Value::from_kind_and_type(
                                            NaturalLit(i),
                                            Value::from_builtin(
                                                Builtin::Natural,
                                            ),
                                        ),
                                    );
                                    kvs.insert("value".into(), e.clone());
                                    Value::from_kind_and_type(
                                        RecordLit(kvs),
                                        t.clone(),
                                    )
                                })
                                .collect(),
                        ),
                        _ => unreachable!(),
                    };
                    Ret::ValueKind(list)
                }
                _ => Ret::DoneAsIs,
            }
        }
        (ListBuild, [t, f]) => {
            let list_t = Value::from_builtin(List).app(t.clone());
            Ret::Value(
                f.app(list_t.clone())
                    .app({
                        // Move `t` under new variables
                        let t1 = t.under_binder(Label::from("x"));
                        let t2 = t1.under_binder(Label::from("xs"));
                        make_closure!(
                            λ(x : #t) ->
                            λ(xs : List #t1) ->
                            [ var(x, 1, #t2) ] # var(xs, 0, List #t2)
                        )
                    })
                    .app(EmptyListLit(t.clone()).into_value_with_type(list_t)),
            )
        }
        (ListFold, [_, l, _, cons, nil, r @ ..]) => match &*l.as_whnf() {
            EmptyListLit(_) => Ret::ValueWithRemainingArgs(r, nil.clone()),
            NEListLit(xs) => {
                let mut v = nil.clone();
                for x in xs.iter().cloned().rev() {
                    v = cons.app(x).app(v);
                }
                Ret::ValueWithRemainingArgs(r, v)
            }
            _ => Ret::DoneAsIs,
        },
        (OptionalBuild, [t, f]) => {
            let optional_t = Value::from_builtin(Optional).app(t.clone());
            Ret::Value(
                f.app(optional_t.clone())
                    .app({
                        let t1 = t.under_binder(Label::from("x"));
                        make_closure!(λ(x: #t) -> Some(var(x, 0, #t1)))
                    })
                    .app(
                        EmptyOptionalLit(t.clone())
                            .into_value_with_type(optional_t),
                    ),
            )
        }
        (OptionalFold, [_, v, _, just, nothing, r @ ..]) => match &*v.as_whnf()
        {
            EmptyOptionalLit(_) => {
                Ret::ValueWithRemainingArgs(r, nothing.clone())
            }
            NEOptionalLit(x) => {
                Ret::ValueWithRemainingArgs(r, just.app(x.clone()))
            }
            _ => Ret::DoneAsIs,
        },
        (NaturalBuild, [f]) => Ret::Value(
            f.app(Value::from_builtin(Natural))
                .app(make_closure!(
                    λ(x : Natural) -> 1 + var(x, 0, Natural)
                ))
                .app(
                    NaturalLit(0)
                        .into_value_with_type(Value::from_builtin(Natural)),
                ),
        ),

        (NaturalFold, [n, t, succ, zero, r @ ..]) => match &*n.as_whnf() {
            NaturalLit(0) => Ret::ValueWithRemainingArgs(r, zero.clone()),
            NaturalLit(n) => {
                let fold = Value::from_builtin(NaturalFold)
                    .app(
                        NaturalLit(n - 1)
                            .into_value_with_type(Value::from_builtin(Natural)),
                    )
                    .app(t.clone())
                    .app(succ.clone())
                    .app(zero.clone());
                Ret::ValueWithRemainingArgs(r, succ.app(fold))
            }
            _ => Ret::DoneAsIs,
        },
        _ => Ret::DoneAsIs,
    };
    match ret {
        Ret::ValueKind(v) => v,
        Ret::Value(v) => v.to_whnf_check_type(ty),
        Ret::ValueWithRemainingArgs(unconsumed_args, mut v) => {
            let n_consumed_args = args.len() - unconsumed_args.len();
            for x in args.into_iter().skip(n_consumed_args) {
                v = v.app(x);
            }
            v.to_whnf_check_type(ty)
        }
        Ret::DoneAsIs => AppliedBuiltin(b, args),
    }
}

pub(crate) fn apply_any(f: Value, a: Value, ty: &Value) -> ValueKind {
    let f_borrow = f.as_whnf();
    match &*f_borrow {
        ValueKind::Lam(x, _, e) => {
            e.subst_shift(&x.into(), &a).to_whnf_check_type(ty)
        }
        ValueKind::AppliedBuiltin(b, args) => {
            use std::iter::once;
            let args = args.iter().cloned().chain(once(a.clone())).collect();
            apply_builtin(*b, args, ty)
        }
        ValueKind::UnionConstructor(l, kts) => {
            ValueKind::UnionLit(l.clone(), a, kts.clone())
        }
        _ => {
            drop(f_borrow);
            ValueKind::PartialExpr(ExprKind::App(f, a))
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
                        ValueKind::TextLit(elts2) => {
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
    F: FnMut(&K, &V, &V) -> Result<V, Err>,
    K: std::hash::Hash + Eq + Clone,
    V: Clone,
{
    let mut kvs = HashMap::new();
    for (x, v2) in map2 {
        let newv = if let Some(v1) = map1.get(x) {
            f(x, v1, v2)?
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

// Small helper enum to avoid repetition
enum Ret<'a> {
    ValueKind(ValueKind),
    Value(Value),
    ValueRef(&'a Value),
    Expr(ExprKind<Value, Normalized>),
}

fn apply_binop<'a>(
    o: BinOp,
    x: &'a Value,
    y: &'a Value,
    ty: &Value,
) -> Option<Ret<'a>> {
    use BinOp::{
        BoolAnd, BoolEQ, BoolNE, BoolOr, Equivalence, ListAppend, NaturalPlus,
        NaturalTimes, RecursiveRecordMerge, RecursiveRecordTypeMerge,
        RightBiasedRecordMerge, TextAppend,
    };
    use ValueKind::{
        BoolLit, EmptyListLit, NEListLit, NaturalLit, RecordLit, RecordType,
        TextLit,
    };
    let x_borrow = x.as_whnf();
    let y_borrow = y.as_whnf();
    Some(match (o, &*x_borrow, &*y_borrow) {
        (BoolAnd, BoolLit(true), _) => Ret::ValueRef(y),
        (BoolAnd, _, BoolLit(true)) => Ret::ValueRef(x),
        (BoolAnd, BoolLit(false), _) => Ret::ValueKind(BoolLit(false)),
        (BoolAnd, _, BoolLit(false)) => Ret::ValueKind(BoolLit(false)),
        (BoolAnd, _, _) if x == y => Ret::ValueRef(x),
        (BoolOr, BoolLit(true), _) => Ret::ValueKind(BoolLit(true)),
        (BoolOr, _, BoolLit(true)) => Ret::ValueKind(BoolLit(true)),
        (BoolOr, BoolLit(false), _) => Ret::ValueRef(y),
        (BoolOr, _, BoolLit(false)) => Ret::ValueRef(x),
        (BoolOr, _, _) if x == y => Ret::ValueRef(x),
        (BoolEQ, BoolLit(true), _) => Ret::ValueRef(y),
        (BoolEQ, _, BoolLit(true)) => Ret::ValueRef(x),
        (BoolEQ, BoolLit(x), BoolLit(y)) => Ret::ValueKind(BoolLit(x == y)),
        (BoolEQ, _, _) if x == y => Ret::ValueKind(BoolLit(true)),
        (BoolNE, BoolLit(false), _) => Ret::ValueRef(y),
        (BoolNE, _, BoolLit(false)) => Ret::ValueRef(x),
        (BoolNE, BoolLit(x), BoolLit(y)) => Ret::ValueKind(BoolLit(x != y)),
        (BoolNE, _, _) if x == y => Ret::ValueKind(BoolLit(false)),

        (NaturalPlus, NaturalLit(0), _) => Ret::ValueRef(y),
        (NaturalPlus, _, NaturalLit(0)) => Ret::ValueRef(x),
        (NaturalPlus, NaturalLit(x), NaturalLit(y)) => {
            Ret::ValueKind(NaturalLit(x + y))
        }
        (NaturalTimes, NaturalLit(0), _) => Ret::ValueKind(NaturalLit(0)),
        (NaturalTimes, _, NaturalLit(0)) => Ret::ValueKind(NaturalLit(0)),
        (NaturalTimes, NaturalLit(1), _) => Ret::ValueRef(y),
        (NaturalTimes, _, NaturalLit(1)) => Ret::ValueRef(x),
        (NaturalTimes, NaturalLit(x), NaturalLit(y)) => {
            Ret::ValueKind(NaturalLit(x * y))
        }

        (ListAppend, EmptyListLit(_), _) => Ret::ValueRef(y),
        (ListAppend, _, EmptyListLit(_)) => Ret::ValueRef(x),
        (ListAppend, NEListLit(xs), NEListLit(ys)) => Ret::ValueKind(
            NEListLit(xs.iter().chain(ys.iter()).cloned().collect()),
        ),

        (TextAppend, TextLit(x), _) if x.is_empty() => Ret::ValueRef(y),
        (TextAppend, _, TextLit(y)) if y.is_empty() => Ret::ValueRef(x),
        (TextAppend, TextLit(x), TextLit(y)) => Ret::ValueKind(TextLit(
            squash_textlit(x.iter().chain(y.iter()).cloned()),
        )),
        (TextAppend, TextLit(x), _) => {
            use std::iter::once;
            let y = InterpolatedTextContents::Expr(y.clone());
            Ret::ValueKind(TextLit(squash_textlit(
                x.iter().cloned().chain(once(y)),
            )))
        }
        (TextAppend, _, TextLit(y)) => {
            use std::iter::once;
            let x = InterpolatedTextContents::Expr(x.clone());
            Ret::ValueKind(TextLit(squash_textlit(
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
            Ret::ValueKind(RecordLit(kvs))
        }

        (RecursiveRecordMerge, _, RecordLit(kvs)) if kvs.is_empty() => {
            Ret::ValueRef(x)
        }
        (RecursiveRecordMerge, RecordLit(kvs), _) if kvs.is_empty() => {
            Ret::ValueRef(y)
        }
        (RecursiveRecordMerge, RecordLit(kvs1), RecordLit(kvs2)) => {
            let ty_borrow = ty.as_whnf();
            let kts = match &*ty_borrow {
                RecordType(kts) => kts,
                _ => unreachable!("Internal type error"),
            };
            let kvs = merge_maps::<_, _, _, !>(kvs1, kvs2, |k, v1, v2| {
                Ok(Value::from_kind_and_type(
                    ValueKind::PartialExpr(ExprKind::BinOp(
                        RecursiveRecordMerge,
                        v1.clone(),
                        v2.clone(),
                    )),
                    kts.get(k).expect("Internal type error").clone(),
                ))
            })?;
            Ret::ValueKind(RecordLit(kvs))
        }

        (RecursiveRecordTypeMerge, _, _) | (Equivalence, _, _) => {
            unreachable!("This case should have been handled in typecheck")
        }

        _ => return None,
    })
}

pub(crate) fn normalize_one_layer(
    expr: ExprKind<Value, Normalized>,
    ty: &Value,
) -> ValueKind {
    use ValueKind::{
        AppliedBuiltin, BoolLit, DoubleLit, EmptyListLit, EmptyOptionalLit,
        IntegerLit, NEListLit, NEOptionalLit, NaturalLit, RecordLit, TextLit,
        UnionConstructor, UnionLit, UnionType,
    };

    let ret = match expr {
        ExprKind::Import(_) => unreachable!(
            "There should remain no imports in a resolved expression"
        ),
        // Those cases have already been completely handled in the typechecking phase (using
        // `RetWhole`), so they won't appear here.
        ExprKind::Lam(_, _, _)
        | ExprKind::Pi(_, _, _)
        | ExprKind::Let(_, _, _, _)
        | ExprKind::Embed(_)
        | ExprKind::Const(_)
        | ExprKind::Builtin(_)
        | ExprKind::Var(_)
        | ExprKind::Annot(_, _)
        | ExprKind::RecordType(_)
        | ExprKind::UnionType(_) => {
            unreachable!("This case should have been handled in typecheck")
        }
        ExprKind::Assert(_) => Ret::Expr(expr),
        ExprKind::App(v, a) => Ret::Value(v.app(a)),
        ExprKind::BoolLit(b) => Ret::ValueKind(BoolLit(b)),
        ExprKind::NaturalLit(n) => Ret::ValueKind(NaturalLit(n)),
        ExprKind::IntegerLit(n) => Ret::ValueKind(IntegerLit(n)),
        ExprKind::DoubleLit(n) => Ret::ValueKind(DoubleLit(n)),
        ExprKind::SomeLit(e) => Ret::ValueKind(NEOptionalLit(e)),
        ExprKind::EmptyListLit(ref t) => {
            // Check if the type is of the form `List x`
            let t_borrow = t.as_whnf();
            match &*t_borrow {
                AppliedBuiltin(Builtin::List, args) if args.len() == 1 => {
                    Ret::ValueKind(EmptyListLit(args[0].clone()))
                }
                _ => {
                    drop(t_borrow);
                    Ret::Expr(expr)
                }
            }
        }
        ExprKind::NEListLit(elts) => {
            Ret::ValueKind(NEListLit(elts.into_iter().collect()))
        }
        ExprKind::RecordLit(kvs) => {
            Ret::ValueKind(RecordLit(kvs.into_iter().collect()))
        }
        ExprKind::TextLit(elts) => {
            use InterpolatedTextContents::Expr;
            let elts: Vec<_> = squash_textlit(elts.into_iter());
            // Simplify bare interpolation
            if let [Expr(th)] = elts.as_slice() {
                Ret::Value(th.clone())
            } else {
                Ret::ValueKind(TextLit(elts))
            }
        }
        ExprKind::BoolIf(ref b, ref e1, ref e2) => {
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
        ExprKind::BinOp(o, ref x, ref y) => match apply_binop(o, x, y, ty) {
            Some(ret) => ret,
            None => Ret::Expr(expr),
        },

        ExprKind::Projection(_, ref ls) if ls.is_empty() => {
            Ret::ValueKind(RecordLit(HashMap::new()))
        }
        ExprKind::Projection(ref v, ref ls) => {
            let v_borrow = v.as_whnf();
            match &*v_borrow {
                RecordLit(kvs) => Ret::ValueKind(RecordLit(
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
        ExprKind::Field(ref v, ref l) => {
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
                    Ret::ValueKind(UnionConstructor(l.clone(), kts.clone()))
                }
                _ => {
                    drop(v_borrow);
                    Ret::Expr(expr)
                }
            }
        }
        ExprKind::ProjectionByExpr(_, _) => {
            unimplemented!("selection by expression")
        }
        ExprKind::Completion(_, _) => unimplemented!("record completion"),

        ExprKind::Merge(ref handlers, ref variant, _) => {
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
                (RecordLit(kvs), EmptyOptionalLit(_)) => {
                    match kvs.get(&"None".into()) {
                        Some(h) => Ret::Value(h.clone()),
                        None => {
                            drop(handlers_borrow);
                            drop(variant_borrow);
                            Ret::Expr(expr)
                        }
                    }
                }
                (RecordLit(kvs), NEOptionalLit(v)) => {
                    match kvs.get(&"Some".into()) {
                        Some(h) => Ret::Value(h.app(v.clone())),
                        None => {
                            drop(handlers_borrow);
                            drop(variant_borrow);
                            Ret::Expr(expr)
                        }
                    }
                }
                _ => {
                    drop(handlers_borrow);
                    drop(variant_borrow);
                    Ret::Expr(expr)
                }
            }
        }
        ExprKind::ToMap(_, _) => unimplemented!("toMap"),
    };

    match ret {
        Ret::ValueKind(v) => v,
        Ret::Value(v) => v.to_whnf_check_type(ty),
        Ret::ValueRef(v) => v.to_whnf_check_type(ty),
        Ret::Expr(expr) => ValueKind::PartialExpr(expr),
    }
}

/// Normalize a ValueKind into WHNF
pub(crate) fn normalize_whnf(v: ValueKind, ty: &Value) -> ValueKind {
    match v {
        ValueKind::AppliedBuiltin(b, args) => apply_builtin(b, args, ty),
        ValueKind::PartialExpr(e) => normalize_one_layer(e, ty),
        ValueKind::TextLit(elts) => {
            ValueKind::TextLit(squash_textlit(elts.into_iter()))
        }
        // All other cases are already in WHNF
        v => v,
    }
}
