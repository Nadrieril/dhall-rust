use crate::semantics::phase::Normalized;
use crate::semantics::{type_with, NzEnv, Value, ValueKind};
use crate::syntax::Const::Type;
use crate::syntax::{
    self, Builtin, Const, Expr, ExprKind, InterpolatedText,
    InterpolatedTextContents, Label, NaiveDouble, Span, UnspannedExpr, V,
};
use std::collections::HashMap;
use std::convert::TryInto;

pub(crate) fn rc<E>(x: UnspannedExpr<E>) -> Expr<E> {
    Expr::new(x, Span::Artificial)
}

// Ad-hoc macro to help construct the types of builtins
macro_rules! make_type {
    (Type) => { rc(ExprKind::Const(Const::Type)) };
    (Bool) => { rc(ExprKind::Builtin(Builtin::Bool)) };
    (Natural) => { rc(ExprKind::Builtin(Builtin::Natural)) };
    (Integer) => { rc(ExprKind::Builtin(Builtin::Integer)) };
    (Double) => { rc(ExprKind::Builtin(Builtin::Double)) };
    (Text) => { rc(ExprKind::Builtin(Builtin::Text)) };
    ($var:ident) => {
        rc(ExprKind::Var(V(stringify!($var).into(), 0)))
    };
    (Optional $ty:ident) => {
        rc(ExprKind::App(
            rc(ExprKind::Builtin(Builtin::Optional)),
            make_type!($ty)
        ))
    };
    (List $($rest:tt)*) => {
        rc(ExprKind::App(
            rc(ExprKind::Builtin(Builtin::List)),
            make_type!($($rest)*)
        ))
    };
    ({ $($label:ident : $ty:ident),* }) => {{
        let mut kts = syntax::map::DupTreeMap::new();
        $(
            kts.insert(
                Label::from(stringify!($label)),
                make_type!($ty),
            );
        )*
        rc(ExprKind::RecordType(kts))
    }};
    ($ty:ident -> $($rest:tt)*) => {
        rc(ExprKind::Pi(
            "_".into(),
            make_type!($ty),
            make_type!($($rest)*)
        ))
    };
    (($($arg:tt)*) -> $($rest:tt)*) => {
        rc(ExprKind::Pi(
            "_".into(),
            make_type!($($arg)*),
            make_type!($($rest)*)
        ))
    };
    (forall ($var:ident : $($ty:tt)*) -> $($rest:tt)*) => {
        rc(ExprKind::Pi(
            stringify!($var).into(),
            make_type!($($ty)*),
            make_type!($($rest)*)
        ))
    };
}

pub(crate) fn type_of_builtin<E>(b: Builtin) -> Expr<E> {
    use Builtin::*;
    match b {
        Bool | Natural | Integer | Double | Text => make_type!(Type),
        List | Optional => make_type!(
            Type -> Type
        ),

        NaturalFold => make_type!(
            Natural ->
            forall (natural: Type) ->
            forall (succ: natural -> natural) ->
            forall (zero: natural) ->
            natural
        ),
        NaturalBuild => make_type!(
            (forall (natural: Type) ->
                forall (succ: natural -> natural) ->
                forall (zero: natural) ->
                natural) ->
            Natural
        ),
        NaturalIsZero | NaturalEven | NaturalOdd => make_type!(
            Natural -> Bool
        ),
        NaturalToInteger => make_type!(Natural -> Integer),
        NaturalShow => make_type!(Natural -> Text),
        NaturalSubtract => make_type!(Natural -> Natural -> Natural),

        IntegerToDouble => make_type!(Integer -> Double),
        IntegerShow => make_type!(Integer -> Text),
        IntegerNegate => make_type!(Integer -> Integer),
        IntegerClamp => make_type!(Integer -> Natural),

        DoubleShow => make_type!(Double -> Text),
        TextShow => make_type!(Text -> Text),

        ListBuild => make_type!(
            forall (a: Type) ->
            (forall (list: Type) ->
                forall (cons: a -> list -> list) ->
                forall (nil: list) ->
                list) ->
            List a
        ),
        ListFold => make_type!(
            forall (a: Type) ->
            (List a) ->
            forall (list: Type) ->
            forall (cons: a -> list -> list) ->
            forall (nil: list) ->
            list
        ),
        ListLength => make_type!(forall (a: Type) -> (List a) -> Natural),
        ListHead | ListLast => {
            make_type!(forall (a: Type) -> (List a) -> Optional a)
        }
        ListIndexed => make_type!(
            forall (a: Type) ->
            (List a) ->
            List { index: Natural, value: a }
        ),
        ListReverse => make_type!(
            forall (a: Type) -> (List a) -> List a
        ),

        OptionalBuild => make_type!(
            forall (a: Type) ->
            (forall (optional: Type) ->
                forall (just: a -> optional) ->
                forall (nothing: optional) ->
                optional) ->
            Optional a
        ),
        OptionalFold => make_type!(
            forall (a: Type) ->
            (Optional a) ->
            forall (optional: Type) ->
            forall (just: a -> optional) ->
            forall (nothing: optional) ->
            optional
        ),
        OptionalNone => make_type!(
            forall (A: Type) -> Optional A
        ),
    }
}

// Ad-hoc macro to help construct closures
macro_rules! make_closure {
    (var($var:ident)) => {{
        rc(ExprKind::Var(syntax::V(
            Label::from(stringify!($var)).into(),
            0
        )))
    }};
    (λ($var:tt : $($ty:tt)*) -> $($body:tt)*) => {{
        let var = Label::from(stringify!($var));
        let ty = make_closure!($($ty)*);
        let body = make_closure!($($body)*);
        rc(ExprKind::Lam(var, ty, body))
    }};
    (Type) => {
        rc(ExprKind::Const(Type))
    };
    (Natural) => {
        rc(ExprKind::Builtin(Builtin::Natural))
    };
    (List $($ty:tt)*) => {{
        let ty = make_closure!($($ty)*);
        rc(ExprKind::App(
            rc(ExprKind::Builtin(Builtin::List)),
            ty
        ))
    }};
    (Some($($v:tt)*)) => {
        rc(ExprKind::SomeLit(
            make_closure!($($v)*)
        ))
    };
    (1 + $($v:tt)*) => {
        rc(ExprKind::BinOp(
            syntax::BinOp::NaturalPlus,
            make_closure!($($v)*),
            rc(ExprKind::NaturalLit(1))
        ))
    };
    ([ $($head:tt)* ] # $($tail:tt)*) => {{
        let head = make_closure!($($head)*);
        let tail = make_closure!($($tail)*);
        rc(ExprKind::BinOp(
            syntax::BinOp::ListAppend,
            rc(ExprKind::NEListLit(vec![head])),
            tail,
        ))
    }};
}

#[allow(clippy::cognitive_complexity)]
pub(crate) fn apply_builtin(
    b: Builtin,
    args: Vec<Value>,
    ty: &Value,
    types: Vec<Value>,
    env: NzEnv,
) -> ValueKind<Value> {
    use syntax::Builtin::*;
    use ValueKind::*;

    // Small helper enum
    enum Ret {
        ValueKind(ValueKind<Value>),
        Value(Value),
        DoneAsIs,
    }
    let make_closure = |e| {
        type_with(&env.to_alpha_tyenv(), &e)
            .unwrap()
            .normalize_whnf(&env)
    };

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
                    .app(
                        make_closure(make_closure!(
                            λ(T : Type) ->
                            λ(a : var(T)) ->
                            λ(as : List var(T)) ->
                            [ var(a) ] # var(as)
                        ))
                        .app(t.clone()),
                    )
                    .app(EmptyListLit(t.clone()).into_value_with_type(list_t)),
            )
        }
        (ListFold, [_, l, _, cons, nil]) => match &*l.as_whnf() {
            EmptyListLit(_) => Ret::Value(nil.clone()),
            NEListLit(xs) => {
                let mut v = nil.clone();
                for x in xs.iter().cloned().rev() {
                    v = cons.app(x).app(v);
                }
                Ret::Value(v)
            }
            _ => Ret::DoneAsIs,
        },
        (OptionalBuild, [t, f]) => {
            let optional_t = Value::from_builtin(Optional).app(t.clone());
            Ret::Value(
                f.app(optional_t.clone())
                    .app(
                        make_closure(make_closure!(
                            λ(T : Type) ->
                            λ(a : var(T)) ->
                            Some(var(a))
                        ))
                        .app(t.clone()),
                    )
                    .app(
                        EmptyOptionalLit(t.clone())
                            .into_value_with_type(optional_t),
                    ),
            )
        }
        (OptionalFold, [_, v, _, just, nothing]) => match &*v.as_whnf() {
            EmptyOptionalLit(_) => Ret::Value(nothing.clone()),
            NEOptionalLit(x) => Ret::Value(just.app(x.clone())),
            _ => Ret::DoneAsIs,
        },
        (NaturalBuild, [f]) => Ret::Value(
            f.app(Value::from_builtin(Natural))
                .app(make_closure(make_closure!(
                    λ(x : Natural) ->
                    1 + var(x)
                )))
                .app(
                    NaturalLit(0)
                        .into_value_with_type(Value::from_builtin(Natural)),
                ),
        ),

        (NaturalFold, [n, t, succ, zero]) => match &*n.as_whnf() {
            NaturalLit(0) => Ret::Value(zero.clone()),
            NaturalLit(n) => {
                let fold = Value::from_builtin(NaturalFold)
                    .app(
                        NaturalLit(n - 1)
                            .into_value_with_type(Value::from_builtin(Natural)),
                    )
                    .app(t.clone())
                    .app(succ.clone())
                    .app(zero.clone());
                Ret::Value(succ.app(fold))
            }
            _ => Ret::DoneAsIs,
        },
        _ => Ret::DoneAsIs,
    };
    match ret {
        Ret::ValueKind(v) => v,
        Ret::Value(v) => v.to_whnf_check_type(ty),
        Ret::DoneAsIs => AppliedBuiltin(b, args, types, env),
    }
}
