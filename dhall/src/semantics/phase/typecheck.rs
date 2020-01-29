use crate::semantics::{NzEnv, Value, ValueKind};
use crate::syntax;
use crate::syntax::{
    Builtin, Const, Expr, ExprKind, Label, Span, UnspannedExpr,
};

pub(crate) fn const_to_value(c: Const) -> Value {
    let v = ValueKind::Const(c);
    match c {
        Const::Type => {
            Value::from_kind_and_type(v, const_to_value(Const::Kind))
        }
        Const::Kind => {
            Value::from_kind_and_type(v, const_to_value(Const::Sort))
        }
        Const::Sort => Value::const_sort(),
    }
}

pub fn rc<E>(x: UnspannedExpr<E>) -> Expr<E> {
    Expr::new(x, Span::Artificial)
}

// Ad-hoc macro to help construct the types of builtins
macro_rules! make_type {
    (Type) => { ExprKind::Const(Const::Type) };
    (Bool) => { ExprKind::Builtin(Builtin::Bool) };
    (Natural) => { ExprKind::Builtin(Builtin::Natural) };
    (Integer) => { ExprKind::Builtin(Builtin::Integer) };
    (Double) => { ExprKind::Builtin(Builtin::Double) };
    (Text) => { ExprKind::Builtin(Builtin::Text) };
    ($var:ident) => {
        ExprKind::Var(syntax::V(stringify!($var).into(), 0))
    };
    (Optional $ty:ident) => {
        ExprKind::App(
            rc(ExprKind::Builtin(Builtin::Optional)),
            rc(make_type!($ty))
        )
    };
    (List $($rest:tt)*) => {
        ExprKind::App(
            rc(ExprKind::Builtin(Builtin::List)),
            rc(make_type!($($rest)*))
        )
    };
    ({ $($label:ident : $ty:ident),* }) => {{
        let mut kts = syntax::map::DupTreeMap::new();
        $(
            kts.insert(
                Label::from(stringify!($label)),
                rc(make_type!($ty)),
            );
        )*
        ExprKind::RecordType(kts)
    }};
    ($ty:ident -> $($rest:tt)*) => {
        ExprKind::Pi(
            "_".into(),
            rc(make_type!($ty)),
            rc(make_type!($($rest)*))
        )
    };
    (($($arg:tt)*) -> $($rest:tt)*) => {
        ExprKind::Pi(
            "_".into(),
            rc(make_type!($($arg)*)),
            rc(make_type!($($rest)*))
        )
    };
    (forall ($var:ident : $($ty:tt)*) -> $($rest:tt)*) => {
        ExprKind::Pi(
            stringify!($var).into(),
            rc(make_type!($($ty)*)),
            rc(make_type!($($rest)*))
        )
    };
}

pub(crate) fn type_of_builtin<E>(b: Builtin) -> Expr<E> {
    use syntax::Builtin::*;
    rc(match b {
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
    })
}

pub(crate) fn builtin_to_value(b: Builtin) -> Value {
    builtin_to_value_env(b, &NzEnv::new())
}
pub(crate) fn builtin_to_value_env(b: Builtin, env: &NzEnv) -> Value {
    Value::from_kind_and_type(
        ValueKind::from_builtin_env(b, env.clone()),
        crate::semantics::tck::typecheck::typecheck(&type_of_builtin(b))
            .unwrap()
            .normalize_whnf_noenv(),
    )
}
