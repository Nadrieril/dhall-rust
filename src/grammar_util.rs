use core::Expr;
use lexer::Builtin;

pub type BoxExpr = Box<Expr<(), ()>>;
pub type ExprOpFn = fn(BoxExpr, BoxExpr) -> Expr<(), ()>;

pub fn bx<T>(x: T) -> Box<T> {
    Box::new(x)
}

pub fn builtin_expr<S, A>(b: Builtin) -> Expr<S, A> {
    match b {
        Builtin::Natural => Expr::Natural,
        Builtin::NaturalFold => Expr::NaturalFold,
        Builtin::NaturalBuild => Expr::NaturalBuild,
        Builtin::NaturalIsZero => Expr::NaturalIsZero,
        Builtin::NaturalEven => Expr::NaturalEven,
        Builtin::NaturalOdd => Expr::NaturalOdd,
        Builtin::Integer => Expr::Integer,
        Builtin::Double => Expr::Double,
        Builtin::Text => Expr::Text,
        Builtin::List => Expr::List,
        Builtin::ListBuild => Expr::ListBuild,
        Builtin::ListFold => Expr::ListFold,
        Builtin::ListLength => Expr::ListLength,
        Builtin::ListHead => Expr::ListHead,
        Builtin::ListLast => Expr::ListLast,
        Builtin::ListIndexed => Expr::ListIndexed,
        Builtin::ListReverse => Expr::ListReverse,
        Builtin::Optional => Expr::Optional,
        Builtin::OptionalFold => Expr::OptionalFold,
        Builtin::Bool => Expr::Bool,
    }
}
