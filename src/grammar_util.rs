use core::Expr;
use lexer::Builtin;

pub type ParsedExpr = Expr<(), ()>;
pub type BoxExpr = Box<ParsedExpr>;
pub type ExprOpFn = fn(BoxExpr, BoxExpr) -> ParsedExpr;
pub type ExprListFn = fn(BoxExpr, Vec<ParsedExpr>) -> ParsedExpr;

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
        Builtin::ListBuild => Expr::ListBuild,
        Builtin::ListFold => Expr::ListFold,
        Builtin::ListLength => Expr::ListLength,
        Builtin::ListHead => Expr::ListHead,
        Builtin::ListLast => Expr::ListLast,
        Builtin::ListIndexed => Expr::ListIndexed,
        Builtin::ListReverse => Expr::ListReverse,
        Builtin::OptionalFold => Expr::OptionalFold,
        Builtin::Bool => Expr::Bool,
    }
}
