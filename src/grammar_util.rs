use core::{Expr, X};
use lexer::Builtin;

pub type ParsedExpr<'i> = Expr<'i, X, X>; // FIXME Parse paths and replace the second X with Path
pub type BoxExpr<'i> = Box<ParsedExpr<'i>>;
pub type ExprOpFn<'i> = fn(BoxExpr<'i>, BoxExpr<'i>) -> ParsedExpr<'i>;
pub type ExprListFn<'i> = fn(BoxExpr<'i>, Vec<ParsedExpr<'i>>) -> ParsedExpr<'i>;

pub fn builtin_expr<'i, S, A>(b: Builtin) -> Expr<'i, S, A> {
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
