use core::{Expr, X};
use lexer::Builtin;

pub type ParsedExpr<'i> = Expr<'i, X, X>; // FIXME Parse paths and replace the second X with Path
pub type BoxExpr<'i> = Box<ParsedExpr<'i>>;
pub type ExprOpFn<'i> = fn(BoxExpr<'i>, BoxExpr<'i>) -> ParsedExpr<'i>;
pub type ExprListFn<'i> = fn(BoxExpr<'i>, Vec<ParsedExpr<'i>>) -> ParsedExpr<'i>;

pub fn builtin_expr<'i, S, A>(b: Builtin) -> Expr<'i, S, A> {
    match b {
        Builtin::Type(t)  => Expr::BuiltinType(t),
        Builtin::Value(v) => Expr::BuiltinValue(v),
    }
}
