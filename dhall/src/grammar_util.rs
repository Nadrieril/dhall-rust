use crate::core::{Expr, X};

pub type ParsedExpr<'i> = Expr<'i, X, X>; // FIXME Parse paths and replace the second X with Path
pub type BoxExpr<'i> = Box<ParsedExpr<'i>>;
pub type ExprOpFn<'i> = fn(BoxExpr<'i>, BoxExpr<'i>) -> ParsedExpr<'i>;
pub type ExprListFn<'i> =
    fn(Option<BoxExpr<'i>>, Vec<ParsedExpr<'i>>) -> ParsedExpr<'i>;
