use crate::core::{Expr, X, Import};

pub type ParsedExpr<'i> = Expr<'i, X, Import>;
pub type BoxExpr<'i> = Box<ParsedExpr<'i>>;
pub type ExprOpFn<'i> = fn(BoxExpr<'i>, BoxExpr<'i>) -> ParsedExpr<'i>;
pub type ExprListFn<'i> =
    fn(Option<BoxExpr<'i>>, Vec<ParsedExpr<'i>>) -> ParsedExpr<'i>;
