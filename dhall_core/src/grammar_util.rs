use crate::core::{Expr, Import, X};

pub type ParsedExpr<'i> = Expr<'i, X, Import>;
pub type BoxExpr<'i> = Box<ParsedExpr<'i>>;
