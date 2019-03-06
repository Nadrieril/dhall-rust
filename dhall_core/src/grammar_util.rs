use crate::core::{Expr, Import, X};

pub type ParsedExpr = Expr<X, Import>;
pub type BoxExpr = Box<ParsedExpr>;
