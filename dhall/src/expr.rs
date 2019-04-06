use crate::imports::ImportRoot;
use dhall_core::*;

#[derive(Debug, Clone, Eq)]
pub struct Parsed(pub(crate) SubExpr<X, Import>, pub(crate) ImportRoot);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Resolved(pub(crate) SubExpr<X, X>);

#[derive(Debug, Clone)]
pub struct Typed(pub(crate) SubExpr<X, X>, pub(crate) Type<'static>);

#[derive(Debug, Clone)]
pub struct Type<'a>(pub(crate) std::borrow::Cow<'a, TypeInternal>);

#[derive(Debug, Clone)]
pub(crate) enum TypeInternal {
    Expr(Box<Normalized>),
    Universe(usize),
}

#[derive(Debug, Clone)]
pub struct Normalized(pub(crate) SubExpr<X, X>, pub(crate) Type<'static>);

impl PartialEq for Parsed {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl std::fmt::Display for Parsed {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.0.fmt(f)
    }
}
