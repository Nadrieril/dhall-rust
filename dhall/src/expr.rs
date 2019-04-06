use crate::imports::ImportRoot;
use crate::typecheck::TypeError;
use dhall_core::*;

#[derive(Debug, Clone, Eq)]
pub struct Parsed(pub(crate) SubExpr<X, Import>, pub(crate) ImportRoot);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Resolved(pub(crate) SubExpr<X, X>);

#[derive(Debug, Clone)]
pub struct Typed(pub(crate) SubExpr<X, X>, Type);

#[derive(Debug, Clone)]
pub struct Type(pub(crate) Box<Normalized>);

#[derive(Debug, Clone)]
pub struct Normalized(pub(crate) SubExpr<X, X>);

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

impl Resolved {
    pub fn typecheck(self) -> Result<Typed, TypeError<X>> {
        let typ = Type(Box::new(Normalized(crate::typecheck::type_of(
            self.0.clone(),
        )?)));
        Ok(Typed(self.0, typ))
    }
}
impl Typed {
    pub fn normalize(self) -> Normalized {
        Normalized(crate::normalize::normalize(self.0))
    }
    pub fn get_type(&self) -> &Type {
        &self.1
    }
}
impl Type {
    pub fn as_expr(&self) -> &Normalized {
        &*self.0
    }
}
