use crate::imports::ImportError;
use crate::imports::ImportRoot;
use crate::typecheck::TypeError;
use dhall_core::*;

#[derive(Debug, Clone)]
pub struct Parsed(pub(crate) SubExpr<X, Import>, pub(crate) ImportRoot);
#[derive(Debug, Clone)]
pub struct Resolved(pub(crate) SubExpr<X, X>);
#[derive(Debug, Clone)]
pub struct Typed(pub(crate) SubExpr<X, X>, Type);
#[derive(Debug, Clone)]
pub struct Type(pub(crate) Box<Normalized>);
#[derive(Debug, Clone)]
pub struct Normalized(pub(crate) SubExpr<X, X>);

impl Parsed {
    pub fn resolve(self) -> Result<Resolved, ImportError> {
        crate::imports::resolve_expr(self, true)
    }
    pub fn resolve_no_imports(self) -> Result<Resolved, ImportError> {
        crate::imports::resolve_expr(self, false)
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
