use crate::typecheck::TypeError;
use dhall_core::*;

pub struct Parsed(SubExpr<X, Import>);
pub struct Resolved(SubExpr<X, X>);
pub struct Typed(SubExpr<X, X>, Type);
pub struct Type(Box<Normalized>);
pub struct Normalized(SubExpr<X, X>);

// impl Parsed {
//     pub fn resolve(self) -> Result<Resolved, ImportError> {
//         Ok(Resolved(crate::imports::resolve(self.0)?))
//     }
// }
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
