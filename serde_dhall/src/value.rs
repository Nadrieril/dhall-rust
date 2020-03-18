use dhall::semantics::Hir;
use dhall::syntax::Expr;
use dhall::{Normalized, Parsed};

use crate::simple::{SimpleType, SimpleValue};
use crate::Error;

/// A Dhall value.
#[derive(Debug, Clone)]
pub struct Value {
    /// Invariant: in normal form
    pub(crate) hir: Hir,
    /// Cached conversions because they are annoying to construct from Hir.
    /// At most one of them will be `Some`.
    pub(crate) as_simple_val: Option<SimpleValue>,
    pub(crate) as_simple_ty: Option<SimpleType>,
}

impl Value {
    /// Parse a string into a Value, and optionally ensure that the value matches the provided type
    /// annotation.
    pub fn from_str_with_annot(
        s: &str,
        ty: Option<&Self>,
    ) -> Result<Self, Error> {
        Self::from_str_with_annot_dhall_error(s, ty).map_err(Error::Dhall)
    }
    fn from_normalized(x: &Normalized) -> Self {
        Value {
            hir: x.to_hir(),
            as_simple_val: SimpleValue::from_nir(x.as_nir()),
            as_simple_ty: SimpleType::from_nir(x.as_nir()),
        }
    }

    fn from_str_with_annot_dhall_error(
        s: &str,
        ty: Option<&Self>,
    ) -> Result<Self, dhall::error::Error> {
        let resolved = Parsed::parse_str(s)?.resolve()?;
        let typed = match ty {
            None => resolved.typecheck()?,
            Some(ty) => resolved.typecheck_with(&ty.hir)?,
        };
        Ok(Self::from_normalized(&typed.normalize()))
    }

    /// Converts a Value into a SimpleValue.
    pub fn to_simple_value(&self) -> Option<SimpleValue> {
        self.as_simple_val.clone()
    }
    /// Converts a Value into a SimpleType.
    pub fn to_simple_type(&self) -> Option<SimpleType> {
        self.as_simple_ty.clone()
    }

    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self) -> Expr {
        self.hir.to_expr(Default::default())
    }
}

impl Eq for Value {}
impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        self.hir == other.hir
    }
}
impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.to_expr().fmt(f)
    }
}
