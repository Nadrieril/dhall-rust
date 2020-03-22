use dhall::semantics::{Hir, Nir};
use dhall::syntax::Expr;

use crate::simple::{Type as SimpleType, Value as SimpleValue};
use crate::{Deserialize, Error, Sealed};

/// An arbitrary Dhall value.
/// TODO
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
    pub(crate) fn from_nir(x: &Nir) -> Self {
        Value {
            hir: x.to_hir_noenv(),
            as_simple_val: SimpleValue::from_nir(x),
            as_simple_ty: SimpleType::from_nir(x),
        }
    }

    /// Converts a Value into a SimpleValue.
    /// TODO
    pub fn to_simple_value(&self) -> Option<SimpleValue> {
        self.as_simple_val.clone()
    }
    /// Converts a Value into a SimpleType.
    /// TODO
    pub fn to_simple_type(&self) -> Option<SimpleType> {
        self.as_simple_ty.clone()
    }

    /// Converts a value back to the corresponding AST expression.
    pub(crate) fn to_expr(&self) -> Expr {
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

impl Sealed for Value {}

impl Deserialize for Value {
    fn from_dhall(v: &Value) -> Result<Self, Error> {
        Ok(v.clone())
    }
}
