use crate::*;

#[derive(Debug, Clone)]
pub enum DhallConversionError {}

pub trait DhallType: Sized {
    fn dhall_type() -> DhallExpr;
    // fn as_dhall(&self) -> DhallExpr;
    // fn from_dhall(e: DhallExpr) -> Result<Self, DhallConversionError>;
}
