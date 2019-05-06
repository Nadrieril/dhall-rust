use crate::error::*;
use crate::phase::*;

/// A data structure that can be deserialized from a Dhall expression
///
/// This is automatically implemented for any type that [serde][serde]
/// can deserialize.
///
/// This trait cannot be implemented manually.
pub trait Deserialize<'de>: Sized {
    /// See [dhall::de::from_str][crate::de::from_str]
    fn from_str(s: &'de str, ty: Option<&Type>) -> Result<Self>;
}

impl<'de> Deserialize<'de> for Parsed {
    /// Simply parses the provided string. Ignores the
    /// provided type.
    fn from_str(s: &'de str, _: Option<&Type>) -> Result<Self> {
        Ok(Parsed::parse_str(s)?)
    }
}

impl<'de> Deserialize<'de> for Resolved {
    /// Parses and resolves the provided string. Ignores the
    /// provided type.
    fn from_str(s: &'de str, ty: Option<&Type>) -> Result<Self> {
        Ok(Parsed::from_str(s, ty)?.resolve()?)
    }
}

impl<'de> Deserialize<'de> for Typed {
    /// Parses, resolves and typechecks the provided string.
    fn from_str(s: &'de str, ty: Option<&Type>) -> Result<Self> {
        let resolved = Resolved::from_str(s, ty)?;
        match ty {
            None => Ok(resolved.typecheck()?),
            Some(t) => Ok(resolved.typecheck_with(t)?),
        }
    }
}

impl<'de> Deserialize<'de> for Normalized {
    /// Parses, resolves, typechecks and normalizes the provided string.
    fn from_str(s: &'de str, ty: Option<&Type>) -> Result<Self> {
        Ok(Typed::from_str(s, ty)?.normalize())
    }
}

impl<'de> Deserialize<'de> for Type {
    fn from_str(s: &'de str, ty: Option<&Type>) -> Result<Self> {
        Ok(Normalized::from_str(s, ty)?.to_type())
    }
}
