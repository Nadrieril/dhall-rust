use crate::error::*;
use crate::expr::*;

pub trait Deserialize<'a>: Sized {
    fn from_str(s: &'a str, ty: Option<&Type>) -> Result<Self>;
}

impl<'de: 'a, 'a> Deserialize<'de> for Parsed<'a> {
    /// Simply parses the provided string. Ignores the
    /// provided type.
    fn from_str(s: &'de str, _: Option<&Type>) -> Result<Self> {
        Ok(Parsed::parse_str(s)?)
    }
}

impl<'de: 'a, 'a> Deserialize<'de> for Resolved<'a> {
    /// Parses and resolves the provided string. Ignores the
    /// provided type.
    fn from_str(s: &'de str, ty: Option<&Type>) -> Result<Self> {
        Ok(Parsed::from_str(s, ty)?.resolve()?)
    }
}

impl<'de: 'a, 'a> Deserialize<'de> for Typed<'a> {
    /// Parses, resolves and typechecks the provided string.
    fn from_str(s: &'de str, ty: Option<&Type>) -> Result<Self> {
        let resolved = Resolved::from_str(s, ty)?;
        match ty {
            None => Ok(resolved.typecheck()?),
            Some(t) => Ok(resolved.typecheck_with(t)?),
        }
    }
}

impl<'de: 'a, 'a> Deserialize<'de> for Normalized<'a> {
    /// Parses, resolves, typechecks and normalizes the provided string.
    fn from_str(s: &'de str, ty: Option<&Type>) -> Result<Self> {
        Ok(Typed::from_str(s, ty)?.normalize())
    }
}

impl<'de: 'a, 'a> Deserialize<'de> for Type<'a> {
    fn from_str(s: &'de str, ty: Option<&Type>) -> Result<Self> {
        Ok(Normalized::from_str(s, ty)?.into_type())
    }
}
