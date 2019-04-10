use crate::error::*;
use crate::expr::*;

pub trait Deserialize<'a>: Sized {
    fn from_str(s: &'a str, ty: Option<&Type>) -> Result<Self>;
}

impl<'a> Deserialize<'a> for Parsed {
    /// Simply parses the provided string. Ignores the
    /// provided type.
    fn from_str(s: &'a str, _ty: Option<&Type>) -> Result<Self> {
        Ok(Parsed::parse_str(s)?)
    }
}

impl<'a> Deserialize<'a> for Resolved {
    /// Parses and resolves the provided string. Ignores the
    /// provided type.
    fn from_str(s: &'a str, ty: Option<&Type>) -> Result<Self> {
        Ok(Parsed::from_str(s, ty)?.resolve()?)
    }
}

impl<'a> Deserialize<'a> for Typed {
    /// Parses, resolves and typechecks the provided string.
    fn from_str(s: &'a str, ty: Option<&Type>) -> Result<Self> {
        let resolved = Resolved::from_str(s, ty)?;
        match ty {
            None => Ok(resolved.typecheck()?),
            Some(t) => Ok(resolved.typecheck_with(t)?),
        }
    }
}

impl<'a> Deserialize<'a> for Normalized {
    /// Parses, resolves, typechecks and normalizes the provided string.
    fn from_str(s: &'a str, ty: Option<&Type>) -> Result<Self> {
        Ok(Typed::from_str(s, ty)?.normalize())
    }
}

impl<'a> Deserialize<'a> for Type {
    fn from_str(s: &'a str, ty: Option<&Type>) -> Result<Self> {
        Ok(Normalized::from_str(s, ty)?.into_type())
    }
}
