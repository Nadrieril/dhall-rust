#![doc(html_root_url = "https://docs.rs/dhall/0.4.0")]
#![allow(
    clippy::module_inception,
    clippy::needless_lifetimes,
    clippy::useless_format
)]

mod tests;

pub mod error;
pub mod semantics;
pub mod simple;
pub mod syntax;

use std::fmt::Display;
use std::path::Path;
use url::Url;

use crate::error::{Error, TypeError};
use crate::semantics::parse;
use crate::semantics::resolve;
use crate::semantics::resolve::ImportLocation;
use crate::semantics::{typecheck, typecheck_with, Hir, Nir, Tir, Type};
use crate::syntax::Expr;

pub use crate::simple::{STyKind, SValKind, SimpleType, SimpleValue};

#[derive(Debug, Clone)]
pub(crate) struct Parsed(Expr, ImportLocation);

/// An expression where all imports have been resolved
///
/// Invariant: there must be no `Import` nodes or `ImportAlt` operations left.
#[derive(Debug, Clone)]
pub(crate) struct Resolved(Hir);

/// A typed expression
#[derive(Debug, Clone)]
pub(crate) struct Typed {
    hir: Hir,
    ty: Type,
}

/// A normalized expression.
#[derive(Debug, Clone)]
pub(crate) struct Normalized(Nir);

/// A Dhall value.
#[derive(Debug, Clone)]
pub struct Value {
    /// Invariant: in normal form
    pub(crate) hir: Hir,
    /// Cached conversions because they are annoying to construct from Hir.
    pub(crate) as_simple_val: Option<SimpleValue>,
    pub(crate) as_simple_ty: Option<SimpleType>,
}

/// Controls conversion from `Nir` to `Expr`
#[derive(Copy, Clone, Default)]
pub(crate) struct ToExprOptions {
    /// Whether to convert all variables to `_`
    pub(crate) alpha: bool,
}

impl Parsed {
    pub fn parse_file(f: &Path) -> Result<Parsed, Error> {
        parse::parse_file(f)
    }
    pub fn parse_remote(url: Url) -> Result<Parsed, Error> {
        parse::parse_remote(url)
    }
    pub fn parse_str(s: &str) -> Result<Parsed, Error> {
        parse::parse_str(s)
    }
    pub fn parse_binary_file(f: &Path) -> Result<Parsed, Error> {
        parse::parse_binary_file(f)
    }
    #[allow(dead_code)]
    pub fn parse_binary(data: &[u8]) -> Result<Parsed, Error> {
        parse::parse_binary(data)
    }

    pub fn resolve(self) -> Result<Resolved, Error> {
        resolve::resolve(self)
    }

    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self) -> Expr {
        self.0.clone()
    }
}

impl Resolved {
    pub fn typecheck(&self) -> Result<Typed, TypeError> {
        Ok(Typed::from_tir(typecheck(&self.0)?))
    }
    pub(crate) fn typecheck_with(self, ty: &Hir) -> Result<Typed, TypeError> {
        Ok(Typed::from_tir(typecheck_with(&self.0, ty)?))
    }
    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self) -> Expr {
        self.0.to_expr_noopts()
    }
}

impl Typed {
    fn from_tir(tir: Tir<'_>) -> Self {
        Typed {
            hir: tir.as_hir().clone(),
            ty: tir.ty().clone(),
        }
    }
    /// Reduce an expression to its normal form, performing beta reduction
    pub fn normalize(&self) -> Normalized {
        Normalized(self.hir.rec_eval_closed_expr())
    }

    /// Converts a value back to the corresponding AST expression.
    fn to_expr(&self) -> Expr {
        self.hir.to_expr(ToExprOptions { alpha: false })
    }

    pub(crate) fn ty(&self) -> &Type {
        &self.ty
    }
    pub(crate) fn get_type(&self) -> Result<Normalized, TypeError> {
        Ok(Normalized(self.ty.clone().into_nir()))
    }
}

impl Normalized {
    pub fn to_value(&self) -> Value {
        Value {
            hir: self.to_hir(),
            as_simple_val: SimpleValue::from_nir(&self.0),
            as_simple_ty: SimpleType::from_nir(&self.0),
        }
    }

    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self) -> Expr {
        self.0.to_expr(ToExprOptions::default())
    }
    /// Converts a value back to the corresponding Hir expression.
    pub(crate) fn to_hir(&self) -> Hir {
        self.0.to_hir_noenv()
    }
    /// Converts a value back to the corresponding AST expression, alpha-normalizing in the process.
    pub(crate) fn to_expr_alpha(&self) -> Expr {
        self.0.to_expr(ToExprOptions { alpha: true })
    }
}

impl Value {
    /// Parse a string into a Value, and optionally ensure that the value matches the provided type
    /// annotation.
    pub fn from_str_with_annot(
        s: &str,
        ty: Option<&Self>,
    ) -> Result<Self, Error> {
        let resolved = Parsed::parse_str(s)?.resolve()?;
        let typed = match ty {
            None => resolved.typecheck()?,
            Some(ty) => resolved.typecheck_with(&ty.hir)?,
        };
        Ok(typed.normalize().to_value())
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
    pub(crate) fn to_expr(&self) -> Expr {
        self.hir.to_expr(ToExprOptions::default())
    }
}

macro_rules! derive_traits_for_wrapper_struct {
    ($ty:ident) => {
        impl std::cmp::PartialEq for $ty {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl std::cmp::Eq for $ty {}

        impl std::fmt::Display for $ty {
            fn fmt(
                &self,
                f: &mut std::fmt::Formatter,
            ) -> Result<(), std::fmt::Error> {
                self.0.fmt(f)
            }
        }
    };
}

derive_traits_for_wrapper_struct!(Parsed);

impl From<Parsed> for Expr {
    fn from(other: Parsed) -> Self {
        other.to_expr()
    }
}
impl From<Normalized> for Expr {
    fn from(other: Normalized) -> Self {
        other.to_expr()
    }
}

impl Display for Resolved {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.to_expr().fmt(f)
    }
}

impl Eq for Typed {}
impl PartialEq for Typed {
    fn eq(&self, other: &Self) -> bool {
        self.normalize() == other.normalize()
    }
}
impl Display for Typed {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.to_expr().fmt(f)
    }
}

impl Eq for Normalized {}
impl PartialEq for Normalized {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl Display for Normalized {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.to_expr().fmt(f)
    }
}

impl Eq for Value {}
impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        self.hir == other.hir
    }
}
impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.to_expr().fmt(f)
    }
}
