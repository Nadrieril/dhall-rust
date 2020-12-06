#![doc(html_root_url = "https://docs.rs/dhall/0.9.0")]
#![allow(
    clippy::implicit_hasher,
    clippy::module_inception,
    clippy::needless_lifetimes,
    clippy::new_ret_no_self,
    clippy::new_without_default,
    clippy::useless_format,
    unreachable_code
)]

pub mod builtins;
pub mod ctxt;
pub mod error;
pub mod operations;
pub mod semantics;
pub mod syntax;
pub mod utils;

use std::fmt::Display;
use std::path::Path;
use url::Url;

use crate::error::{Error, TypeError};
use crate::semantics::parse;
use crate::semantics::resolve;
use crate::semantics::resolve::ImportLocation;
use crate::semantics::{typecheck, typecheck_with, Hir, Nir, Tir, Type};
use crate::syntax::Expr;

pub use ctxt::{Ctxt, ImportId, ImportResultId};

#[derive(Debug, Clone)]
pub struct Parsed(Expr, ImportLocation);

/// An expression where all imports have been resolved
///
/// Invariant: there must be no `Import` nodes or `ImportAlt` operations left.
#[derive(Debug, Clone)]
pub struct Resolved<'cx>(Hir<'cx>);

/// A typed expression
#[derive(Debug, Clone)]
pub struct Typed<'cx> {
    pub hir: Hir<'cx>,
    pub ty: Type<'cx>,
}

/// A normalized expression.
///
/// This is actually a lie, because the expression will only get normalized on demand.
#[derive(Debug, Clone)]
pub struct Normalized<'cx>(Nir<'cx>);

/// Controls conversion from `Nir` to `Expr`
#[derive(Copy, Clone, Default)]
pub struct ToExprOptions {
    /// Whether to convert all variables to `_`
    pub alpha: bool,
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

    pub fn resolve<'cx>(self, cx: Ctxt<'cx>) -> Result<Resolved<'cx>, Error> {
        resolve::resolve(cx, self)
    }
    pub fn skip_resolve<'cx>(self) -> Result<Resolved<'cx>, Error> {
        resolve::skip_resolve(self)
    }

    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self) -> Expr {
        self.0.clone()
    }
}

impl<'cx> Resolved<'cx> {
    pub fn typecheck(&self, cx: Ctxt<'cx>) -> Result<Typed<'cx>, TypeError> {
        Ok(Typed::from_tir(typecheck(cx, &self.0)?))
    }
    pub fn typecheck_with(
        self,
        cx: Ctxt<'cx>,
        ty: &Hir<'cx>,
    ) -> Result<Typed<'cx>, TypeError> {
        Ok(Typed::from_tir(typecheck_with(cx, &self.0, ty)?))
    }
    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self) -> Expr {
        self.0.to_expr_noopts()
    }
}

impl<'cx> Typed<'cx> {
    fn from_tir(tir: Tir<'cx, '_>) -> Self {
        Typed {
            hir: tir.as_hir().clone(),
            ty: tir.ty().clone(),
        }
    }
    /// Reduce an expression to its normal form, performing beta reduction
    pub fn normalize(&self, cx: Ctxt<'cx>) -> Normalized<'cx> {
        Normalized(self.hir.eval_closed_expr(cx))
    }

    /// Converts a value back to the corresponding AST expression.
    fn to_expr(&self) -> Expr {
        self.hir.to_expr(ToExprOptions { alpha: false })
    }

    pub fn ty(&self) -> &Type<'cx> {
        &self.ty
    }
    pub fn get_type(&self) -> Result<Normalized<'cx>, TypeError> {
        Ok(Normalized(self.ty.clone().into_nir()))
    }
}

impl<'cx> Normalized<'cx> {
    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self) -> Expr {
        self.0.to_expr(ToExprOptions::default())
    }
    /// Converts a value back to the corresponding Hir expression.
    pub fn to_hir(&self) -> Hir<'cx> {
        self.0.to_hir_noenv()
    }
    pub fn as_nir(&self) -> &Nir<'cx> {
        &self.0
    }
    /// Converts a value back to the corresponding AST expression, alpha-normalizing in the process.
    pub fn to_expr_alpha(&self) -> Expr {
        self.0.to_expr(ToExprOptions { alpha: true })
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
impl<'cx> From<Normalized<'cx>> for Expr {
    fn from(other: Normalized<'cx>) -> Self {
        other.to_expr()
    }
}

impl<'cx> Display for Resolved<'cx> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.to_expr().fmt(f)
    }
}

impl<'cx> Display for Typed<'cx> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.to_expr().fmt(f)
    }
}

impl<'cx> Eq for Normalized<'cx> {}
impl<'cx> PartialEq for Normalized<'cx> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl<'cx> Display for Normalized<'cx> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.to_expr().fmt(f)
    }
}
