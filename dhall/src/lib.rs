#![doc(html_root_url = "https://docs.rs/dhall/0.3.0")]
#![allow(
    clippy::int_plus_one, // Comes from pest_consume macro
    clippy::module_inception,
    clippy::needless_lifetimes,
    clippy::useless_format
)]

mod tests;

pub mod error;
pub mod semantics;
pub mod syntax;

use std::fmt::Display;
use std::path::Path;
use url::Url;

use crate::error::{EncodeError, Error, TypeError};
use crate::semantics::parse;
use crate::semantics::resolve;
use crate::semantics::resolve::ImportLocation;
use crate::semantics::{
    typecheck, typecheck_with, Hir, Nir, NirKind, Tir, Type,
};
use crate::syntax::binary;
use crate::syntax::{Builtin, Expr};

pub type ParsedExpr = Expr;
pub type DecodedExpr = Expr;
pub type ResolvedExpr = Expr;
pub type NormalizedExpr = Expr;

#[derive(Debug, Clone)]
pub struct Parsed(ParsedExpr, ImportLocation);

/// An expression where all imports have been resolved
///
/// Invariant: there must be no `Import` nodes or `ImportAlt` operations left.
#[derive(Debug, Clone)]
pub struct Resolved(Hir);

/// A typed expression
#[derive(Debug, Clone)]
pub struct Typed {
    hir: Hir,
    ty: Type,
}

/// A normalized expression.
///
/// Invariant: the contained expression must be in normal form,
#[derive(Debug, Clone)]
pub struct Normalized(Nir);

/// Controls conversion from `Nir` to `Expr`
#[derive(Copy, Clone)]
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
    pub fn parse_binary(data: &[u8]) -> Result<Parsed, Error> {
        parse::parse_binary(data)
    }

    pub fn resolve(self) -> Result<Resolved, Error> {
        resolve::resolve(self)
    }
    pub fn skip_resolve(self) -> Result<Resolved, Error> {
        Ok(Resolved(resolve::skip_resolve(&self.0)?))
    }

    pub fn encode(&self) -> Result<Vec<u8>, EncodeError> {
        binary::encode(&self.0)
    }

    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self) -> ParsedExpr {
        self.0.clone()
    }
}

impl Resolved {
    pub fn typecheck(&self) -> Result<Typed, TypeError> {
        Ok(Typed::from_tir(typecheck(&self.0)?))
    }
    pub fn typecheck_with(self, ty: &Normalized) -> Result<Typed, TypeError> {
        Ok(Typed::from_tir(typecheck_with(&self.0, ty.to_hir())?))
    }
    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self) -> ResolvedExpr {
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
    fn to_expr(&self) -> ResolvedExpr {
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
    pub fn encode(&self) -> Result<Vec<u8>, EncodeError> {
        binary::encode(&self.to_expr())
    }

    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self) -> NormalizedExpr {
        self.0.to_expr(ToExprOptions { alpha: false })
    }
    /// Converts a value back to the corresponding Hir expression.
    pub(crate) fn to_hir(&self) -> Hir {
        self.0.to_hir_noenv()
    }
    /// Converts a value back to the corresponding AST expression, alpha-normalizing in the process.
    pub(crate) fn to_expr_alpha(&self) -> NormalizedExpr {
        self.0.to_expr(ToExprOptions { alpha: true })
    }
    pub(crate) fn to_nir(&self) -> Nir {
        self.0.clone()
    }
    pub(crate) fn into_nir(self) -> Nir {
        self.0
    }

    pub(crate) fn from_kind(v: NirKind) -> Self {
        Normalized(Nir::from_kind(v))
    }
    pub(crate) fn from_nir(th: Nir) -> Self {
        Normalized(th)
    }

    pub fn make_builtin_type(b: Builtin) -> Self {
        Normalized::from_nir(Nir::from_builtin(b))
    }
    pub fn make_optional_type(t: Normalized) -> Self {
        Normalized::from_nir(
            Nir::from_builtin(Builtin::Optional).app(t.to_nir()),
        )
    }
    pub fn make_list_type(t: Normalized) -> Self {
        Normalized::from_nir(Nir::from_builtin(Builtin::List).app(t.to_nir()))
    }
    pub fn make_record_type(
        kts: impl Iterator<Item = (String, Normalized)>,
    ) -> Self {
        Normalized::from_kind(NirKind::RecordType(
            kts.map(|(k, t)| (k.into(), t.into_nir())).collect(),
        ))
    }
    pub fn make_union_type(
        kts: impl Iterator<Item = (String, Option<Normalized>)>,
    ) -> Self {
        Normalized::from_kind(NirKind::UnionType(
            kts.map(|(k, t)| (k.into(), t.map(|t| t.into_nir())))
                .collect(),
        ))
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

impl std::hash::Hash for Normalized {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        if let Ok(vec) = self.encode() {
            vec.hash(state)
        }
    }
}

impl From<Parsed> for NormalizedExpr {
    fn from(other: Parsed) -> Self {
        other.to_expr()
    }
}
impl From<Normalized> for NormalizedExpr {
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
