use std::borrow::Cow;
use std::fmt::Display;
use std::path::Path;

use dhall_syntax::{Const, SubExpr};

use crate::core::value::Value;
use crate::core::valuef::ValueF;
use crate::core::var::{AlphaVar, Shift, Subst};
use crate::error::{EncodeError, Error, ImportError, TypeError};

use resolve::ImportRoot;

pub(crate) mod binary;
pub(crate) mod normalize;
pub(crate) mod parse;
pub(crate) mod resolve;
pub(crate) mod typecheck;

pub type ParsedSubExpr = SubExpr<!>;
pub type DecodedSubExpr = SubExpr<!>;
pub type ResolvedSubExpr = SubExpr<Normalized>;
pub type NormalizedSubExpr = SubExpr<Normalized>;

#[derive(Debug, Clone)]
pub struct Parsed(ParsedSubExpr, ImportRoot);

/// An expression where all imports have been resolved
///
/// Invariant: there must be no `Import` nodes or `ImportAlt` operations left.
#[derive(Debug, Clone)]
pub struct Resolved(ResolvedSubExpr);

/// A typed expression
#[derive(Debug, Clone)]
pub struct Typed(Value);

/// A normalized expression.
///
/// Invariant: the contained Typed expression must be in normal form,
#[derive(Debug, Clone)]
pub struct Normalized(Typed);

impl Parsed {
    pub fn parse_file(f: &Path) -> Result<Parsed, Error> {
        parse::parse_file(f)
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

    pub fn resolve(self) -> Result<Resolved, ImportError> {
        resolve::resolve(self)
    }
    pub fn skip_resolve(self) -> Result<Resolved, ImportError> {
        resolve::skip_resolve_expr(self)
    }

    pub fn encode(&self) -> Result<Vec<u8>, EncodeError> {
        crate::phase::binary::encode(&self.0)
    }
}

impl Resolved {
    pub fn typecheck(self) -> Result<Typed, TypeError> {
        Ok(typecheck::typecheck(self.0)?.into_typed())
    }
    pub fn typecheck_with(self, ty: &Typed) -> Result<Typed, TypeError> {
        Ok(typecheck::typecheck_with(self.0, ty.to_expr())?.into_typed())
    }
}

impl Typed {
    /// Reduce an expression to its normal form, performing beta reduction
    ///
    /// `normalize` does not type-check the expression.  You may want to type-check
    /// expressions before normalizing them since normalization can convert an
    /// ill-typed expression into a well-typed expression.
    ///
    /// However, `normalize` will not fail if the expression is ill-typed and will
    /// leave ill-typed sub-expressions unevaluated.
    pub fn normalize(mut self) -> Normalized {
        self.normalize_mut();
        Normalized(self)
    }

    pub(crate) fn from_const(c: Const) -> Self {
        Typed(Value::from_const(c))
    }
    pub fn from_valuef_and_type(v: ValueF, t: Typed) -> Self {
        Typed(Value::from_valuef_and_type(v, t.into_value()))
    }
    pub(crate) fn from_value(th: Value) -> Self {
        Typed(th)
    }
    pub fn const_type() -> Self {
        Typed::from_const(Const::Type)
    }

    pub fn to_expr(&self) -> NormalizedSubExpr {
        self.0.to_expr()
    }
    pub(crate) fn to_expr_alpha(&self) -> NormalizedSubExpr {
        self.0.to_expr_alpha()
    }
    pub fn to_value(&self) -> Value {
        self.0.clone()
    }
    pub(crate) fn into_value(self) -> Value {
        self.0
    }

    pub(crate) fn normalize_mut(&mut self) {
        self.0.normalize_mut()
    }

    #[allow(dead_code)]
    pub(crate) fn get_type(&self) -> Result<Cow<'_, Typed>, TypeError> {
        Ok(Cow::Owned(self.0.get_type()?.into_owned().into_typed()))
    }
}

impl Normalized {
    pub fn encode(&self) -> Result<Vec<u8>, EncodeError> {
        crate::phase::binary::encode(&self.to_expr())
    }

    pub(crate) fn to_expr(&self) -> NormalizedSubExpr {
        self.0.to_expr()
    }
    #[allow(dead_code)]
    pub(crate) fn to_expr_alpha(&self) -> NormalizedSubExpr {
        self.0.to_expr_alpha()
    }
    pub(crate) fn into_typed(self) -> Typed {
        self.0
    }
}

impl Shift for Typed {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(Typed(self.0.shift(delta, var)?))
    }
}

impl Shift for Normalized {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(Normalized(self.0.shift(delta, var)?))
    }
}

impl Subst<Value> for Typed {
    fn subst_shift(&self, var: &AlphaVar, val: &Value) -> Self {
        Typed(self.0.subst_shift(var, val))
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
derive_traits_for_wrapper_struct!(Resolved);
derive_traits_for_wrapper_struct!(Normalized);

impl std::hash::Hash for Normalized {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        match self.encode() {
            Ok(vec) => vec.hash(state),
            Err(_) => {}
        }
    }
}

impl Eq for Typed {}
impl PartialEq for Typed {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Display for Typed {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.to_expr().fmt(f)
    }
}
