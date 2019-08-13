use std::borrow::Cow;
use std::fmt::Display;
use std::path::Path;

use dhall_syntax::{Const, SubExpr, Void};

use crate::core::thunk::{Thunk, TypedThunk};
use crate::core::value::Value;
use crate::core::var::{AlphaVar, Shift, Subst};
use crate::error::{EncodeError, Error, ImportError, TypeError};

use resolve::ImportRoot;

pub(crate) mod binary;
pub(crate) mod normalize;
pub(crate) mod parse;
pub(crate) mod resolve;
pub(crate) mod typecheck;

pub type ParsedSubExpr = SubExpr<Void>;
pub type DecodedSubExpr = SubExpr<Void>;
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
pub struct Typed(TypedThunk);

/// A normalized expression.
///
/// Invariant: the contained Typed expression must be in normal form,
#[derive(Debug, Clone)]
pub struct Normalized(Typed);

pub type Type = Typed;

impl Parsed {
    pub fn parse_file(f: &Path) -> Result<Parsed, Error> {
        parse::parse_file(f)
    }
    pub fn parse_str(s: &str) -> Result<Parsed, Error> {
        parse::parse_str(s)
    }
    #[allow(dead_code)]
    pub fn parse_binary_file(f: &Path) -> Result<Parsed, Error> {
        parse::parse_binary_file(f)
    }
    #[allow(dead_code)]
    pub fn parse_binary(data: &[u8]) -> Result<Parsed, Error> {
        parse::parse_binary(data)
    }

    pub fn resolve(self) -> Result<Resolved, ImportError> {
        resolve::resolve(self)
    }
    #[allow(dead_code)]
    pub fn skip_resolve(self) -> Result<Resolved, ImportError> {
        resolve::skip_resolve_expr(self)
    }

    #[allow(dead_code)]
    pub fn encode(&self) -> Result<Vec<u8>, EncodeError> {
        crate::phase::binary::encode(&self.0)
    }
}

impl Resolved {
    pub fn typecheck(self) -> Result<Typed, TypeError> {
        typecheck::typecheck(self)
    }
    pub fn typecheck_with(self, ty: &Type) -> Result<Typed, TypeError> {
        typecheck::typecheck_with(self, ty)
    }
    /// Pretends this expression has been typechecked. Use with care.
    #[allow(dead_code)]
    pub fn skip_typecheck(self) -> Typed {
        typecheck::skip_typecheck(self)
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

    pub fn from_thunk_and_type(th: Thunk, t: Type) -> Self {
        Typed(TypedThunk::from_thunk_and_type(th, t))
    }
    pub fn from_thunk_untyped(th: Thunk) -> Self {
        Typed(TypedThunk::from_thunk_untyped(th))
    }
    pub fn from_const(c: Const) -> Self {
        Typed(TypedThunk::from_const(c))
    }
    pub fn from_value_untyped(v: Value) -> Self {
        Typed(TypedThunk::from_value_untyped(v))
    }
    pub fn from_typethunk(th: TypedThunk) -> Self {
        Typed(th)
    }

    pub fn to_value(&self) -> Value {
        self.0.to_value()
    }
    pub fn to_expr(&self) -> NormalizedSubExpr {
        self.0.to_expr()
    }
    pub fn to_expr_alpha(&self) -> NormalizedSubExpr {
        self.0.to_expr_alpha()
    }
    pub fn to_thunk(&self) -> Thunk {
        self.0.to_thunk()
    }
    // Deprecated
    pub fn to_type(&self) -> Type {
        self.clone()
    }
    // Deprecated
    pub fn into_type(self) -> Type {
        self
    }
    pub fn into_typethunk(self) -> TypedThunk {
        self.0
    }
    pub fn to_normalized(&self) -> Normalized {
        self.clone().normalize()
    }
    pub fn as_const(&self) -> Option<Const> {
        self.0.as_const()
    }

    pub fn normalize_mut(&mut self) {
        self.0.normalize_mut()
    }

    pub fn get_type(&self) -> Result<Cow<'_, Type>, TypeError> {
        self.0.get_type()
    }
}

impl Normalized {
    #[allow(dead_code)]
    pub fn to_expr(&self) -> NormalizedSubExpr {
        self.0.to_expr()
    }
    #[allow(dead_code)]
    pub fn to_expr_alpha(&self) -> NormalizedSubExpr {
        self.0.to_expr_alpha()
    }
    #[allow(dead_code)]
    pub fn to_type(&self) -> Type {
        self.0.to_type()
    }
    pub fn to_value(&self) -> Value {
        self.0.to_value()
    }
    pub fn into_typed(self) -> Typed {
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

impl Subst<Typed> for Typed {
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
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

impl Eq for Typed {}
impl PartialEq for Typed {
    fn eq(&self, other: &Self) -> bool {
        self.to_value() == other.to_value()
    }
}

impl Display for Typed {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.to_expr().fmt(f)
    }
}
