use std::fmt::Display;
use std::path::Path;

use crate::error::{EncodeError, Error, ImportError, TypeError};
use crate::semantics::core::value::Value;
use crate::semantics::core::value::ValueKind;
use crate::semantics::tck::tyexpr::TyExpr;
use crate::syntax::binary;
use crate::syntax::{Builtin, Const, Expr};
use resolve::ImportRoot;

pub(crate) mod normalize;
pub(crate) mod parse;
pub(crate) mod resolve;
pub(crate) mod typecheck;

pub type ParsedExpr = Expr<Normalized>;
pub type DecodedExpr = Expr<Normalized>;
pub type ResolvedExpr = Expr<Normalized>;
pub type NormalizedExpr = Expr<Normalized>;

#[derive(Debug, Clone)]
pub struct Parsed(ParsedExpr, ImportRoot);

/// An expression where all imports have been resolved
///
/// Invariant: there must be no `Import` nodes or `ImportAlt` operations left.
#[derive(Debug, Clone)]
pub struct Resolved(ResolvedExpr);

/// A typed expression
#[derive(Debug, Clone)]
pub struct Typed(TyExpr);

/// A normalized expression.
///
/// Invariant: the contained Typed expression must be in normal form,
#[derive(Debug, Clone)]
pub struct Normalized(Value);

/// Controls conversion from `Value` to `Expr`
#[derive(Copy, Clone)]
pub(crate) struct ToExprOptions {
    /// Whether to convert all variables to `_`
    pub(crate) alpha: bool,
    /// Whether to normalize before converting
    pub(crate) normalize: bool,
}

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
        binary::encode(&self.0)
    }

    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self) -> ParsedExpr {
        self.0.clone()
    }
}

impl Resolved {
    pub fn typecheck(&self) -> Result<Typed, TypeError> {
        Ok(Typed(crate::semantics::tck::typecheck::typecheck(&self.0)?))
    }
    pub fn typecheck_with(self, ty: &Normalized) -> Result<Typed, TypeError> {
        Ok(Typed(crate::semantics::tck::typecheck::typecheck_with(
            &self.0,
            ty.to_expr(),
        )?))
    }
    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self) -> ResolvedExpr {
        self.0.clone()
    }
    pub fn tck_and_normalize_new_flow(&self) -> Result<Normalized, TypeError> {
        let val = crate::semantics::tck::typecheck::typecheck(&self.0)?
            .normalize_whnf_noenv();
        Ok(Normalized(val))
    }
}

impl Typed {
    /// Reduce an expression to its normal form, performing beta reduction
    pub fn normalize(&self) -> Normalized {
        let mut val = self.0.normalize_whnf_noenv();
        val.normalize_mut();
        Normalized(val)
    }

    /// Converts a value back to the corresponding AST expression.
    fn to_expr(&self) -> ResolvedExpr {
        self.0.to_expr(ToExprOptions {
            alpha: false,
            normalize: false,
        })
    }

    pub(crate) fn get_type(&self) -> Result<Normalized, TypeError> {
        Ok(Normalized(self.0.get_type()?))
    }
}

impl Normalized {
    pub fn encode(&self) -> Result<Vec<u8>, EncodeError> {
        binary::encode(&self.to_expr())
    }

    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self) -> NormalizedExpr {
        self.0.to_expr(ToExprOptions {
            alpha: false,
            normalize: false,
        })
    }
    /// Converts a value back to the corresponding AST expression, alpha-normalizing in the process.
    pub(crate) fn to_expr_alpha(&self) -> NormalizedExpr {
        self.0.to_expr(ToExprOptions {
            alpha: true,
            normalize: false,
        })
    }
    pub(crate) fn to_value(&self) -> Value {
        self.0.clone()
    }
    pub(crate) fn into_value(self) -> Value {
        self.0
    }

    pub(crate) fn from_const(c: Const) -> Self {
        Normalized(Value::from_const(c))
    }
    pub(crate) fn from_kind_and_type(
        v: ValueKind<Value>,
        t: Normalized,
    ) -> Self {
        Normalized(Value::from_kind_and_type(v, t.into_value()))
    }
    pub(crate) fn from_value(th: Value) -> Self {
        Normalized(th)
    }
    pub(crate) fn const_type() -> Self {
        Normalized::from_const(Const::Type)
    }

    pub fn make_builtin_type(b: Builtin) -> Self {
        Normalized::from_value(Value::from_builtin(b))
    }
    pub fn make_optional_type(t: Normalized) -> Self {
        Normalized::from_value(
            Value::from_builtin(Builtin::Optional).app(t.to_value()),
        )
    }
    pub fn make_list_type(t: Normalized) -> Self {
        Normalized::from_value(
            Value::from_builtin(Builtin::List).app(t.to_value()),
        )
    }
    pub fn make_record_type(
        kts: impl Iterator<Item = (String, Normalized)>,
    ) -> Self {
        Normalized::from_kind_and_type(
            ValueKind::RecordType(
                kts.map(|(k, t)| (k.into(), t.into_value())).collect(),
            ),
            Normalized::const_type(),
        )
    }
    pub fn make_union_type(
        kts: impl Iterator<Item = (String, Option<Normalized>)>,
    ) -> Self {
        Normalized::from_kind_and_type(
            ValueKind::UnionType(
                kts.map(|(k, t)| (k.into(), t.map(|t| t.into_value())))
                    .collect(),
            ),
            Normalized::const_type(),
        )
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
