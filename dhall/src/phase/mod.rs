use std::borrow::Cow;
use std::fmt::Display;
use std::path::Path;

use dhall_syntax::{Const, Import, Span, SubExpr, X};

use crate::error::Error;

use normalize::{AlphaVar, Thunk, Value};
use resolve::{ImportError, ImportRoot};
use typecheck::{
    const_to_typed, type_of_const, TypeError, TypeMessage, TypecheckContext,
};

pub(crate) mod binary;
pub(crate) mod normalize;
pub(crate) mod parse;
pub(crate) mod resolve;
pub(crate) mod typecheck;

pub(crate) type ParsedSubExpr = SubExpr<Span, Import>;
pub(crate) type ResolvedSubExpr = SubExpr<Span, Normalized>;
pub(crate) type NormalizedSubExpr = SubExpr<X, X>;

#[derive(Debug, Clone)]
pub(crate) struct Parsed(pub(crate) ParsedSubExpr, pub(crate) ImportRoot);

/// An expression where all imports have been resolved
#[derive(Debug, Clone)]
pub(crate) struct Resolved(pub(crate) ResolvedSubExpr);

/// A typed expression
#[derive(Debug, Clone)]
pub(crate) enum Typed {
    // The `Sort` higher-kinded type; it doesn't have a type
    Sort,
    // Any other value, along with (optionally) its type
    Value(Thunk, Option<Type>),
}

/// A normalized expression.
///
/// Invariant: the contained Typed expression must be in normal form,
#[derive(Debug, Clone)]
pub(crate) struct Normalized(pub(crate) Typed);

/// A Dhall expression representing a simple type.
///
/// This captures what is usually simply called a "type", like
/// `Bool`, `{ x: Integer }` or `Natural -> Text`.
///
/// For a more general notion of "type", see [Type].
#[derive(Debug, Clone)]
pub struct SimpleType(pub(crate) NormalizedSubExpr);

/// A Dhall expression representing a (possibly higher-kinded) type.
///
/// This includes [SimpleType]s but also higher-kinded expressions like
/// `Type`, `Kind` and `{ x: Type }`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type(pub(crate) TypeInternal);

#[derive(Debug, Clone)]
pub(crate) enum TypeInternal {
    Const(Const),
    /// This must not contain a Const value.
    Typed(Box<Typed>),
}

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

    pub fn resolve(self) -> Result<Resolved, ImportError> {
        resolve::resolve(self)
    }

    #[allow(dead_code)]
    pub fn skip_resolve(self) -> Result<Resolved, ImportError> {
        resolve::skip_resolve_expr(self)
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
    pub fn normalize(self) -> Normalized {
        match &self {
            Typed::Sort => {}
            Typed::Value(thunk, _) => {
                thunk.normalize_nf();
            }
        }
        Normalized(self)
    }

    pub(crate) fn from_thunk_and_type(th: Thunk, t: Type) -> Self {
        Typed::Value(th, Some(t))
    }
    pub(crate) fn from_thunk_untyped(th: Thunk) -> Self {
        Typed::Value(th, None)
    }

    // TODO: Avoid cloning if possible
    pub(crate) fn to_value(&self) -> Value {
        match self {
            Typed::Value(th, _) => th.to_value(),
            Typed::Sort => Value::Const(Const::Sort),
        }
    }
    pub(crate) fn to_expr(&self) -> NormalizedSubExpr {
        self.to_value().normalize_to_expr()
    }
    pub(crate) fn to_expr_alpha(&self) -> NormalizedSubExpr {
        self.to_value().normalize_to_expr_maybe_alpha(true)
    }
    pub(crate) fn to_thunk(&self) -> Thunk {
        match self {
            Typed::Value(th, _) => th.clone(),
            Typed::Sort => Thunk::from_value(Value::Const(Const::Sort)),
        }
    }
    pub(crate) fn to_type(&self) -> Type {
        match self {
            Typed::Sort => Type(TypeInternal::Const(Const::Sort)),
            Typed::Value(th, _) => match &*th.as_value() {
                Value::Const(c) => Type(TypeInternal::Const(*c)),
                _ => Type(TypeInternal::Typed(Box::new(self.clone()))),
            },
        }
    }

    pub(crate) fn get_type(&self) -> Result<Cow<'_, Type>, TypeError> {
        match self {
            Typed::Value(_, Some(t)) => Ok(Cow::Borrowed(t)),
            Typed::Value(_, None) => Err(TypeError::new(
                &TypecheckContext::new(),
                TypeMessage::Untyped,
            )),
            Typed::Sort => {
                Err(TypeError::new(&TypecheckContext::new(), TypeMessage::Sort))
            }
        }
    }

    pub(crate) fn const_sort() -> Self {
        Typed::Sort
    }

    pub(crate) fn shift(&self, delta: isize, var: &AlphaVar) -> Self {
        match self {
            Typed::Value(th, t) => Typed::Value(
                th.shift(delta, var),
                t.as_ref().map(|x| x.shift(delta, var)),
            ),
            Typed::Sort => Typed::Sort,
        }
    }

    pub(crate) fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        match self {
            Typed::Value(th, t) => Typed::Value(
                th.subst_shift(var, val),
                t.as_ref().map(|x| x.subst_shift(var, val)),
            ),
            Typed::Sort => Typed::Sort,
        }
    }
}

impl Type {
    pub(crate) fn to_normalized(&self) -> Normalized {
        self.0.to_normalized()
    }
    pub(crate) fn to_expr(&self) -> NormalizedSubExpr {
        self.0.to_expr()
    }
    pub(crate) fn to_value(&self) -> Value {
        self.0.to_value()
    }
    pub(crate) fn as_const(&self) -> Option<Const> {
        self.0.as_const()
    }
    pub(crate) fn internal_whnf(&self) -> Option<Value> {
        self.0.whnf()
    }
    pub(crate) fn get_type(&self) -> Result<Cow<'_, Type>, TypeError> {
        self.0.get_type()
    }

    pub(crate) fn const_sort() -> Self {
        Type(TypeInternal::Const(Const::Sort))
    }
    pub(crate) fn const_kind() -> Self {
        Type(TypeInternal::Const(Const::Kind))
    }
    pub(crate) fn const_type() -> Self {
        Type(TypeInternal::Const(Const::Type))
    }

    pub(crate) fn shift(&self, delta: isize, var: &AlphaVar) -> Self {
        Type(self.0.shift(delta, var))
    }
    pub(crate) fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        Type(self.0.subst_shift(var, val))
    }
}

impl TypeInternal {
    pub(crate) fn to_typed(&self) -> Typed {
        match self {
            TypeInternal::Typed(e) => e.as_ref().clone(),
            TypeInternal::Const(c) => const_to_typed(*c),
        }
    }
    pub(crate) fn to_normalized(&self) -> Normalized {
        self.to_typed().normalize()
    }
    pub(crate) fn to_expr(&self) -> NormalizedSubExpr {
        self.to_normalized().to_expr()
    }
    pub(crate) fn to_value(&self) -> Value {
        self.to_typed().to_value()
    }
    pub(crate) fn get_type(&self) -> Result<Cow<'_, Type>, TypeError> {
        Ok(match self {
            TypeInternal::Typed(e) => e.get_type()?,
            TypeInternal::Const(c) => Cow::Owned(type_of_const(*c)?),
        })
    }
    pub(crate) fn as_const(&self) -> Option<Const> {
        match self {
            TypeInternal::Const(c) => Some(*c),
            _ => None,
        }
    }
    pub(crate) fn whnf(&self) -> Option<Value> {
        match self {
            TypeInternal::Typed(e) => Some(e.to_value()),
            _ => None,
        }
    }
    pub(crate) fn shift(&self, delta: isize, var: &AlphaVar) -> Self {
        use TypeInternal::*;
        match self {
            Typed(e) => Typed(Box::new(e.shift(delta, var))),
            Const(c) => Const(*c),
        }
    }
    pub(crate) fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        use TypeInternal::*;
        match self {
            Typed(e) => Typed(Box::new(e.subst_shift(var, val))),
            Const(c) => Const(*c),
        }
    }
}

impl Normalized {
    pub(crate) fn from_thunk_and_type(th: Thunk, t: Type) -> Self {
        Normalized(Typed::from_thunk_and_type(th, t))
    }

    pub(crate) fn to_expr(&self) -> NormalizedSubExpr {
        self.0.to_expr()
    }
    #[allow(dead_code)]
    pub(crate) fn to_expr_alpha(&self) -> NormalizedSubExpr {
        self.0.to_expr_alpha()
    }
    pub(crate) fn to_value(&self) -> Value {
        self.0.to_value()
    }
    pub(crate) fn to_thunk(&self) -> Thunk {
        self.0.to_thunk()
    }
    pub(crate) fn to_type(self) -> Type {
        self.0.to_type()
    }
    pub(crate) fn shift(&self, delta: isize, var: &AlphaVar) -> Self {
        Normalized(self.0.shift(delta, var))
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
derive_traits_for_wrapper_struct!(SimpleType);

impl Eq for Typed {}
impl PartialEq for Typed {
    fn eq(&self, other: &Self) -> bool {
        self.to_value() == other.to_value()
    }
}

impl Eq for TypeInternal {}
impl PartialEq for TypeInternal {
    fn eq(&self, other: &Self) -> bool {
        self.to_normalized() == other.to_normalized()
    }
}

impl Display for Typed {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.to_expr().fmt(f)
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.to_normalized().fmt(f)
    }
}

// Exposed for the macros
#[doc(hidden)]
impl From<SimpleType> for NormalizedSubExpr {
    fn from(x: SimpleType) -> NormalizedSubExpr {
        x.0
    }
}

// Exposed for the macros
#[doc(hidden)]
impl From<NormalizedSubExpr> for SimpleType {
    fn from(x: NormalizedSubExpr) -> SimpleType {
        SimpleType(x)
    }
}

// Exposed for the macros
#[doc(hidden)]
impl From<Normalized> for Typed {
    fn from(x: Normalized) -> Typed {
        x.0
    }
}
