use crate::imports::ImportRoot;
use dhall_core::*;
use std::marker::PhantomData;

macro_rules! derive_other_traits {
    ($ty:ident) => {
        impl std::cmp::PartialEq for $ty {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

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

macro_rules! derive_other_traits_ {
    ($ty:ident) => {
        impl<'a> std::cmp::PartialEq for $ty<'a> {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl<'a> std::fmt::Display for $ty<'a> {
            fn fmt(
                &self,
                f: &mut std::fmt::Formatter,
            ) -> Result<(), std::fmt::Error> {
                self.0.fmt(f)
            }
        }
    };
}

#[derive(Debug, Clone, Eq)]
pub struct Parsed<'a>(
    pub(crate) SubExpr<X, Import>,
    pub(crate) ImportRoot,
    pub(crate) PhantomData<&'a ()>,
);
derive_other_traits_!(Parsed);

#[derive(Debug, Clone, Eq)]
pub struct Resolved<'a>(
    pub(crate) SubExpr<X, Normalized>,
    pub(crate) PhantomData<&'a ()>,
);
derive_other_traits_!(Resolved);

#[derive(Debug, Clone, Eq)]
pub struct Typed(pub(crate) SubExpr<X, Normalized>, pub(crate) Option<Type>);
derive_other_traits!(Typed);

#[derive(Debug, Clone, Eq)]
pub struct Normalized(pub(crate) SubExpr<X, X>, pub(crate) Option<Type>);
derive_other_traits!(Normalized);

/// An expression of type `Type` (like `Bool` or `Natural -> Text`, but not `Type`)
#[derive(Debug, Clone, Eq)]
pub struct SimpleType(pub(crate) SubExpr<X, X>);
derive_other_traits!(SimpleType);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type(pub(crate) TypeInternal);

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TypeInternal {
    Expr(Box<Normalized>),
    // The type of `Sort`
    SuperType,
}

// Exposed for the macros
#[doc(hidden)]
impl From<SimpleType> for SubExpr<X, X> {
    fn from(x: SimpleType) -> SubExpr<X, X> {
        x.0
    }
}

// Exposed for the macros
#[doc(hidden)]
impl From<SubExpr<X, X>> for SimpleType {
    fn from(x: SubExpr<X, X>) -> SimpleType {
        SimpleType(x)
    }
}

// Exposed for the macros
#[doc(hidden)]
impl From<Normalized> for Typed {
    fn from(x: Normalized) -> Typed {
        Typed(x.0.absurd(), x.1)
    }
}

impl Typed {
    pub(crate) fn as_expr(&self) -> &SubExpr<X, Normalized> {
        &self.0
    }
    pub(crate) fn into_expr(self) -> SubExpr<X, Normalized> {
        self.0
    }
}

impl Normalized {
    pub(crate) fn as_expr(&self) -> &SubExpr<X, X> {
        &self.0
    }
    pub(crate) fn into_expr<T>(self) -> SubExpr<X, T> {
        self.0.absurd()
    }
    pub(crate) fn into_type(self) -> Type {
        crate::expr::Type(TypeInternal::Expr(Box::new(self)))
    }
}

impl SimpleType {
    pub(crate) fn into_type(self) -> Type {
        Normalized(self.0, Some(Type::const_type())).into_type()
    }
}
