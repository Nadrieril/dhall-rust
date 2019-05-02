use crate::imports::ImportRoot;
use dhall_core::*;
use std::marker::PhantomData;

macro_rules! derive_other_traits {
    ($ty:ident) => {
        impl<'a> std::cmp::PartialEq for $ty<'a> {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl<'a> std::cmp::Eq for $ty<'a> {}

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

#[derive(Debug, Clone)]
pub(crate) struct Parsed<'a>(
    pub(crate) SubExpr<Span<'a>, Import>,
    pub(crate) ImportRoot,
);
derive_other_traits!(Parsed);

#[derive(Debug, Clone)]
pub(crate) struct Resolved<'a>(
    pub(crate) SubExpr<Span<'a>, Normalized<'static>>,
);
derive_other_traits!(Resolved);

#[derive(Debug, Clone)]
pub(crate) struct Typed<'a>(
    pub(crate) crate::normalize::Thunk,
    pub(crate) Option<Type<'static>>,
    pub(crate) PhantomData<&'a ()>,
);

#[derive(Debug, Clone)]
pub(crate) struct Normalized<'a>(
    pub(crate) crate::normalize::Thunk,
    pub(crate) Option<Type<'static>>,
    pub(crate) PhantomData<&'a ()>,
);

impl<'a> std::cmp::PartialEq for Normalized<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.0.normalize_to_expr() == other.0.normalize_to_expr()
    }
}

impl<'a> std::cmp::Eq for Normalized<'a> {}

impl<'a> std::fmt::Display for Normalized<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.0.normalize_to_expr().fmt(f)
    }
}

/// A Dhall expression representing a simple type.
///
/// This captures what is usually simply called a "type", like
/// `Bool`, `{ x: Integer }` or `Natural -> Text`.
///
/// For a more general notion of "type", see [Type].
#[derive(Debug, Clone)]
pub struct SimpleType<'a>(
    pub(crate) SubExpr<X, X>,
    pub(crate) PhantomData<&'a ()>,
);
derive_other_traits!(SimpleType);

pub(crate) use crate::typecheck::TypeInternal;

/// A Dhall expression representing a (possibly higher-kinded) type.
///
/// This includes [SimpleType]s but also higher-kinded expressions like
/// `Type`, `Kind` and `{ x: Type }`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type<'a>(pub(crate) TypeInternal<'a>);

impl<'a> std::fmt::Display for Type<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self.0.clone().into_normalized() {
            Ok(e) => e.fmt(f),
            Err(_) => write!(f, "SuperType"),
        }
    }
}

// Exposed for the macros
#[doc(hidden)]
impl<'a> From<SimpleType<'a>> for SubExpr<X, X> {
    fn from(x: SimpleType<'a>) -> SubExpr<X, X> {
        x.0
    }
}

// Exposed for the macros
#[doc(hidden)]
impl<'a> From<SubExpr<X, X>> for SimpleType<'a> {
    fn from(x: SubExpr<X, X>) -> SimpleType<'a> {
        SimpleType(x, PhantomData)
    }
}

// Exposed for the macros
#[doc(hidden)]
impl<'a> From<Normalized<'a>> for Typed<'a> {
    fn from(x: Normalized<'a>) -> Typed<'a> {
        Typed(x.0, x.1, x.2)
    }
}

impl<'a> Normalized<'a> {
    // Deprecated
    pub(crate) fn as_expr(&self) -> SubExpr<X, X> {
        self.0.normalize_to_expr()
    }
    pub(crate) fn to_expr(&self) -> SubExpr<X, X> {
        self.0.normalize_to_expr()
    }
    pub(crate) fn to_value(&self) -> crate::normalize::Value {
        self.0.normalize_nf().clone()
    }
    #[allow(dead_code)]
    pub(crate) fn unnote<'b>(self) -> Normalized<'b> {
        Normalized(self.0, self.1, PhantomData)
    }
}

#[doc(hidden)]
impl<'a> Type<'a> {
    pub(crate) fn unnote<'b>(self) -> Type<'b> {
        // use TypeInternal::*;
        // Type(match self.0 {
        //     Expr(e) => Expr(Box::new(e.unnote())),
        //     Pi(ctx, c, x, t, e) => Pi(ctx, c, x, t, e),
        //     Const(c) => Const(c),
        //     SuperType => SuperType,
        // })

        // Yes, this is positively horrible. Please forgive me.
        unsafe { std::mem::transmute::<Type<'a>, Type<'b>>(self) }
    }
}
