use crate::imports::ImportRoot;
use crate::normalize::{Thunk, Value};
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

pub(crate) use self::typed::TypedInternal;

#[derive(Debug, Clone)]
pub(crate) struct Typed<'a>(
    pub(crate) TypedInternal,
    pub(crate) PhantomData<&'a ()>,
);

#[derive(Debug, Clone)]
pub(crate) struct Normalized<'a>(
    pub(crate) TypedInternal,
    pub(crate) PhantomData<&'a ()>,
);

impl<'a> std::cmp::PartialEq for Normalized<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.to_expr() == other.to_expr()
    }
}

impl<'a> std::cmp::Eq for Normalized<'a> {}

impl<'a> std::fmt::Display for Normalized<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.to_expr().fmt(f)
    }
}

mod typed {
    use super::{Type, Typed};
    use crate::normalize::{Thunk, Value};
    use crate::typecheck::{
        TypeError, TypeInternal, TypeMessage, TypecheckContext,
    };
    use dhall_core::{Const, Label, SubExpr, V, X};
    use std::borrow::Cow;
    use std::marker::PhantomData;

    #[derive(Debug, Clone)]
    pub(crate) enum TypedInternal {
        // The `Sort` higher-kinded type doesn't have a type
        Sort,
        // Any other value, along with its type
        Value(Thunk, Option<Type<'static>>),
    }

    impl TypedInternal {
        pub(crate) fn from_thunk_and_type(th: Thunk, t: Type<'static>) -> Self {
            TypedInternal::Value(th, Some(t))
        }

        pub(crate) fn from_thunk_untyped(th: Thunk) -> Self {
            TypedInternal::Value(th, None)
        }

        // TODO: Avoid cloning if possible
        pub(crate) fn to_value(&self) -> Value {
            match self {
                TypedInternal::Value(th, _) => th.normalize_whnf().clone(),
                TypedInternal::Sort => Value::Const(Const::Sort),
            }
        }

        pub(crate) fn to_expr(&self) -> SubExpr<X, X> {
            self.to_value().normalize_to_expr()
        }

        pub(crate) fn to_thunk(&self) -> Thunk {
            match self {
                TypedInternal::Value(th, _) => th.clone(),
                TypedInternal::Sort => {
                    Thunk::from_whnf(Value::Const(Const::Sort))
                }
            }
        }

        pub(crate) fn to_type(&self) -> Type<'static> {
            match self {
                TypedInternal::Sort => Type(TypeInternal::Const(Const::Sort)),
                TypedInternal::Value(th, _) => match &*th.normalize_whnf() {
                    Value::Const(c) => Type(TypeInternal::Const(*c)),
                    _ => Type(TypeInternal::Typed(Box::new(Typed(
                        self.clone(),
                        PhantomData,
                    )))),
                },
            }
        }

        pub(crate) fn get_type(
            &self,
        ) -> Result<Cow<'_, Type<'static>>, TypeError> {
            match self {
                TypedInternal::Value(_, Some(t)) => Ok(Cow::Borrowed(t)),
                TypedInternal::Value(_, None) => Err(TypeError::new(
                    &TypecheckContext::new(),
                    TypeMessage::Untyped,
                )),
                TypedInternal::Sort => Err(TypeError::new(
                    &TypecheckContext::new(),
                    TypeMessage::Sort,
                )),
            }
        }

        pub(crate) fn shift(&self, delta: isize, var: &V<Label>) -> Self {
            match self {
                TypedInternal::Value(th, t) => TypedInternal::Value(
                    th.shift(delta, var),
                    t.as_ref().map(|x| x.shift(delta, var)),
                ),
                TypedInternal::Sort => TypedInternal::Sort,
            }
        }

        pub(crate) fn subst_shift(
            &self,
            var: &V<Label>,
            val: &Typed<'static>,
        ) -> Self {
            match self {
                TypedInternal::Value(th, t) => TypedInternal::Value(
                    th.subst_shift(var, val),
                    t.as_ref().map(|x| x.subst_shift(var, val)),
                ),
                TypedInternal::Sort => TypedInternal::Sort,
            }
        }
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
        self.to_normalized().fmt(f)
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
        Typed(x.0, x.1)
    }
}

impl<'a> Normalized<'a> {
    pub(crate) fn from_thunk_and_type(th: Thunk, t: Type<'static>) -> Self {
        Normalized(TypedInternal::from_thunk_and_type(th, t), PhantomData)
    }
    // Deprecated
    pub(crate) fn as_expr(&self) -> SubExpr<X, X> {
        self.0.to_expr()
    }
    pub(crate) fn to_expr(&self) -> SubExpr<X, X> {
        self.0.to_expr()
    }
    pub(crate) fn to_value(&self) -> Value {
        self.0.to_value()
    }
    #[allow(dead_code)]
    pub(crate) fn unnote<'b>(self) -> Normalized<'b> {
        Normalized(self.0, PhantomData)
    }
}

impl<'a> Typed<'a> {
    pub(crate) fn from_thunk_and_type(th: Thunk, t: Type<'static>) -> Self {
        Typed(TypedInternal::from_thunk_and_type(th, t), PhantomData)
    }
    pub(crate) fn from_thunk_untyped(th: Thunk) -> Self {
        Typed(TypedInternal::from_thunk_untyped(th), PhantomData)
    }
    pub(crate) fn const_sort() -> Self {
        Typed(TypedInternal::Sort, PhantomData)
    }
}
