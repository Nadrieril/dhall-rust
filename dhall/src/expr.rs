use crate::imports::ImportRoot;
use crate::normalize::{Thunk, Value};
use dhall_syntax::*;

macro_rules! derive_other_traits {
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

#[derive(Debug, Clone)]
pub(crate) struct Parsed(
    pub(crate) SubExpr<Span, Import>,
    pub(crate) ImportRoot,
);
derive_other_traits!(Parsed);

#[derive(Debug, Clone)]
pub(crate) struct Resolved(pub(crate) SubExpr<Span, Normalized>);
derive_other_traits!(Resolved);

pub(crate) use self::typed::TypedInternal;

#[derive(Debug, Clone)]
pub(crate) struct Typed(pub(crate) TypedInternal);

#[derive(Debug, Clone)]
pub(crate) struct Normalized(pub(crate) TypedInternal);

impl std::cmp::PartialEq for Normalized {
    fn eq(&self, other: &Self) -> bool {
        self.to_expr() == other.to_expr()
    }
}

impl std::cmp::Eq for Normalized {}

impl std::fmt::Display for Normalized {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.to_expr().fmt(f)
    }
}

mod typed {
    use super::{Type, Typed};
    use crate::normalize::{DoubleVar, Thunk, Value};
    use crate::typecheck::{
        TypeError, TypeInternal, TypeMessage, TypecheckContext,
    };
    use dhall_syntax::{Const, SubExpr, X};
    use std::borrow::Cow;

    #[derive(Debug, Clone)]
    pub(crate) enum TypedInternal {
        // The `Sort` higher-kinded type doesn't have a type
        Sort,
        // Any other value, along with its type
        Value(Thunk, Option<Type>),
    }

    impl TypedInternal {
        pub(crate) fn from_thunk_and_type(th: Thunk, t: Type) -> Self {
            TypedInternal::Value(th, Some(t))
        }

        pub(crate) fn from_thunk_untyped(th: Thunk) -> Self {
            TypedInternal::Value(th, None)
        }

        // TODO: Avoid cloning if possible
        pub(crate) fn to_value(&self) -> Value {
            match self {
                TypedInternal::Value(th, _) => th.to_value(),
                TypedInternal::Sort => Value::Const(Const::Sort),
            }
        }

        pub(crate) fn to_expr(&self) -> SubExpr<X, X> {
            self.to_value().normalize_to_expr()
        }

        pub(crate) fn to_expr_alpha(&self) -> SubExpr<X, X> {
            self.to_value().normalize_to_expr_maybe_alpha(true)
        }

        pub(crate) fn to_thunk(&self) -> Thunk {
            match self {
                TypedInternal::Value(th, _) => th.clone(),
                TypedInternal::Sort => {
                    Thunk::from_value(Value::Const(Const::Sort))
                }
            }
        }

        pub(crate) fn to_type(&self) -> Type {
            match self {
                TypedInternal::Sort => Type(TypeInternal::Const(Const::Sort)),
                TypedInternal::Value(th, _) => match &*th.as_value() {
                    Value::Const(c) => Type(TypeInternal::Const(*c)),
                    _ => {
                        Type(TypeInternal::Typed(Box::new(Typed(self.clone()))))
                    }
                },
            }
        }

        pub(crate) fn get_type(&self) -> Result<Cow<'_, Type>, TypeError> {
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

        pub(crate) fn shift(&self, delta: isize, var: &DoubleVar) -> Self {
            match self {
                TypedInternal::Value(th, t) => TypedInternal::Value(
                    th.shift(delta, var),
                    t.as_ref().map(|x| x.shift(delta, var)),
                ),
                TypedInternal::Sort => TypedInternal::Sort,
            }
        }

        pub(crate) fn subst_shift(&self, var: &DoubleVar, val: &Typed) -> Self {
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
pub struct SimpleType(pub(crate) SubExpr<X, X>);
derive_other_traits!(SimpleType);

pub(crate) use crate::typecheck::TypeInternal;

/// A Dhall expression representing a (possibly higher-kinded) type.
///
/// This includes [SimpleType]s but also higher-kinded expressions like
/// `Type`, `Kind` and `{ x: Type }`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type(pub(crate) TypeInternal);

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.to_normalized().fmt(f)
    }
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
        Typed(x.0)
    }
}

impl Normalized {
    pub(crate) fn from_thunk_and_type(th: Thunk, t: Type) -> Self {
        Normalized(TypedInternal::from_thunk_and_type(th, t))
    }
    pub(crate) fn to_expr(&self) -> SubExpr<X, X> {
        self.0.to_expr()
    }
    #[allow(dead_code)]
    pub(crate) fn to_expr_alpha(&self) -> SubExpr<X, X> {
        self.0.to_expr_alpha()
    }
    pub(crate) fn to_value(&self) -> Value {
        self.0.to_value()
    }
    pub(crate) fn to_thunk(&self) -> Thunk {
        self.0.to_thunk()
    }
}

impl Typed {
    pub(crate) fn from_thunk_and_type(th: Thunk, t: Type) -> Self {
        Typed(TypedInternal::from_thunk_and_type(th, t))
    }
    pub(crate) fn from_thunk_untyped(th: Thunk) -> Self {
        Typed(TypedInternal::from_thunk_untyped(th))
    }
    pub(crate) fn const_sort() -> Self {
        Typed(TypedInternal::Sort)
    }
}
