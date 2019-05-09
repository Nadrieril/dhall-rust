use std::borrow::Cow;
use std::fmt::Display;
use std::path::Path;

use dhall_syntax::{Const, Import, Span, SubExpr, X};

use crate::core::context::TypecheckContext;
use crate::core::thunk::Thunk;
use crate::core::value::Value;
use crate::core::var::{AlphaVar, Shift, Subst};
use crate::error::{Error, ImportError, TypeError, TypeMessage};

use resolve::ImportRoot;
use typecheck::type_of_const;

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
    // Any value, along with (optionally) its type
    Untyped(Thunk),
    Typed(Thunk, Box<Type>),
    // One of the base higher-kinded typed.
    // Used to avoid storing the same tower ot Type->Kind->Sort
    // over and over again. Also enables having Sort as a type
    // even though it doesn't itself have a type.
    Const(Const),
}

/// A normalized expression.
///
/// Invariant: the contained Typed expression must be in normal form,
#[derive(Debug, Clone)]
pub(crate) struct Normalized(pub(crate) Typed);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type(pub(crate) Typed);

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
            Typed::Const(_) => {}
            Typed::Untyped(thunk) | Typed::Typed(thunk, _) => {
                thunk.normalize_nf();
            }
        }
        Normalized(self)
    }

    pub(crate) fn from_thunk_and_type(th: Thunk, t: Type) -> Self {
        Typed::Typed(th, Box::new(t))
    }
    pub(crate) fn from_thunk_untyped(th: Thunk) -> Self {
        Typed::Untyped(th)
    }
    pub(crate) fn from_const(c: Const) -> Self {
        Typed::Const(c)
    }
    pub(crate) fn from_value_untyped(v: Value) -> Self {
        Typed::Untyped(Thunk::from_value(v))
    }
    pub(crate) fn from_normalized_expr_untyped(e: NormalizedSubExpr) -> Self {
        Typed::from_thunk_untyped(Thunk::from_normalized_expr(e))
    }

    // TODO: Avoid cloning if possible
    pub(crate) fn to_value(&self) -> Value {
        match self {
            Typed::Untyped(th) | Typed::Typed(th, _) => th.to_value(),
            Typed::Const(c) => Value::Const(*c),
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
            Typed::Untyped(th) | Typed::Typed(th, _) => th.clone(),
            Typed::Const(c) => Thunk::from_value(Value::Const(*c)),
        }
    }
    // Deprecated
    pub(crate) fn to_type(&self) -> Type {
        self.clone().into_type()
    }
    pub(crate) fn into_type(self) -> Type {
        Type(self)
    }

    pub(crate) fn normalize_mut(&mut self) {
        match self {
            Typed::Untyped(th) | Typed::Typed(th, _) => th.normalize_mut(),
            Typed::Const(_) => {}
        }
    }

    pub(crate) fn get_type(&self) -> Result<Cow<'_, Type>, TypeError> {
        match self {
            Typed::Untyped(_) => Err(TypeError::new(
                &TypecheckContext::new(),
                TypeMessage::Untyped,
            )),
            Typed::Typed(_, t) => Ok(Cow::Borrowed(t)),
            Typed::Const(c) => Ok(Cow::Owned(type_of_const(*c)?)),
        }
    }
}

impl Type {
    // Deprecated
    pub(crate) fn to_normalized(&self) -> Normalized {
        self.0.clone().normalize()
    }
    pub(crate) fn to_expr(&self) -> NormalizedSubExpr {
        self.0.to_expr()
    }
    pub(crate) fn to_value(&self) -> Value {
        self.0.to_value()
    }
    pub(crate) fn to_typed(&self) -> Typed {
        self.0.clone()
    }
    pub(crate) fn as_const(&self) -> Option<Const> {
        // TODO: avoid clone
        match &self.to_value() {
            Value::Const(c) => Some(*c),
            _ => None,
        }
    }
    pub(crate) fn get_type(&self) -> Result<Cow<'_, Type>, TypeError> {
        self.0.get_type()
    }

    pub(crate) fn from_const(c: Const) -> Self {
        Type(Typed::from_const(c))
    }
}

impl Normalized {
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
    pub(crate) fn to_type(&self) -> Type {
        self.0.to_type()
    }
    pub(crate) fn into_typed(self) -> Typed {
        self.0
    }
    pub(crate) fn get_type(&self) -> Result<Cow<'_, Type>, TypeError> {
        self.0.get_type()
    }
}

impl Shift for Typed {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(match self {
            Typed::Untyped(th) => Typed::Untyped(th.shift(delta, var)?),
            Typed::Typed(th, t) => Typed::Typed(
                th.shift(delta, var)?,
                Box::new(t.shift(delta, var)?),
            ),
            Typed::Const(c) => Typed::Const(*c),
        })
    }
}

impl Shift for Type {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(Type(self.0.shift(delta, var)?))
    }
}

impl Shift for Normalized {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(Normalized(self.0.shift(delta, var)?))
    }
}

impl Subst<Typed> for Typed {
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        match self {
            Typed::Untyped(th) => Typed::Untyped(th.subst_shift(var, val)),
            Typed::Typed(th, t) => Typed::Typed(
                th.subst_shift(var, val),
                Box::new(t.subst_shift(var, val)),
            ),
            Typed::Const(c) => Typed::Const(*c),
        }
    }
}

impl Subst<Typed> for Type {
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        Type(self.0.subst_shift(var, val))
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

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.to_normalized().fmt(f)
    }
}
