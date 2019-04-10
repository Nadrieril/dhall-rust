use crate::error::*;
use crate::expr::*;
use dhall_core::*;
use dhall_generator::*;
use std::borrow::Cow;

pub trait StaticType {
    fn get_static_type() -> Type;
}

/// Trait for rust types that can be represented in dhall in
/// a single way, independent of the value. A typical example is `Option<bool>`,
/// represented by the dhall expression `Optional Bool`. A typical counterexample
/// is `HashMap<Text, bool>` because dhall cannot represent records with a
/// variable number of fields.
pub trait SimpleStaticType {
    fn get_simple_static_type() -> SimpleType;
}


pub trait Deserialize<'a>: Sized {
    fn from_str(s: &'a str, ty: Option<&Type>) -> Result<Self>;
}

impl<'a> Deserialize<'a> for Parsed {
    /// Simply parses the provided string. Ignores the
    /// provided type.
    fn from_str(s: &'a str, _ty: Option<&Type>) -> Result<Self> {
        Ok(Parsed::parse_str(s).map_err(|_| ())?)
    }
}

impl<'a> Deserialize<'a> for Resolved {
    /// Parses and resolves the provided string. Ignores the
    /// provided type.
    fn from_str(s: &'a str, ty: Option<&Type>) -> Result<Self> {
        Ok(Parsed::from_str(s, ty)?
            .resolve()
            .map_err(|_| ())?
        )
    }
}

impl<'a> Deserialize<'a> for Typed {
    /// Parses, resolves and typechecks the provided string.
    fn from_str(s: &'a str, ty: Option<&Type>) -> Result<Self> {
        // TODO: compare with provided type
        Ok(Resolved::from_str(s, ty)?
            .typecheck()
            .map_err(|_| ())?
        )
    }
}

impl<'a> Deserialize<'a> for Normalized {
    /// Parses, resolves, typechecks and normalizes the provided string.
    fn from_str(s: &'a str, ty: Option<&Type>) -> Result<Self> {
        Ok(Typed::from_str(s, ty)?.normalize())
    }
}

impl<'a> Deserialize<'a> for Type {
    fn from_str(s: &'a str, ty: Option<&Type>) -> Result<Self> {
        Ok(Normalized::from_str(s, ty)?.into_type())
    }
}

fn mktype(x: SubExpr<X, X>) -> SimpleType {
    SimpleType(x)
}

impl<T: SimpleStaticType> StaticType for T {
    fn get_static_type() -> Type {
        crate::expr::Normalized(
            T::get_simple_static_type().into(),
            Type::const_type(),
        )
        .into_type()
    }
}

impl StaticType for SimpleType {
    fn get_static_type() -> Type {
        Type::const_type()
    }
}

impl SimpleStaticType for bool {
    fn get_simple_static_type() -> SimpleType {
        mktype(dhall_expr!(Bool))
    }
}

impl SimpleStaticType for Natural {
    fn get_simple_static_type() -> SimpleType {
        mktype(dhall_expr!(Natural))
    }
}

impl SimpleStaticType for Integer {
    fn get_simple_static_type() -> SimpleType {
        mktype(dhall_expr!(Integer))
    }
}

impl SimpleStaticType for String {
    fn get_simple_static_type() -> SimpleType {
        mktype(dhall_expr!(Text))
    }
}

impl<A: SimpleStaticType, B: SimpleStaticType> SimpleStaticType for (A, B) {
    fn get_simple_static_type() -> SimpleType {
        let ta: SubExpr<_, _> = A::get_simple_static_type().into();
        let tb: SubExpr<_, _> = B::get_simple_static_type().into();
        mktype(dhall_expr!({ _1: ta, _2: tb }))
    }
}

impl<T: SimpleStaticType> SimpleStaticType for Option<T> {
    fn get_simple_static_type() -> SimpleType {
        let t: SubExpr<_, _> = T::get_simple_static_type().into();
        mktype(dhall_expr!(Optional t))
    }
}

impl<T: SimpleStaticType> SimpleStaticType for Vec<T> {
    fn get_simple_static_type() -> SimpleType {
        let t: SubExpr<_, _> = T::get_simple_static_type().into();
        mktype(dhall_expr!(List t))
    }
}

impl<'a, T: SimpleStaticType> SimpleStaticType for &'a T {
    fn get_simple_static_type() -> SimpleType {
        T::get_simple_static_type()
    }
}

impl<T> SimpleStaticType for std::marker::PhantomData<T> {
    fn get_simple_static_type() -> SimpleType {
        mktype(dhall_expr!({}))
    }
}

impl<T: SimpleStaticType, E: SimpleStaticType> SimpleStaticType
    for std::result::Result<T, E>
{
    fn get_simple_static_type() -> SimpleType {
        let tt: SubExpr<_, _> = T::get_simple_static_type().into();
        let te: SubExpr<_, _> = E::get_simple_static_type().into();
        mktype(dhall_expr!(< Ok: tt | Err: te>))
    }
}
