use crate::expr::*;
use dhall_core::*;
use dhall_generator as dhall;

/// A value that has a statically-known Dhall type.
///
/// This trait is strictly more general than [SimpleStaticType].
/// The reason is that it allows an arbitrary [Type] to be returned
/// instead of just a [SimpleType].
///
/// For now the only interesting impl is [SimpleType] itself, who
/// has a statically-known type which is not itself a [SimpleType].
pub trait StaticType {
    fn get_static_type() -> Type<'static>;
}

/// A Rust type that can be represented as a Dhall type.
///
/// A typical example is `Option<bool>`,
/// represented by the dhall expression `Optional Bool`.
///
/// This trait can and should be automatically derived.
///
/// The representation needs to be independent of the value.
/// For this reason, something like `HashMap<String, bool>` cannot implement
/// [SimpleStaticType] because each different value would
/// have a different Dhall record type.
///
/// The `Simple` in `SimpleStaticType` indicates that the returned type is
/// a [SimpleType].
pub trait SimpleStaticType {
    fn get_simple_static_type<'a>() -> SimpleType<'a>;
}

fn mktype<'a>(x: SubExpr<X, X>) -> SimpleType<'a> {
    x.into()
}

impl<T: SimpleStaticType> StaticType for T {
    fn get_static_type() -> Type<'static> {
        crate::expr::Normalized(
            T::get_simple_static_type().into(),
            Some(Type::const_type()),
            std::marker::PhantomData,
        )
        .into_type()
        .unwrap()
    }
}

impl<'a> StaticType for SimpleType<'a> {
    /// By definition, a [SimpleType] has type `Type`.
    /// This returns the Dhall expression `Type`
    fn get_static_type() -> Type<'static> {
        Type::const_type()
    }
}

impl SimpleStaticType for bool {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        mktype(dhall::subexpr!(Bool))
    }
}

impl SimpleStaticType for Natural {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        mktype(dhall::subexpr!(Natural))
    }
}

impl SimpleStaticType for u32 {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        mktype(dhall::subexpr!(Natural))
    }
}

impl SimpleStaticType for u64 {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        mktype(dhall::subexpr!(Natural))
    }
}

impl SimpleStaticType for Integer {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        mktype(dhall::subexpr!(Integer))
    }
}

impl SimpleStaticType for i32 {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        mktype(dhall::subexpr!(Integer))
    }
}

impl SimpleStaticType for i64 {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        mktype(dhall::subexpr!(Integer))
    }
}

impl SimpleStaticType for String {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        mktype(dhall::subexpr!(Text))
    }
}

impl<A: SimpleStaticType, B: SimpleStaticType> SimpleStaticType for (A, B) {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        let ta: SubExpr<_, _> = A::get_simple_static_type().into();
        let tb: SubExpr<_, _> = B::get_simple_static_type().into();
        mktype(dhall::subexpr!({ _1: ta, _2: tb }))
    }
}

impl<T: SimpleStaticType> SimpleStaticType for Option<T> {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        let t: SubExpr<_, _> = T::get_simple_static_type().into();
        mktype(dhall::subexpr!(Optional t))
    }
}

impl<T: SimpleStaticType> SimpleStaticType for Vec<T> {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        let t: SubExpr<_, _> = T::get_simple_static_type().into();
        mktype(dhall::subexpr!(List t))
    }
}

impl<'a, T: SimpleStaticType> SimpleStaticType for &'a T {
    fn get_simple_static_type<'b>() -> SimpleType<'b> {
        T::get_simple_static_type()
    }
}

impl<T> SimpleStaticType for std::marker::PhantomData<T> {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        mktype(dhall::subexpr!({}))
    }
}

impl<T: SimpleStaticType, E: SimpleStaticType> SimpleStaticType
    for std::result::Result<T, E>
{
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        let tt: SubExpr<_, _> = T::get_simple_static_type().into();
        let te: SubExpr<_, _> = E::get_simple_static_type().into();
        mktype(dhall::subexpr!(< Ok: tt | Err: te>))
    }
}
