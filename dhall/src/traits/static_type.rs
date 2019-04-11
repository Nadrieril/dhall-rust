use crate::expr::*;
use dhall_core::*;
use dhall_generator::*;

pub trait StaticType {
    fn get_static_type() -> Type<'static>;
}

/// Trait for rust types that can be represented in dhall in
/// a single way, independent of the value. A typical example is `Option<bool>`,
/// represented by the dhall expression `Optional Bool`. A typical counterexample
/// is `HashMap<Text, bool>` because dhall cannot represent records with a
/// variable number of fields.
pub trait SimpleStaticType {
    fn get_simple_static_type<'a>() -> SimpleType<'a>;
}

fn mktype<'a>(x: SubExpr<X, X>) -> SimpleType<'a> {
    SimpleType(x, std::marker::PhantomData)
}

impl<T: SimpleStaticType> StaticType for T {
    fn get_static_type() -> Type<'static> {
        crate::expr::Normalized(
            T::get_simple_static_type().into(),
            Some(Type::const_type()),
            std::marker::PhantomData,
        )
        .into_type()
    }
}

impl<'a> StaticType for SimpleType<'a> {
    fn get_static_type() -> Type<'static> {
        Type::const_type()
    }
}

impl SimpleStaticType for bool {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        mktype(dhall_expr!(Bool))
    }
}

impl SimpleStaticType for Natural {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        mktype(dhall_expr!(Natural))
    }
}

impl SimpleStaticType for u32 {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        mktype(dhall_expr!(Natural))
    }
}

impl SimpleStaticType for u64 {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        mktype(dhall_expr!(Natural))
    }
}

impl SimpleStaticType for Integer {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        mktype(dhall_expr!(Integer))
    }
}

impl SimpleStaticType for i32 {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        mktype(dhall_expr!(Integer))
    }
}

impl SimpleStaticType for i64 {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        mktype(dhall_expr!(Integer))
    }
}

impl SimpleStaticType for String {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        mktype(dhall_expr!(Text))
    }
}

impl<A: SimpleStaticType, B: SimpleStaticType> SimpleStaticType for (A, B) {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        let ta: SubExpr<_, _> = A::get_simple_static_type().into();
        let tb: SubExpr<_, _> = B::get_simple_static_type().into();
        mktype(dhall_expr!({ _1: ta, _2: tb }))
    }
}

impl<T: SimpleStaticType> SimpleStaticType for Option<T> {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        let t: SubExpr<_, _> = T::get_simple_static_type().into();
        mktype(dhall_expr!(Optional t))
    }
}

impl<T: SimpleStaticType> SimpleStaticType for Vec<T> {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        let t: SubExpr<_, _> = T::get_simple_static_type().into();
        mktype(dhall_expr!(List t))
    }
}

impl<'b, T: SimpleStaticType> SimpleStaticType for &'b T {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        T::get_simple_static_type()
    }
}

impl<T> SimpleStaticType for std::marker::PhantomData<T> {
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        mktype(dhall_expr!({}))
    }
}

impl<T: SimpleStaticType, E: SimpleStaticType> SimpleStaticType
    for std::result::Result<T, E>
{
    fn get_simple_static_type<'a>() -> SimpleType<'a> {
        let tt: SubExpr<_, _> = T::get_simple_static_type().into();
        let te: SubExpr<_, _> = E::get_simple_static_type().into();
        mktype(dhall_expr!(< Ok: tt | Err: te>))
    }
}
