use dhall::{STyKind, SimpleType};

use crate::Type;

/// A Rust type that can be represented as a Dhall type.
///
/// A typical example is `Option<bool>`,
/// represented by the dhall expression `Optional Bool`.
///
/// This trait can and should be automatically derived.
///
/// The representation needs to be independent of the value.
/// For this reason, something like `HashMap<String, bool>` cannot implement
/// [StaticType] because each different value would
/// have a different Dhall record type.
pub trait StaticType {
    fn static_type() -> Type;
}

macro_rules! derive_builtin {
    ($rust_ty:ty, $dhall_ty:ident) => {
        impl StaticType for $rust_ty {
            fn static_type() -> Type {
                Type::from_simple_type(SimpleType::new(STyKind::$dhall_ty))
            }
        }
    };
}

derive_builtin!(bool, Bool);
derive_builtin!(usize, Natural);
derive_builtin!(u64, Natural);
derive_builtin!(u32, Natural);
derive_builtin!(isize, Integer);
derive_builtin!(i64, Integer);
derive_builtin!(i32, Integer);
derive_builtin!(f64, Double);
derive_builtin!(f32, Double);
derive_builtin!(String, Text);

impl<A, B> StaticType for (A, B)
where
    A: StaticType,
    B: StaticType,
{
    fn static_type() -> Type {
        Type::make_record_type(
            vec![
                ("_1".to_owned(), A::static_type()),
                ("_2".to_owned(), B::static_type()),
            ]
            .into_iter(),
        )
    }
}

impl<T, E> StaticType for std::result::Result<T, E>
where
    T: StaticType,
    E: StaticType,
{
    fn static_type() -> Type {
        Type::make_union_type(
            vec![
                ("Ok".to_owned(), Some(T::static_type())),
                ("Err".to_owned(), Some(E::static_type())),
            ]
            .into_iter(),
        )
    }
}

impl<T> StaticType for Option<T>
where
    T: StaticType,
{
    fn static_type() -> Type {
        Type::make_optional_type(T::static_type())
    }
}

impl<T> StaticType for Vec<T>
where
    T: StaticType,
{
    fn static_type() -> Type {
        Type::make_list_type(T::static_type())
    }
}

impl<'a, T> StaticType for &'a T
where
    T: StaticType,
{
    fn static_type() -> Type {
        T::static_type()
    }
}
