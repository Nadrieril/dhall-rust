use dhall::syntax::{Builtin, Integer, Natural};

use crate::Value;

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
    fn static_type() -> Value;
}

macro_rules! derive_builtin {
    ($ty:ty, $builtin:ident) => {
        impl StaticType for $ty {
            fn static_type() -> Value {
                Value::make_builtin_type(Builtin::$builtin)
            }
        }
    };
}

derive_builtin!(bool, Bool);
derive_builtin!(Natural, Natural);
derive_builtin!(u64, Natural);
derive_builtin!(Integer, Integer);
derive_builtin!(String, Text);

impl<A, B> StaticType for (A, B)
where
    A: StaticType,
    B: StaticType,
{
    fn static_type() -> Value {
        Value::make_record_type(
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
    fn static_type() -> Value {
        Value::make_union_type(
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
    fn static_type() -> Value {
        Value::make_optional_type(T::static_type())
    }
}

impl<T> StaticType for Vec<T>
where
    T: StaticType,
{
    fn static_type() -> Value {
        Value::make_list_type(T::static_type())
    }
}

impl<'a, T> StaticType for &'a T
where
    T: StaticType,
{
    fn static_type() -> Value {
        T::static_type()
    }
}
