#![feature(non_exhaustive)]

//! [Dhall][dhall] is a programmable configuration language that provides a non-repetitive
//! alternative to JSON and YAML.
//!
//! You can think of Dhall as: JSON + types + imports + functions
//!
//! For a description of the Dhall language, examples, tutorials, and more, see the [language
//! website][dhall].
//!
//! This crate provides support for consuming Dhall files the same way you would consume JSON or
//! YAML. It uses the [Serde][serde] serialization library to provide drop-in support for Dhall
//! for any datatype that supports serde (and that's a lot of them !).
//!
//! This library is limited to deserializing (reading) Dhall values; serializing (writing)
//! values to Dhall is not supported for now.
//!
//! # Examples
//!
//! ### Custom datatype
//!
//! If you have a custom datatype for which you derived [serde::Deserialize], chances are
//! you will be able to derive [StaticType] for it as well.
//! This allows easy type-safe deserializing.
//!
//! ```edition2018
//! use serde::Deserialize;
//! use serde_dhall::{de::Error, StaticType};
//!
//! #[derive(Debug, Deserialize, StaticType)]
//! struct Point {
//!     x: u64,
//!     y: u64,
//! }
//!
//! fn main() -> Result<(), Error> {
//!     // Some Dhall data
//!     let data = "{ x = 1, y = 1 + 1 }";
//!
//!     // Convert the Dhall string to a Point.
//!     let point: Point = serde_dhall::from_str_auto_type(data)?;
//!     assert_eq!(point.x, 1);
//!     assert_eq!(point.y, 2);
//!
//!     // Invalid data fails the type validation
//!     let invalid_data = "{ x = 1, z = 0.3 }";
//!     assert!(serde_dhall::from_str_auto_type::<Point>(invalid_data).is_err());
//!
//!     Ok(())
//! }
//! ```
//!
//! ### Loosely typed
//!
//! If you used to consume JSON or YAML in a loosely typed way, you can continue to do so
//! with Dhall. You only need to replace [serde_json::from_str] or [serde_yaml::from_str]
//! with [serde_dhall::from_str][from_str].
//! More generally, if the [StaticType] derive doesn't suit your
//! needs, you can still deserialize any valid Dhall file that serde can handle.
//!
//! [serde_json::from_str]: https://docs.serde.rs/serde_json/de/fn.from_str.html
//! [serde_yaml::from_str]: https://docs.serde.rs/serde_yaml/fn.from_str.html
//!
//! ```edition2018
//! # fn main() -> serde_dhall::de::Result<()> {
//! use std::collections::BTreeMap;
//!
//! // Some Dhall data
//! let data = "{ x = 1, y = 1 + 1 } : { x: Natural, y: Natural }";
//!
//! // Deserialize it to a Rust type.
//! let deserialized_map: BTreeMap<String, usize> = serde_dhall::from_str(data)?;
//!
//! let mut expected_map = BTreeMap::new();
//! expected_map.insert("x".to_string(), 1);
//! expected_map.insert("y".to_string(), 2);
//!
//! assert_eq!(deserialized_map, expected_map);
//! # Ok(())
//! # }
//! ```
//!
//! You can alternatively specify a Dhall type that the input should match.
//!
//! ```edition2018
//! # fn main() -> serde_dhall::de::Result<()> {
//! use std::collections::BTreeMap;
//!
//! // Parse a Dhall type
//! let point_type_str = "{ x: Natural, y: Natural }";
//! let point_type = serde_dhall::from_str(point_type_str)?;
//!
//! // Some Dhall data
//! let point_data = "{ x = 1, y = 1 + 1 }";
//!
//! // Deserialize the data to a Rust type. This ensures that
//! // the data matches the point type.
//! let deserialized_map: BTreeMap<String, usize> =
//!         serde_dhall::from_str_check_type(point_data, &point_type)?;
//!
//! let mut expected_map = BTreeMap::new();
//! expected_map.insert("x".to_string(), 1);
//! expected_map.insert("y".to_string(), 2);
//!
//! assert_eq!(deserialized_map, expected_map);
//! # Ok(())
//! # }
//! ```
//!
//! [dhall]: https://dhall-lang.org/
//! [serde]: https://docs.serde.rs/serde/
//! [serde::Deserialize]: https://docs.serde.rs/serde/trait.Deserialize.html

mod serde;
mod static_type;

#[doc(inline)]
pub use de::{from_str, from_str_auto_type, from_str_check_type};
#[doc(hidden)]
pub use dhall_proc_macros::StaticType;
pub use static_type::StaticType;
#[doc(inline)]
pub use value::Value;

// A Dhall value.
pub mod value {
    use dhall::phase::{NormalizedExpr, Parsed, Typed};
    use dhall_syntax::Builtin;

    use super::de::{Error, Result};

    /// A Dhall value
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Value(Typed);

    impl Value {
        pub fn from_str(s: &str, ty: Option<&Value>) -> Result<Self> {
            Value::from_str_using_dhall_error_type(s, ty).map_err(Error::Dhall)
        }
        fn from_str_using_dhall_error_type(
            s: &str,
            ty: Option<&Value>,
        ) -> dhall::error::Result<Self> {
            let resolved = Parsed::parse_str(s)?.resolve()?;
            let typed = match ty {
                None => resolved.typecheck()?,
                Some(t) => resolved.typecheck_with(t.as_typed())?,
            };
            Ok(Value(typed))
        }
        pub(crate) fn to_expr(&self) -> NormalizedExpr {
            self.0.normalize_to_expr()
        }
        pub(crate) fn as_typed(&self) -> &Typed {
            &self.0
        }

        pub(crate) fn make_builtin_type(b: Builtin) -> Self {
            Value(Typed::make_builtin_type(b))
        }
        pub(crate) fn make_optional_type(t: Value) -> Self {
            Value(Typed::make_optional_type(t.0))
        }
        pub(crate) fn make_list_type(t: Value) -> Self {
            Value(Typed::make_list_type(t.0))
        }
        // Made public for the StaticType derive macro
        #[doc(hidden)]
        pub fn make_record_type(
            kts: impl Iterator<Item = (String, Value)>,
        ) -> Self {
            Value(Typed::make_record_type(kts.map(|(k, t)| (k, t.0))))
        }
        #[doc(hidden)]
        pub fn make_union_type(
            kts: impl Iterator<Item = (String, Option<Value>)>,
        ) -> Self {
            Value(Typed::make_union_type(
                kts.map(|(k, t)| (k, t.map(|t| t.0))),
            ))
        }
    }

    impl super::de::Deserialize for Value {
        fn from_dhall(v: &Value) -> Result<Self> {
            Ok(v.clone())
        }
    }
}

/// Deserialize Dhall data to a Rust data structure.
pub mod de {
    use super::StaticType;
    use super::Value;
    pub use error::{Error, Result};

    mod error {
        use dhall::error::Error as DhallError;

        pub type Result<T> = std::result::Result<T, Error>;

        #[derive(Debug)]
        #[non_exhaustive]
        pub enum Error {
            Dhall(DhallError),
            Deserialize(String),
        }

        impl std::fmt::Display for Error {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                match self {
                    Error::Dhall(err) => write!(f, "{}", err),
                    Error::Deserialize(err) => write!(f, "{}", err),
                }
            }
        }

        impl std::error::Error for Error {}

        impl serde::de::Error for Error {
            fn custom<T>(msg: T) -> Self
            where
                T: std::fmt::Display,
            {
                Error::Deserialize(msg.to_string())
            }
        }
    }

    /// A data structure that can be deserialized from a Dhall expression
    ///
    /// This is automatically implemented for any type that [serde][serde]
    /// can deserialize.
    ///
    /// This trait cannot be implemented manually.
    // TODO: seal trait
    pub trait Deserialize: Sized {
        /// See [serde_dhall::from_str][crate::from_str]
        fn from_dhall(v: &Value) -> Result<Self>;
    }

    /// Deserialize an instance of type `T` from a string of Dhall text.
    ///
    /// This will recursively resolve all imports in the expression, and
    /// typecheck it before deserialization. Relative imports will be resolved relative to the
    /// provided file. More control over this process is not yet available
    /// but will be in a coming version of this crate.
    pub fn from_str<T>(s: &str) -> Result<T>
    where
        T: Deserialize,
    {
        T::from_dhall(&Value::from_str(s, None)?)
    }

    /// Deserialize an instance of type `T` from a string of Dhall text,
    /// additionally checking that it matches the supplied type.
    ///
    /// Like [from_str], but this additionally checks that
    /// the type of the provided expression matches the supplied type.
    pub fn from_str_check_type<T>(s: &str, ty: &Value) -> Result<T>
    where
        T: Deserialize,
    {
        T::from_dhall(&Value::from_str(s, Some(ty))?)
    }

    /// Deserialize an instance of type `T` from a string of Dhall text,
    /// additionally checking that it matches the type of `T`.
    ///
    /// Like [from_str], but this additionally checks that
    /// the type of the provided expression matches the output type `T`. The [StaticType] trait
    /// captures Rust types that are valid Dhall types.
    pub fn from_str_auto_type<T>(s: &str) -> Result<T>
    where
        T: Deserialize + StaticType,
    {
        from_str_check_type(s, &<T as StaticType>::static_type())
    }
}
