#![feature(non_exhaustive)]

//! [Dhall][dhall] is a programmable configuration language that provides a non-repetitive
//! alternative to JSON and YAML.
//!
//! You can think of Dhall as: JSON + types + imports + functions
//!
//! For a description of the dhall language, examples, tutorials, and more, see the [language
//! website][dhall].
//!
//! This crate provides support for consuming dhall files the same way you would consume JSON or
//! YAML. It uses the [Serde][serde] serialization library to provide drop-in support for dhall
//! for any datatype that supports serde (and that's a lot of them !).
//!
//! This library is limited to deserializing (reading) dhall values; serializing (writing)
//! values to dhall is not supported for now.
//!
//! # Examples
//!
//! ### Custom datatype
//!
//! If you have a custom datatype for which you derived [serde::Deserialize], chances are
//! you will be able to derive [StaticType][de::StaticType] for it as well.
//! This gives you access to a dhall representation of your datatype that can be outputted
//! to users, and allows easy type-safe deserializing.
//!
//! ```edition2018
//! use serde::Deserialize;
//! use serde_dhall::de::StaticType;
//!
//! #[derive(Debug, Deserialize, StaticType)]
//! struct Point {
//!     x: u64,
//!     y: u64,
//! }
//!
//! fn main() {
//!     // Some dhall data
//!     let data = "{ x = 1, y = 1 + 1 }";
//!
//!     // Convert the dhall string to a Point.
//!     let point: Point =
//!             serde_dhall::de::from_str_auto_type(&data)
//!                 .expect("An error ocurred !");
//!
//!     // Prints "point = Point { x: 1, y: 2 }"
//!     println!("point = {:?}", point);
//! }
//! ```
//!
//! ### Loosely typed
//!
//! If you used to consume JSON or YAML in a loosely typed way, you can continue to do so
//! with dhall. You only need to replace [serde_json::from_str] or [serde_yaml::from_str]
//! with [serde_dhall::de::from_str][de::from_str].
//! More generally, if the [StaticType][de::StaticType] derive doesn't suit your
//! needs, you can still deserialize any valid dhall file that serde can handle.
//!
//! [serde_json::from_str]: https://docs.serde.rs/serde_json/de/fn.from_str.html
//! [serde_yaml::from_str]: https://docs.serde.rs/serde_yaml/fn.from_str.html
//!
//! ```edition2018
//! use std::collections::BTreeMap;
//!
//! let mut map = BTreeMap::new();
//! map.insert("x".to_string(), 1);
//! map.insert("y".to_string(), 2);
//!
//! // Some dhall data
//! let data = "{ x = 1, y = 1 + 1 } : { x: Natural, y: Natural }";
//!
//! // Deserialize it to a Rust type.
//! let deserialized_map: BTreeMap<String, usize> =
//!         serde_dhall::de::from_str(&data, None)
//!             .expect("Failed reading the data !");
//! assert_eq!(map, deserialized_map);
//! ```
//!
//! You can of course specify a dhall type that the input should match.
//!
//! ```edition2018
//! use std::collections::BTreeMap;
//!
//! let mut map = BTreeMap::new();
//! map.insert("x".to_string(), 1);
//! map.insert("y".to_string(), 2);
//!
//! // Some dhall data
//! let point_data = "{ x = 1, y = 1 + 1 }";
//! let point_type_data = "{ x: Natural, y: Natural }";
//!
//! // Construct a type
//! let point_type =
//!         serde_dhall::de::from_str(point_type_data, None)
//!             .expect("Could not parse the Point type");
//!
//! // Deserialize it to a Rust type.
//! let deserialized_map: BTreeMap<String, usize> =
//!         serde_dhall::de::from_str(&point_data, Some(&point_type))
//!             .expect("Failed reading the data !");
//! assert_eq!(map, deserialized_map);
//! ```
//!
//! [dhall]: https://dhall-lang.org/
//! [serde]: https://docs.serde.rs/serde/
//! [serde::Deserialize]: https://docs.serde.rs/serde/trait.Deserialize.html

mod serde;
mod static_type;

pub use value::Value;

mod value {
    use dhall::core::thunk::{Thunk, TypeThunk};
    use dhall::core::value::Value as DhallValue;
    use dhall::phase::{NormalizedSubExpr, Parsed, Type, Typed};
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
                Some(t) => resolved.typecheck_with(&t.to_type())?,
            };
            Ok(Value(typed))
        }
        pub(crate) fn to_expr(&self) -> NormalizedSubExpr {
            self.0.to_expr()
        }
        pub(crate) fn to_thunk(&self) -> Thunk {
            self.0.to_thunk()
        }
        pub(crate) fn to_type(&self) -> Type {
            self.0.to_type()
        }

        pub(crate) fn from_dhall_value(v: DhallValue) -> Self {
            Value(Typed::from_value_untyped(v))
        }
        pub(crate) fn make_builtin_type(b: Builtin) -> Self {
            Self::from_dhall_value(DhallValue::from_builtin(b))
        }
        pub(crate) fn make_optional_type(t: Value) -> Self {
            Self::from_dhall_value(DhallValue::AppliedBuiltin(
                Builtin::Optional,
                vec![t.to_thunk()],
            ))
        }
        pub(crate) fn make_list_type(t: Value) -> Self {
            Self::from_dhall_value(DhallValue::AppliedBuiltin(
                Builtin::List,
                vec![t.to_thunk()],
            ))
        }
        // Made public for the StaticType derive macro
        #[doc(hidden)]
        pub fn make_record_type(
            kts: impl Iterator<Item = (String, Value)>,
        ) -> Self {
            Self::from_dhall_value(DhallValue::RecordType(
                kts.map(|(k, t)| {
                    (k.into(), TypeThunk::from_thunk(t.to_thunk()))
                })
                .collect(),
            ))
        }
        #[doc(hidden)]
        pub fn make_union_type(
            kts: impl Iterator<Item = (String, Option<Value>)>,
        ) -> Self {
            Self::from_dhall_value(DhallValue::UnionType(
                kts.map(|(k, t)| {
                    (k.into(), t.map(|t| TypeThunk::from_thunk(t.to_thunk())))
                })
                .collect(),
            ))
        }
    }

    impl super::de::Deserialize for Value {
        fn from_dhall(v: &Value) -> Result<Self> {
            Ok(v.clone())
        }
    }
}

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

/// Deserialization of Dhall expressions into Rust
pub mod de {
    #[doc(hidden)]
    pub use dhall_proc_macros::StaticType;

    pub use super::error::{Error, Result};
    pub use super::static_type::StaticType;
    pub use super::Value;

    /// A data structure that can be deserialized from a Dhall expression
    ///
    /// This is automatically implemented for any type that [serde][serde]
    /// can deserialize.
    ///
    /// This trait cannot be implemented manually.
    // TODO: seal trait
    pub trait Deserialize: Sized {
        /// See [dhall::de::from_str][crate::de::from_str]
        fn from_dhall(v: &Value) -> Result<Self>;
    }

    /// Deserialize an instance of type T from a string of Dhall text.
    ///
    /// This will recursively resolve all imports in the expression, and
    /// typecheck it before deserialization. Relative imports will be resolved relative to the
    /// provided file. More control over this process is not yet available
    /// but will be in a coming version of this crate.
    ///
    /// If a type is provided, this additionally checks that the provided
    /// expression has that type.
    pub fn from_str<T>(s: &str, ty: Option<&Value>) -> Result<T>
    where
        T: Deserialize,
    {
        T::from_dhall(&Value::from_str(s, ty)?)
    }

    /// Deserialize an instance of type T from a string of Dhall text,
    /// additionally checking that it matches the type of T.
    ///
    /// This will recursively resolve all imports in the expression, and
    /// typecheck it before deserialization. Relative imports will be resolved relative to the
    /// provided file. More control over this process is not yet available
    /// but will be in a coming version of this crate.
    pub fn from_str_auto_type<T>(s: &str) -> Result<T>
    where
        T: Deserialize + StaticType,
    {
        from_str(s, Some(&<T as StaticType>::static_type()))
    }
}
