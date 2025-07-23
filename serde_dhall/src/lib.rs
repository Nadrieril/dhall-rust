#![doc(html_root_url = "https://docs.rs/serde_dhall/0.13.0")]
#![allow(unknown_lints)] // for `rustdoc::missing_doc_code_examples`
#![warn(missing_docs, rustdoc::missing_doc_code_examples)]
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
//! # Basic usage
//!
//! ## Deserialization (reading)
//!
//! The entrypoint for deserialization is the [`from_str()`] function. It reads a string containing
//! a Dhall expression and deserializes it into any serde-compatible type.
//!
//! This could mean a common Rust type like `HashMap`:
//!
//! ```rust
//! # fn main() -> serde_dhall::Result<()> {
//! use std::collections::HashMap;
//!
//! // Some Dhall data
//! let data = "{ x = 1, y = 1 + 1 } : { x: Natural, y: Natural }";
//!
//! // Deserialize it to a Rust type.
//! let deserialized_map: HashMap<String, u64> = serde_dhall::from_str(data).parse()?;
//!
//! let mut expected_map = HashMap::new();
//! expected_map.insert("x".to_string(), 1);
//! expected_map.insert("y".to_string(), 2);
//!
//! assert_eq!(deserialized_map, expected_map);
//! # Ok(())
//! # }
//! ```
//!
//! or a custom datatype, using serde's `derive` mechanism:
//!
//! ```rust
//! # fn main() -> serde_dhall::Result<()> {
//! use serde::Deserialize;
//!
//! #[derive(Deserialize)]
//! struct Point {
//!     x: u64,
//!     y: u64,
//! }
//!
//! // Some Dhall data
//! let data = "{ x = 1, y = 1 + 1 } : { x: Natural, y: Natural }";
//!
//! // Convert the Dhall string to a Point.
//! let point: Point = serde_dhall::from_str(data).parse()?;
//! assert_eq!(point.x, 1);
//! assert_eq!(point.y, 2);
//!
//! # Ok(())
//! # }
//! ```
//!
//! ## Serialization (writing)
//!
//! The entrypoint for serialization is the [`serialize()`] function. It takes a serde-compatible
//! type value and serializes it to a string containing a Dhall expression.
//!
//! This could mean a common Rust type like `HashMap`:
//!
//! ```rust
//! # fn main() -> serde_dhall::Result<()> {
//! use std::collections::HashMap;
//!
//! let mut map = HashMap::new();
//! map.insert("x".to_string(), 1u64);
//! map.insert("y".to_string(), 2u64);
//!
//! let string = serde_dhall::serialize(&map).to_string()?;
//! assert_eq!(
//!     string,
//!     "{ x = 1, y = 2 }".to_string(),
//! );
//! # Ok(())
//! # }
//! ```
//!
//! or a custom datatype, using serde's `derive` mechanism:
//!
//! ```rust
//! # fn main() -> serde_dhall::Result<()> {
//! use serde::Serialize;
//!
//! #[derive(Serialize)]
//! struct Point {
//!     x: u64,
//!     y: u64,
//! }
//!
//! let data = Point { x: 1, y: 2 };
//! let string = serde_dhall::serialize(&data).to_string()?;
//! assert_eq!(
//!     string,
//!     "{ x = 1, y = 2 }".to_string(),
//! );
//! # Ok(())
//! # }
//! ```
//!
//! Beware that in order to serialize empty options, empty lists or enums correctly, you will need
//! to provide a type annotation!
//!
//! # Replacing `serde_json` or `serde_yaml`
//!
//! If you used to consume JSON or YAML, you only need to replace [`serde_json::from_str`] or
//! [`serde_yaml::from_str`] with [`serde_dhall::from_str(…).parse()`](from_str()).
//! If you used to produce JSON or YAML, you only need to replace [`serde_json::to_string`] or
//! [`serde_yaml::to_string`] with [`serde_dhall::serialize(…).to_string()`](serialize()).
//!
//! [`serde_json::from_str`]: https://docs.serde.rs/serde_json/fn.from_str.html
//! [`serde_yaml::from_str`]: https://docs.serde.rs/serde_yaml/fn.from_str.html
//! [`serde_json::to_string`]: https://docs.serde.rs/serde_json/fn.to_string.html
//! [`serde_yaml::to_string`]: https://docs.serde.rs/serde_yaml/fn.to_string.html
//!
//!
//! # Additional type annotations
//!
//! When deserializing, normal type checking is done to ensure that the returned value is a valid
//! Dhall value. However types are
//! first-class in Dhall, and this library allows you to additionally check that the input data
//! matches a given Dhall type. That way, a type error will be caught on the Dhall side, and have
//! pretty and explicit errors that point to the source file.
//!
//! It is also possible to provide a type annotation when serializing. This is useful in particular
//! for types like `HashMap` or [`SimpleValue`] that do not have a fixed type as Dhall values.
//!
//! Moreover, some values (namely empty options, empty lists, and enums) _require_ a type annotation
//! in order to be converted to Dhall, because the resulting Dhall value will contain the type
//! explicitly.
//!
//! There are two ways to provide a type in this way: you can provide it manually or you can let
//! Rust infer it for you. To let Rust infer the appropriate Dhall type, use the [`StaticType`]
//! trait.
//!
//! ```rust
//! # fn main() -> serde_dhall::Result<()> {
//! use serde::Deserialize;
//! use serde_dhall::StaticType;
//!
//! #[derive(Deserialize, StaticType)]
//! struct Point {
//!     x: u64,
//!     y: u64,
//! }
//!
//! // Some Dhall data
//! let data = "{ x = 1, y = 1 + 1 }";
//!
//! // Convert the Dhall string to a Point.
//! let point = serde_dhall::from_str(data)
//!     .static_type_annotation()
//!     .parse::<Point>()?;
//! assert_eq!(point.x, 1);
//! assert_eq!(point.y, 2);
//!
//! // Invalid data fails the type validation
//! let invalid_data = "{ x = 1, z = 0.3 }";
//! assert!(
//!     serde_dhall::from_str(invalid_data)
//!         .static_type_annotation()
//!         .parse::<Point>()
//!         .is_err()
//! );
//! # Ok(())
//! # }
//! ```
//!
//! ```
//! # fn main() -> serde_dhall::Result<()> {
//! use serde::Serialize;
//! use serde_dhall::{serialize, StaticType};
//!
//! #[derive(Serialize, StaticType)]
//! enum MyOption {
//!     MyNone,
//!     MySome(u64),
//! }
//!
//! let data = MyOption::MySome(0);
//! let string = serialize(&data)
//!     .static_type_annotation()
//!     .to_string()?;
//! // The resulting Dhall string depends on the type annotation; it could not have been
//! // printed without it.
//! assert_eq!(string, "< MyNone | MySome: Natural >.MySome 0".to_string());
//! # Ok(())
//! # }
//! ```
//!
//! To provide a type manually, you need a [`SimpleType`] value. You can parse it from some Dhall
//! text like you would parse any other value.
//!
//! ```rust
//! # fn main() -> serde_dhall::Result<()> {
//! use serde_dhall::SimpleType;
//! use std::collections::HashMap;
//!
//! // Parse a Dhall type
//! let point_type_str = "{ x: Natural, y: Natural }";
//! let point_type = serde_dhall::from_str(point_type_str).parse::<SimpleType>()?;
//!
//! // Some Dhall data
//! let point_data = "{ x = 1, y = 1 + 1 }";
//!
//! // Deserialize the data to a Rust type. This checks that
//! // the data matches the provided type.
//! let deserialized_map = serde_dhall::from_str(point_data)
//!     .type_annotation(&point_type)
//!     .parse::<HashMap<String, u64>>()?;
//!
//! let mut expected_map = HashMap::new();
//! expected_map.insert("x".to_string(), 1);
//! expected_map.insert("y".to_string(), 2);
//!
//! assert_eq!(deserialized_map, expected_map);
//! # Ok(())
//! # }
//! ```
//!
//! ```
//! # fn main() -> serde_dhall::Result<()> {
//! use serde_dhall::{serialize, from_str, SimpleValue};
//!
//! let ty = from_str("< A | B: Bool >").parse()?;
//! let data = SimpleValue::Union("A".to_string(), None);
//! let string = serialize(&data)
//!     .type_annotation(&ty)
//!     .to_string()?;
//! assert_eq!(string, "< A | B: Bool >.A".to_string());
//! # Ok(())
//! # }
//! ```
//!
//! # Controlling deserialization
//!
//! If you need more control over the process of reading Dhall values, e.g. disabling
//! imports, see the [`Deserializer`] methods.
//!
//! [dhall]: https://dhall-lang.org/
//! [serde]: https://docs.serde.rs/serde/
//! [serde::Deserialize]: https://docs.serde.rs/serde/trait.Deserialize.html

#[cfg(doctest)]
mod test_readme {
    doc_comment::doctest!("../../README.md");
}

mod deserialize;
mod error;
mod options;
mod serialize;
mod static_type;
/// Dhall values
mod value;

#[doc(hidden)]
pub use dhall_proc_macros::StaticType;

pub use deserialize::{from_simple_value, FromDhall};
pub(crate) use error::ErrorKind;
pub use error::{Error, Result};
pub use options::de::{
    from_binary, from_binary_file, from_file, from_str, Deserializer,
};
pub use options::ser::{serialize, Serializer};
pub use serialize::ToDhall;
pub use static_type::StaticType;
pub use value::{NumKind, SimpleType, SimpleValue, Value};
