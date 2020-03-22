#![doc(html_root_url = "https://docs.rs/serde_dhall/0.4.0")]
// TODO #![warn(missing_docs)] #![warn(missing_doc_code_examples)]
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
//! values to Dhall is not supported.
//!
//! # Basic usage
//!
//! The main entrypoint of this library is the [`from_str`](fn.from_str.html) function. It reads a string
//! containing a Dhall expression and deserializes it into any serde-compatible type.
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
//! let deserialized_map: HashMap<String, usize> = serde_dhall::from_str(data)?;
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
//! #[derive(Debug, Deserialize)]
//! struct Point {
//!     x: u64,
//!     y: u64,
//! }
//!
//! // Some Dhall data
//! let data = "{ x = 1, y = 1 + 1 } : { x: Natural, y: Natural }";
//!
//! // Convert the Dhall string to a Point.
//! let point: Point = serde_dhall::from_str(data)?;
//! assert_eq!(point.x, 1);
//! assert_eq!(point.y, 2);
//!
//! # Ok(())
//! # }
//! ```
//!
//! # Type correspondence
//!
//! The following Dhall types correspond to the following Rust types:
//!
//! Dhall  | Rust
//! -------|------
//! `Bool`  | `bool`
//! `Natural`  | `u64`, `u32`, ...
//! `Integer`  | `i64`, `i32`, ...
//! `Double`  | `f64`, `f32`, ...
//! `Text`  | `String`
//! `List T`  | `Vec<T>`
//! `Optional T`  | `Option<T>`
//! `{ x: T, y: U }`  | structs
//! `{ _1: T, _2: U }`  | `(T, U)`, structs
//! `{ x: T, y: T }`  | `HashMap<String, T>`, structs
//! `< x: T \| y: U >`  | enums
//! `T -> U`  | unsupported
//! `Prelude.JSON.Type`  | unsupported
//! `Prelude.Map.Type T U`  | unsupported
//!
//!
//! # Replacing `serde_json` or `serde_yaml`
//!
//! If you used to consume JSON or YAML, you only need to replace [`serde_json::from_str`] or
//! [`serde_yaml::from_str`] with [`serde_dhall::from_str`](fn.from_str.html).
//!
//! [`serde_json::from_str`]: https://docs.serde.rs/serde_json/fn.from_str.html
//! [`serde_yaml::from_str`]: https://docs.serde.rs/serde_yaml/fn.from_str.html
//!
//!
//! # Additional Dhall typechecking
//!
//! When deserializing, normal type checking is done to ensure that the returned value is a valid
//! Dhall value, and that it can be deserialized into the required Rust type. However types are
//! first-class in Dhall, and this library allows you to additionally check that some input data
//! matches a given Dhall type. That way, a type error will be caught on the Dhall side, and have
//! pretty and explicit errors that point to the source file.
//!
//! There are two ways to typecheck a Dhall value: you can provide the type as Dhall text or you
//! can let Rust infer it for you.
//!
//! To provide a type written in Dhall, first parse it into a [`simple::Type`](simple/struct.Type.html), then
//! pass it to [`from_str_manual_type`](fn.from_str_manual_type.html).
//!
//! ```rust
//! # fn main() -> serde_dhall::Result<()> {
//! use serde_dhall::simple::Type;
//! use std::collections::HashMap;
//!
//! // Parse a Dhall type
//! let point_type_str = "{ x: Natural, y: Natural }";
//! let point_type: Type = serde_dhall::from_str(point_type_str)?;
//!
//! // Some Dhall data
//! let point_data = "{ x = 1, y = 1 + 1 }";
//!
//! // Deserialize the data to a Rust type. This checks that
//! // the data matches the provided type.
//! let deserialized_map: HashMap<String, usize> =
//!         serde_dhall::from_str_manual_type(point_data, &point_type)?;
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
//! You can also let Rust infer the appropriate Dhall type, using the
//! [StaticType](trait.StaticType.html) trait.
//!
//! ```rust
//! # fn main() -> serde_dhall::Result<()> {
//! use serde::Deserialize;
//! use serde_dhall::StaticType;
//!
//! #[derive(Debug, Deserialize, StaticType)]
//! struct Point {
//!     x: u64,
//!     y: u64,
//! }
//!
//! // Some Dhall data
//! let data = "{ x = 1, y = 1 + 1 }";
//!
//! // Convert the Dhall string to a Point.
//! let point: Point = serde_dhall::from_str_static_type(data)?;
//! assert_eq!(point.x, 1);
//! assert_eq!(point.y, 2);
//!
//! // Invalid data fails the type validation
//! let invalid_data = "{ x = 1, z = 0.3 }";
//! assert!(serde_dhall::from_str_static_type::<Point>(invalid_data).is_err());
//! # Ok(())
//! # }
//! ```
//!
//! [dhall]: https://dhall-lang.org/
//! [serde]: https://docs.serde.rs/serde/
//! [serde::Deserialize]: https://docs.serde.rs/serde/trait.Deserialize.html

#[cfg(doctest)]
doc_comment::doctest!("../../README.md");

/// Finer-grained control over deserializing Dhall values
pub mod options;
/// Serde-compatible Dhall values and their type
pub mod simple;
/// Arbitrary Dhall values
pub mod value;

mod deserialize;
mod error;
/// Common patterns made easier
mod shortcuts;
mod static_type;

#[doc(hidden)]
pub use dhall_proc_macros::StaticType;

pub use deserialize::Deserialize;
pub(crate) use deserialize::Sealed;
pub use error::{Error, Result};
pub use shortcuts::{from_str, from_str_manual_type, from_str_static_type};
pub use simple::{Type as SimpleType, Value as SimpleValue};
pub use static_type::StaticType;
pub use value::Value;
