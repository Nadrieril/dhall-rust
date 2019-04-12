#![feature(trace_macros)]
#![feature(proc_macro_hygiene)]
#![feature(slice_patterns)]
#![feature(label_break_value)]
#![feature(non_exhaustive)]
#![cfg_attr(test, feature(custom_inner_attributes))]
#![allow(
    clippy::type_complexity,
    clippy::infallible_destructuring_match,
    clippy::many_single_char_names
)]

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
//! you will be able to derive [SimpleStaticType] for it as well. This gives you access to
//! a dhall representation of your datatype that can be outputted to users, and
//! allows easy type-safe deserializing.
//!
//! ```edition2018
//! use serde::Deserialize;
//! use dhall::SimpleStaticType;
//!
//! #[derive(Debug, Deserialize, SimpleStaticType)]
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
//!             dhall::from_str_auto_type(&data)
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
//! with [dhall::from_str][from_str].
//! More generally, if the [SimpleStaticType] derive doesn't suit your needs, you can still
//! deserialize any valid dhall file that serde can handle.
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
//!         dhall::from_str(&data, None)
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
//!         dhall::from_str(point_type_data, None)
//!             .expect("Could not parse the Point type");
//!
//! // Deserialize it to a Rust type.
//! let deserialized_map: BTreeMap<String, usize> =
//!         dhall::from_str(&point_data, Some(&point_type))
//!             .expect("Failed reading the data !");
//! assert_eq!(map, deserialized_map);
//! ```
//!
//! [dhall]: https://dhall-lang.org/
//! [serde]: https://docs.serde.rs/serde/
//! [serde::Deserialize]: https://docs.serde.rs/serde/trait.Deserialize.html

#[cfg(test)]
#[macro_use]
mod tests;

#[cfg(test)]
mod parser;

mod binary;
mod imports;
mod normalize;
mod traits;
mod typecheck;
pub use crate::traits::{Deserialize, SimpleStaticType, StaticType};
#[doc(hidden)]
pub use dhall_generator::SimpleStaticType;
/// When manipulating Dhall expressions goes wrong.
pub mod error;
pub mod expr;
mod serde;

/// Deserialize an instance of type T from a string of Dhall text.
///
/// This will recursively resolve all imports in the expression, and
/// typecheck it. More control over this process is not yet available
/// but will be in a coming verions of this crate.
///
/// If a type is provided, this additionally checks that the provided
/// expression has that type.
pub fn from_str<'a, T: Deserialize<'a>>(
    s: &'a str,
    ty: Option<&crate::expr::Type>,
) -> crate::error::Result<T> {
    T::from_str(s, ty)
}

/// Deserialize an instance of type T from a string of Dhall text,
/// additionally checking that it matches the type of T.
///
/// This will recursively resolve all imports in the expression, and
/// typecheck it. More control over this process is not yet available
/// but will be in a coming verions of this crate.
pub fn from_str_auto_type<'a, T: Deserialize<'a> + StaticType>(
    s: &'a str,
) -> crate::error::Result<T> {
    from_str(s, Some(&<T as StaticType>::get_static_type()))
}
