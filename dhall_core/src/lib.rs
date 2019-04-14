#![feature(trace_macros)]
#![feature(slice_patterns)]
#![allow(
    clippy::many_single_char_names,
    clippy::should_implement_trait,
    clippy::new_without_default,
    clippy::type_complexity
)]

//! This crate contains the core AST-handling primitives for the [dhall-rust][dhall-rust] crate.
//! This is highly unstable and breaks regularly; use at your own risk.
//!
//! [dhall-rust]: https://github.com/Nadrieril/dhall-rust

mod core;
pub use crate::core::*;
mod import;
pub use crate::import::*;
mod label;
pub use crate::label::*;
mod text;
pub use crate::text::*;
mod printer;
pub use crate::printer::*;
mod parser;
pub use crate::parser::*;
pub mod context;
pub mod visitor;
