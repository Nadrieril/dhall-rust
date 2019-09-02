#![feature(trace_macros)]
#![feature(slice_patterns)]
#![feature(try_blocks)]
#![feature(never_type)]
#![feature(proc_macro_hygiene)]
#![feature(type_alias_enum_variants)]
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
pub use crate::core::context;
pub use crate::core::visitor;
pub use crate::core::*;
mod printer;
pub use crate::printer::*;
mod parser;
pub use crate::parser::*;
