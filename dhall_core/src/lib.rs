#![feature(trace_macros)]
#![feature(slice_patterns)]
#![allow(
    clippy::many_single_char_names,
    clippy::should_implement_trait,
    clippy::new_without_default
)]

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
mod dhall_type;
pub use dhall_type::*;
pub mod context;
