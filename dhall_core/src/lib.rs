#![feature(trace_macros)]
#![feature(slice_patterns)]
#![recursion_limit="128"]
#![allow(
    clippy::many_single_char_names,
    clippy::should_implement_trait,
    clippy::new_without_default
)]

pub mod core;
pub use crate::core::*;
pub mod context;
pub mod parser;
