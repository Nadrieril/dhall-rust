#![feature(trace_macros)]
#![allow(
    clippy::many_single_char_names,
    clippy::should_implement_trait,
    clippy::new_without_default
)]

pub mod core;
pub use crate::core::*;
pub mod context;
pub mod parser;
