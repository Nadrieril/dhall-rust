#![feature(trace_macros)]
#![feature(proc_macro_hygiene)]
#![feature(slice_patterns)]
#![feature(label_break_value)]
#![cfg_attr(test, feature(custom_inner_attributes))]
#![allow(
    clippy::type_complexity,
    clippy::infallible_destructuring_match,
    clippy::many_single_char_names
)]

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
pub use crate::traits::SimpleStaticType;
pub use crate::traits::StaticType;
pub use dhall_generator::SimpleStaticType;
pub mod expr;
