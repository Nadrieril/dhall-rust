#![feature(box_patterns)]
#![feature(trace_macros)]
#![feature(proc_macro_hygiene)]
#![feature(slice_patterns)]
#![allow(
    clippy::type_complexity,
    clippy::infallible_destructuring_match,
    clippy::many_single_char_names
)]

mod normalize;
pub use crate::normalize::*;
pub mod binary;
pub mod imports;
pub mod typecheck;

pub use crate::imports::{load_dhall_file, DhallError};
