#![feature(trace_macros)]
#![feature(proc_macro_hygiene)]
#![feature(slice_patterns)]
#![allow(
    clippy::type_complexity,
    clippy::infallible_destructuring_match,
    clippy::many_single_char_names
)]

mod binary;
mod imports;
mod normalize;
pub mod traits;
pub mod typecheck;
pub use crate::imports::{load_dhall_file, ImportError};
pub use crate::traits::StaticType;
pub use dhall_generator::expr;
pub use dhall_generator::subexpr;
pub use dhall_generator::StaticType;
pub mod expr;
