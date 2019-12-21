#![doc(html_root_url = "https://docs.rs/dhall/0.1.1")]
#![feature(trace_macros)]
#![feature(slice_patterns)]
#![feature(never_type)]
#![allow(
    clippy::type_complexity,
    clippy::infallible_destructuring_match,
    clippy::many_single_char_names,
    clippy::match_wild_err_arm,
    clippy::redundant_closure,
    clippy::ptr_arg
)]

mod tests;

pub mod error;
pub mod semantics;
pub mod syntax;
