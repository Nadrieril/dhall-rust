#![feature(trace_macros)]
#![feature(proc_macro_hygiene)]
#![feature(slice_patterns)]
#![feature(label_break_value)]
#![feature(non_exhaustive)]
#![feature(bind_by_move_pattern_guards)]
#![feature(try_trait)]
#![feature(inner_deref)]
#![feature(never_type)]
#![cfg_attr(test, feature(custom_inner_attributes))]
#![allow(
    clippy::type_complexity,
    clippy::infallible_destructuring_match,
    clippy::many_single_char_names,
    clippy::match_wild_err_arm,
    clippy::redundant_closure,
    clippy::ptr_arg
)]

#[cfg(test)]
#[macro_use]
mod tests;

pub mod core;
pub mod error;
pub mod phase;
