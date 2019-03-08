#![feature(box_patterns)]
#![feature(trace_macros)]
#![feature(proc_macro_hygiene)]

mod normalize;
pub use crate::normalize::*;
pub mod imports;
pub mod typecheck;

pub use crate::imports::{load_dhall_file, DhallError};
