#![feature(proc_macro_hygiene)]
#![feature(custom_inner_attributes)]
#![rustfmt::skip]
mod common;

// See ../build.rs
include!(concat!(env!("OUT_DIR"), "/parser_tests.rs"));
