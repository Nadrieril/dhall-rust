#![feature(box_patterns)]
#![feature(concat_idents)]
#![feature(transpose_result)]

pub mod context;
mod core;
pub use crate::core::*;
use lalrpop_util::lalrpop_mod;
lalrpop_mod!(pub grammar);
mod grammar_util;
pub mod lexer;
pub mod parser;
pub mod typecheck;
