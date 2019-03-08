#![feature(box_patterns)]
#![feature(trace_macros)]
#![feature(proc_macro_hygiene)]

mod normalize;
pub use crate::normalize::*;
pub mod imports;
pub mod typecheck;

use dhall_core::*;
use std::fs::File;
use std::io::Read;
use std::path::Path;
use std::fmt;

#[derive(Debug)]
pub enum DhallError {
    ParseError(parser::ParseError),
    IOError(std::io::Error),
}
impl From<parser::ParseError> for DhallError {
    fn from(e: parser::ParseError) -> Self {
        DhallError::ParseError(e)
    }
}
impl From<std::io::Error> for DhallError {
    fn from(e: std::io::Error) -> Self {
        DhallError::IOError(e)
    }
}
impl fmt::Display for DhallError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use self::DhallError::*;
        match self {
            ParseError(e) => e.fmt(f),
            IOError(e) => e.fmt(f),
        }
    }
}

/// `source_pool` is a Vec of strings to be used to store the contents of imported files.
/// No ideal but necessary for lifetime reasons for now.
pub fn load_dhall_file<'i, 'a: 'i>(
    f: &Path,
    source_pool: &'a mut Vec<String>,
    _resolve_imports: bool,
) -> Result<Expr<'i, X, X>, DhallError> {
    source_pool.push(String::new());
    let mut buffer = source_pool.last_mut().unwrap();
    File::open(f)?.read_to_string(&mut buffer)?;
    let expr = parser::parse_expr(&*buffer)?;
    let expr = imports::resolve_imports(&expr);
    Ok(expr)
}
