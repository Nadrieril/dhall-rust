use std::fs::File;
use std::io::Read;
use std::path::Path;

use crate::error::Error;
use crate::semantics::resolve::ImportRoot;
use crate::syntax::binary;
use crate::syntax::parse_expr;
use crate::Parsed;

pub(crate) fn parse_file(f: &Path) -> Result<Parsed, Error> {
    let mut buffer = String::new();
    File::open(f)?.read_to_string(&mut buffer)?;
    let expr = parse_expr(&*buffer)?;
    let root = ImportRoot::LocalDir(f.parent().unwrap().to_owned());
    Ok(Parsed(expr, root))
}

pub(crate) fn parse_str(s: &str) -> Result<Parsed, Error> {
    let expr = parse_expr(s)?;
    let root = ImportRoot::LocalDir(std::env::current_dir()?);
    Ok(Parsed(expr, root))
}

pub(crate) fn parse_binary(data: &[u8]) -> Result<Parsed, Error> {
    let expr = binary::decode(data)?;
    let root = ImportRoot::LocalDir(std::env::current_dir()?);
    Ok(Parsed(expr, root))
}

pub(crate) fn parse_binary_file(f: &Path) -> Result<Parsed, Error> {
    let mut buffer = Vec::new();
    File::open(f)?.read_to_end(&mut buffer)?;
    let expr = binary::decode(&buffer)?;
    let root = ImportRoot::LocalDir(f.parent().unwrap().to_owned());
    Ok(Parsed(expr, root))
}
