use std::fs::File;
use std::io::Read;
use std::path::Path;

use dhall_syntax::parse_expr;

use crate::error::Error;
use crate::phase::resolve::ImportRoot;
use crate::phase::Parsed;

pub fn parse_file(f: &Path) -> Result<Parsed, Error> {
    let mut buffer = String::new();
    File::open(f)?.read_to_string(&mut buffer)?;
    let expr = parse_expr(&*buffer)?;
    let root = ImportRoot::LocalDir(f.parent().unwrap().to_owned());
    Ok(Parsed(expr, root))
}

pub fn parse_str(s: &str) -> Result<Parsed, Error> {
    let expr = parse_expr(s)?;
    let root = ImportRoot::LocalDir(std::env::current_dir()?);
    Ok(Parsed(expr, root))
}

pub fn parse_binary(data: &[u8]) -> Result<Parsed, Error> {
    let expr = crate::phase::binary::decode(data)?;
    let root = ImportRoot::LocalDir(std::env::current_dir()?);
    Ok(Parsed(expr.note_absurd(), root))
}

pub fn parse_binary_file(f: &Path) -> Result<Parsed, Error> {
    let mut buffer = Vec::new();
    File::open(f)?.read_to_end(&mut buffer)?;
    let expr = crate::phase::binary::decode(&buffer)?;
    let root = ImportRoot::LocalDir(f.parent().unwrap().to_owned());
    Ok(Parsed(expr.note_absurd(), root))
}
