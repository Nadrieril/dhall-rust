use std::fs::File;
use std::io::Read;
use std::path::Path;
use url::Url;

use crate::error::Error;
use crate::semantics::resolve::ImportLocation;
use crate::syntax::binary;
use crate::syntax::parse_expr;
use crate::Parsed;

pub(crate) fn parse_file(f: &Path) -> Result<Parsed, Error> {
    let text = std::fs::read_to_string(f)?;
    let expr = parse_expr(&text)?;
    let root = ImportLocation::Local(f.to_owned());
    Ok(Parsed(expr, root))
}

pub(crate) fn parse_remote(url: Url) -> Result<Parsed, Error> {
    let body = reqwest::blocking::get(url.clone()).unwrap().text().unwrap();
    let expr = parse_expr(&body)?;
    let root = ImportLocation::Remote(url);
    Ok(Parsed(expr, root))
}

pub(crate) fn parse_str(s: &str) -> Result<Parsed, Error> {
    let expr = parse_expr(s)?;
    let root = ImportLocation::Missing;
    Ok(Parsed(expr, root))
}

pub(crate) fn parse_binary(data: &[u8]) -> Result<Parsed, Error> {
    let expr = binary::decode(data)?;
    let root = ImportLocation::Missing;
    Ok(Parsed(expr, root))
}

pub(crate) fn parse_binary_file(f: &Path) -> Result<Parsed, Error> {
    let mut buffer = Vec::new();
    File::open(f)?.read_to_end(&mut buffer)?;
    let expr = binary::decode(&buffer)?;
    let root = ImportLocation::Local(f.to_owned());
    Ok(Parsed(expr, root))
}
