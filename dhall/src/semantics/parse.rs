use std::path::Path;
use url::Url;

use crate::error::Error;
use crate::semantics::resolve::{download_http_text, ImportLocation};
use crate::syntax::{binary, parse_expr};
use crate::Parsed;

pub fn parse_file(f: &Path) -> Result<Parsed, Error> {
    let text = std::fs::read_to_string(f)?;
    let expr = parse_expr(&text)?;
    let root = ImportLocation::local_dhall_code(f.to_owned());
    Ok(Parsed(expr, root))
}

pub fn parse_remote(url: Url) -> Result<Parsed, Error> {
    let body = download_http_text(url.clone())?;
    let expr = parse_expr(&body)?;
    let root = ImportLocation::remote_dhall_code(url);
    Ok(Parsed(expr, root))
}

pub fn parse_str(s: &str) -> Result<Parsed, Error> {
    let expr = parse_expr(s)?;
    let root = ImportLocation::dhall_code_of_unknown_origin();
    Ok(Parsed(expr, root))
}

pub fn parse_binary(data: &[u8]) -> Result<Parsed, Error> {
    let expr = binary::decode(data)?;
    let root = ImportLocation::dhall_code_of_unknown_origin();
    Ok(Parsed(expr, root))
}

pub fn parse_binary_file(f: &Path) -> Result<Parsed, Error> {
    let data = crate::utils::read_binary_file(f)?;
    let expr = binary::decode(&data)?;
    let root = ImportLocation::local_dhall_code(f.to_owned());
    Ok(Parsed(expr, root))
}
