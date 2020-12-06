use std::path::Path;
use url::Url;

use crate::error::Error;
use crate::semantics::resolve::{
    download_http_text, ImportLocation, ImportLocationKind,
};
use crate::syntax::binary;
use crate::syntax::parse_expr;
use crate::Parsed;

pub fn parse_file(f: &Path) -> Result<Parsed, Error> {
    let text = std::fs::read_to_string(f)?;
    let expr = parse_expr(&text)?;
    let root_kind = ImportLocationKind::Local(f.to_owned());
    let root = ImportLocation { kind: root_kind };
    Ok(Parsed(expr, root))
}

pub fn parse_remote(url: Url) -> Result<Parsed, Error> {
    let body = download_http_text(url.clone())?;
    let expr = parse_expr(&body)?;
    let root_kind = ImportLocationKind::Remote(url);
    let root = ImportLocation { kind: root_kind };
    Ok(Parsed(expr, root))
}

pub fn parse_str(s: &str) -> Result<Parsed, Error> {
    let expr = parse_expr(s)?;
    let root_kind = ImportLocationKind::Missing;
    let root = ImportLocation { kind: root_kind };
    Ok(Parsed(expr, root))
}

pub fn parse_binary(data: &[u8]) -> Result<Parsed, Error> {
    let expr = binary::decode(data)?;
    let root_kind = ImportLocationKind::Missing;
    let root = ImportLocation { kind: root_kind };
    Ok(Parsed(expr, root))
}

pub fn parse_binary_file(f: &Path) -> Result<Parsed, Error> {
    let data = crate::utils::read_binary_file(f)?;
    let expr = binary::decode(&data)?;
    let root_kind = ImportLocationKind::Local(f.to_owned());
    let root = ImportLocation { kind: root_kind };
    Ok(Parsed(expr, root))
}
