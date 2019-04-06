// use dhall_core::{Expr, FilePrefix, Import, ImportLocation, ImportMode, X};
use dhall_core::{Expr, Import, X};
// use std::path::Path;
use crate::expr::*;
use dhall_core::*;
use std::fmt;
use std::fs::File;
use std::io::Read;
use std::path::Path;
use std::path::PathBuf;

#[derive(Debug)]
pub enum ImportError {
    ParseError(ParseError),
    IOError(std::io::Error),
    UnexpectedImportError(Import),
}
impl From<ParseError> for ImportError {
    fn from(e: ParseError) -> Self {
        ImportError::ParseError(e)
    }
}
impl From<std::io::Error> for ImportError {
    fn from(e: std::io::Error) -> Self {
        ImportError::IOError(e)
    }
}
impl fmt::Display for ImportError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use self::ImportError::*;
        match self {
            ParseError(e) => e.fmt(f),
            IOError(e) => e.fmt(f),
            UnexpectedImportError(e) => e.fmt(f),
        }
    }
}

// Deprecated
pub fn panic_imports<S: Clone>(expr: &Expr<S, Import>) -> Expr<S, X> {
    let no_import = |i: &Import| -> X { panic!("ahhh import: {:?}", i) };
    expr.map_embed(&no_import)
}

/// A root from which to resolve relative imports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportRoot {
    LocalDir(PathBuf),
}

fn resolve_import(
    import: &Import,
    root: &ImportRoot,
) -> Result<Expr<X, X>, ImportError> {
    use self::ImportRoot::*;
    use dhall_core::FilePrefix::*;
    use dhall_core::ImportLocation::*;
    let cwd = match root {
        LocalDir(cwd) => cwd,
    };
    match &import.location_hashed.location {
        Local(prefix, path) => {
            let path = match prefix {
                Parent => cwd.parent().unwrap().join(path),
                Here => cwd.join(path),
                _ => unimplemented!("{:?}", import),
            };
            load_dhall_file(&path, true)
        }
        _ => unimplemented!("{:?}", import),
    }
}

pub(crate) fn resolve_expr(
    Parsed(expr, root): Parsed,
    allow_imports: bool,
) -> Result<Resolved, ImportError> {
    let resolve = |import: &Import| -> Result<SubExpr<X, X>, ImportError> {
        if allow_imports {
            let expr = resolve_import(import, &root)?;
            Ok(expr.roll())
        } else {
            Err(ImportError::UnexpectedImportError(import.clone()))
        }
    };
    let expr = expr.as_ref().traverse_embed(&resolve)?;
    Ok(Resolved(expr.squash_embed()))
}

pub fn load_from_file(f: &Path) -> Result<Parsed, ImportError> {
    let mut buffer = String::new();
    File::open(f)?.read_to_string(&mut buffer)?;
    let expr = parse_expr(&*buffer)?;
    let root = ImportRoot::LocalDir(f.parent().unwrap().to_owned());
    Ok(Parsed(expr, root))
}

// Deprecated
pub fn load_dhall_file(
    f: &Path,
    resolve_imports: bool,
) -> Result<Expr<X, X>, ImportError> {
    let expr = load_from_file(f)?;
    let expr = resolve_expr(expr, resolve_imports)?;
    Ok(expr.0.unroll())
}

// Deprecated
pub fn load_dhall_file_no_resolve_imports(
    f: &Path,
) -> Result<ParsedExpr, ImportError> {
    Ok(load_from_file(f)?.0)
}
