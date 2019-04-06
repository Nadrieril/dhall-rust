// use dhall_core::{Expr, FilePrefix, Import, ImportLocation, ImportMode, X};
use dhall_core::{Expr, Import, X};
// use std::path::Path;
use dhall_core::*;
use std::fmt;
use std::fs::File;
use std::io::Read;
use std::path::Path;
use std::path::PathBuf;

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

#[derive(Debug)]
pub enum ImportError {
    ParseError(ParseError),
    IOError(std::io::Error),
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
        }
    }
}

pub fn load_dhall_file(
    f: &Path,
    resolve_imports: bool,
) -> Result<Expr<X, X>, ImportError> {
    let mut buffer = String::new();
    File::open(f)?.read_to_string(&mut buffer)?;
    let expr = parse_expr(&*buffer)?;
    let expr = if resolve_imports {
        let root = ImportRoot::LocalDir(f.parent().unwrap().to_owned());
        let resolve = |import: &Import| -> Expr<X, X> {
            resolve_import(import, &root).unwrap()
        };
        expr.as_ref().map_embed(&resolve).squash_embed()
    } else {
        panic_imports(expr.as_ref())
    };
    Ok(expr)
}

pub fn load_dhall_file_no_resolve_imports(
    f: &Path,
) -> Result<ParsedExpr, ImportError> {
    let mut buffer = String::new();
    File::open(f)?.read_to_string(&mut buffer)?;
    let expr = parse_expr(&*buffer)?;
    Ok(expr)
}
