// use dhall_core::{Expr, FilePrefix, Import, ImportLocation, ImportMode, X};
use dhall_core::{Expr, Import, X};
// use std::path::Path;
use crate::error::Error;
use crate::expr::*;
use dhall_core::*;
use quick_error::quick_error;
use std::fs::File;
use std::io::Read;
use std::path::Path;
use std::path::PathBuf;

quick_error! {
    #[derive(Debug)]
    pub enum ImportError {
        Recursive(import: Import, err: Box<Error>) {}
        UnexpectedImport(import: Import) {}
    }
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
            Ok(load_dhall_file(&path, true).map_err(|e| {
                ImportError::Recursive(import.clone(), Box::new(e))
            })?)
        }
        _ => unimplemented!("{:?}", import),
    }
}

fn resolve_expr(
    Parsed(expr, root): Parsed,
    allow_imports: bool,
) -> Result<Resolved, ImportError> {
    let resolve = |import: &Import| -> Result<SubExpr<X, X>, ImportError> {
        if allow_imports {
            let expr = resolve_import(import, &root)?;
            Ok(expr.roll())
        } else {
            Err(ImportError::UnexpectedImport(import.clone()))
        }
    };
    let expr = expr.as_ref().traverse_embed(&resolve)?;
    Ok(Resolved(expr.squash_embed()))
}

impl Parsed {
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

    pub fn parse_binary_file(f: &Path) -> Result<Parsed, Error> {
        let mut buffer = Vec::new();
        File::open(f)?.read_to_end(&mut buffer)?;
        let expr = crate::binary::decode(&buffer)?;
        let root = ImportRoot::LocalDir(f.parent().unwrap().to_owned());
        Ok(Parsed(expr, root))
    }

    pub fn resolve(self) -> Result<Resolved, ImportError> {
        crate::imports::resolve_expr(self, true)
    }
    pub fn skip_resolve(self) -> Result<Resolved, ImportError> {
        crate::imports::resolve_expr(self, false)
    }
}

// Deprecated
pub fn load_dhall_file(
    f: &Path,
    resolve_imports: bool,
) -> Result<Expr<X, X>, Error> {
    let expr = Parsed::parse_file(f)?;
    let expr = resolve_expr(expr, resolve_imports)?;
    Ok(expr.0.unroll())
}
