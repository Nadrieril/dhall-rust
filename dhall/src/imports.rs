use crate::error::Error;
use crate::expr::*;
use dhall_syntax::*;
use std::collections::HashMap;
use std::fs::File;
use std::io::Read;
use std::path::Path;
use std::path::PathBuf;

#[derive(Debug)]
pub enum ImportError {
    Recursive(Import, Box<Error>),
    UnexpectedImport(Import),
    ImportCycle(ImportStack, Import),
}

/// A root from which to resolve relative imports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportRoot {
    LocalDir(PathBuf),
}

type ImportCache = HashMap<Import, Normalized<'static>>;

type ImportStack = Vec<Import>;

fn resolve_import(
    import: &Import,
    root: &ImportRoot,
    import_cache: &mut ImportCache,
    import_stack: &ImportStack,
) -> Result<Normalized<'static>, ImportError> {
    use self::ImportRoot::*;
    use dhall_syntax::FilePrefix::*;
    use dhall_syntax::ImportLocation::*;
    let cwd = match root {
        LocalDir(cwd) => cwd,
    };
    match &import.location_hashed.location {
        Local(prefix, path) => {
            let path = match prefix {
                // TODO: fail gracefully
                Parent => cwd.parent().unwrap().join(path),
                Here => cwd.join(path),
                _ => unimplemented!("{:?}", import),
            };
            Ok(load_import(&path, import_cache, import_stack).map_err(|e| {
                ImportError::Recursive(import.clone(), Box::new(e))
            })?)
        }
        _ => unimplemented!("{:?}", import),
    }
}

fn load_import(
    f: &Path,
    import_cache: &mut ImportCache,
    import_stack: &ImportStack,
) -> Result<Normalized<'static>, Error> {
    Ok(
        do_resolve_expr(Parsed::parse_file(f)?, import_cache, import_stack)?
            .typecheck()?
            .normalize(),
    )
}

fn do_resolve_expr<'a>(
    Parsed(expr, root): Parsed<'a>,
    import_cache: &mut ImportCache,
    import_stack: &ImportStack,
) -> Result<Resolved<'a>, ImportError> {
    let resolve =
        |import: &Import| -> Result<Normalized<'static>, ImportError> {
            if import_stack.contains(import) {
                return Err(ImportError::ImportCycle(
                    import_stack.clone(),
                    import.clone(),
                ));
            }
            match import_cache.get(import) {
                Some(expr) => Ok(expr.clone()),
                None => {
                    // Copy the import stack and push the current import
                    let mut import_stack = import_stack.clone();
                    import_stack.push(import.clone());

                    // Resolve the import recursively
                    let expr = resolve_import(
                        import,
                        &root,
                        import_cache,
                        &import_stack,
                    )?;

                    // Add the import to the cache
                    import_cache.insert(import.clone(), expr.clone());
                    Ok(expr)
                }
            }
        };
    let expr = expr.traverse_embed(resolve)?;
    Ok(Resolved(expr))
}

fn skip_resolve_expr(
    Parsed(expr, _root): Parsed<'_>,
) -> Result<Resolved<'_>, ImportError> {
    let resolve =
        |import: &Import| -> Result<Normalized<'static>, ImportError> {
            Err(ImportError::UnexpectedImport(import.clone()))
        };
    let expr = expr.traverse_embed(resolve)?;
    Ok(Resolved(expr))
}

impl<'a> Parsed<'a> {
    pub fn parse_file(f: &Path) -> Result<Parsed<'a>, Error> {
        let mut buffer = String::new();
        File::open(f)?.read_to_string(&mut buffer)?;
        let expr = parse_expr(&*buffer)?;
        let root = ImportRoot::LocalDir(f.parent().unwrap().to_owned());
        Ok(Parsed(expr.unnote().note_absurd(), root))
    }

    pub fn parse_str(s: &'a str) -> Result<Parsed<'a>, Error> {
        let expr = parse_expr(s)?;
        let root = ImportRoot::LocalDir(std::env::current_dir()?);
        Ok(Parsed(expr, root))
    }

    #[allow(dead_code)]
    pub fn parse_binary_file(f: &Path) -> Result<Parsed<'a>, Error> {
        let mut buffer = Vec::new();
        File::open(f)?.read_to_end(&mut buffer)?;
        let expr = crate::binary::decode(&buffer)?;
        let root = ImportRoot::LocalDir(f.parent().unwrap().to_owned());
        Ok(Parsed(expr.note_absurd(), root))
    }

    pub fn resolve(self) -> Result<Resolved<'a>, ImportError> {
        crate::imports::do_resolve_expr(self, &mut HashMap::new(), &Vec::new())
    }

    #[allow(dead_code)]
    pub fn skip_resolve(self) -> Result<Resolved<'a>, ImportError> {
        crate::imports::skip_resolve_expr(self)
    }
}

#[cfg(test)]
mod spec_tests {
    #![rustfmt::skip]

    macro_rules! import_success {
        ($name:ident, $path:expr) => {
            make_spec_test!(Import, Success, $name, $path);
        };
    }

    // macro_rules! import_failure {
    //     ($name:ident, $path:expr) => {
    //         make_spec_test!(Import, Failure, $name, $path);
    //     };
    // }

    // import_success!(success_alternativeEnvNatural, "alternativeEnvNatural");
    // import_success!(success_alternativeEnvSimple, "alternativeEnvSimple");
    // import_success!(success_alternativeNatural, "alternativeNatural");
    // import_success!(success_asText, "asText");
    import_success!(success_fieldOrder, "fieldOrder");
    // import_failure!(failure_alternativeEnv, "alternativeEnv");
    // import_failure!(failure_alternativeEnvMissing, "alternativeEnvMissing");
    // import_failure!(failure_cycle, "cycle");
    // import_failure!(failure_missing, "missing");
    // import_failure!(failure_referentiallyInsane, "referentiallyInsane");
}
