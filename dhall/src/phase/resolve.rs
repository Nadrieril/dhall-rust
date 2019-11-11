use std::collections::HashMap;
use std::path::{Path, PathBuf};

use crate::error::{Error, ImportError};
use crate::phase::{Normalized, NormalizedExpr, Parsed, Resolved};
use dhall_syntax::{FilePath, ImportLocation, URL};

type Import = dhall_syntax::Import<NormalizedExpr>;

/// A root from which to resolve relative imports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ImportRoot {
    LocalDir(PathBuf),
}

type ImportCache = HashMap<Import, Normalized>;

pub(crate) type ImportStack = Vec<Import>;

fn resolve_import(
    import: &Import,
    root: &ImportRoot,
    import_cache: &mut ImportCache,
    import_stack: &ImportStack,
) -> Result<Normalized, ImportError> {
    use self::ImportRoot::*;
    use dhall_syntax::FilePrefix::*;
    use dhall_syntax::ImportLocation::*;
    let cwd = match root {
        LocalDir(cwd) => cwd,
    };
    match &import.location {
        Local(prefix, path) => {
            let path_buf: PathBuf = path.file_path.iter().collect();
            let path_buf = match prefix {
                // TODO: fail gracefully
                Parent => cwd.parent().unwrap().join(path_buf),
                Here => cwd.join(path_buf),
                _ => unimplemented!("{:?}", import),
            };
            Ok(load_import(&path_buf, import_cache, import_stack).map_err(
                |e| ImportError::Recursive(import.clone(), Box::new(e)),
            )?)
        }
        _ => unimplemented!("{:?}", import),
    }
}

fn load_import(
    f: &Path,
    import_cache: &mut ImportCache,
    import_stack: &ImportStack,
) -> Result<Normalized, Error> {
    Ok(
        do_resolve_expr(Parsed::parse_file(f)?, import_cache, import_stack)?
            .typecheck()?
            .normalize(),
    )
}

fn do_resolve_expr(
    parsed: Parsed,
    import_cache: &mut ImportCache,
    import_stack: &ImportStack,
) -> Result<Resolved, ImportError> {
    let Parsed(mut expr, root) = parsed;
    let mut resolve = |import: Import| -> Result<Normalized, ImportError> {
        if import_stack.contains(&import) {
            return Err(ImportError::ImportCycle(import_stack.clone(), import));
        }
        match import_cache.get(&import) {
            Some(expr) => Ok(expr.clone()),
            None => {
                // Copy the import stack and push the current import
                let mut import_stack = import_stack.clone();
                import_stack.push(import.clone());

                // Resolve the import recursively
                let expr = resolve_import(
                    &import,
                    &root,
                    import_cache,
                    &import_stack,
                )?;

                // Add the import to the cache
                import_cache.insert(import, expr.clone());
                Ok(expr)
            }
        }
    };
    expr.traverse_resolve_mut(&mut resolve)?;
    Ok(Resolved(expr))
}

pub(crate) fn resolve(e: Parsed) -> Result<Resolved, ImportError> {
    do_resolve_expr(e, &mut HashMap::new(), &Vec::new())
}

pub(crate) fn skip_resolve_expr(
    parsed: Parsed,
) -> Result<Resolved, ImportError> {
    let mut expr = parsed.0;
    let mut resolve = |import: Import| -> Result<Normalized, ImportError> {
        Err(ImportError::UnexpectedImport(import))
    };
    expr.traverse_resolve_mut(&mut resolve)?;
    Ok(Resolved(expr))
}

pub trait Canonicalize {
    fn canonicalize(&self) -> Self;
}

impl Canonicalize for FilePath {
    fn canonicalize(&self) -> FilePath {
        let mut file_path = Vec::new();
        let mut file_path_components = self.file_path.clone().into_iter();

        loop {
            let component = file_path_components.next();
            match component.as_ref() {
                // ───────────────────
                // canonicalize(ε) = ε
                None => break,

                // canonicalize(directory₀) = directory₁
                // ───────────────────────────────────────
                // canonicalize(directory₀/.) = directory₁
                Some(c) if c == "." => continue,

                Some(c) if c == ".." => match file_path_components.next() {
                    // canonicalize(directory₀) = ε
                    // ────────────────────────────
                    // canonicalize(directory₀/..) = /..
                    None => file_path.push("..".to_string()),

                    // canonicalize(directory₀) = directory₁/..
                    // ──────────────────────────────────────────────
                    // canonicalize(directory₀/..) = directory₁/../..
                    Some(ref c) if c == ".." => {
                        file_path.push("..".to_string());
                        file_path.push("..".to_string());
                    }

                    // canonicalize(directory₀) = directory₁/component
                    // ───────────────────────────────────────────────  ; If "component" is not
                    // canonicalize(directory₀/..) = directory₁         ; ".."
                    Some(_) => continue,
                },

                // canonicalize(directory₀) = directory₁
                // ─────────────────────────────────────────────────────────  ; If no other
                // canonicalize(directory₀/component) = directory₁/component  ; rule matches
                Some(c) => file_path.push(c.clone()),
            }
        }

        FilePath { file_path }
    }
}

impl<SE: Copy> Canonicalize for ImportLocation<SE> {
    fn canonicalize(&self) -> ImportLocation<SE> {
        match self {
            ImportLocation::Local(prefix, file) => {
                ImportLocation::Local(*prefix, file.canonicalize())
            }
            ImportLocation::Remote(url) => ImportLocation::Remote(URL {
                scheme: url.scheme,
                authority: url.authority.clone(),
                path: url.path.canonicalize(),
                query: url.query.clone(),
                headers: url.headers.clone(),
            }),
            ImportLocation::Env(name) => ImportLocation::Env(name.to_string()),
            ImportLocation::Missing => ImportLocation::Missing,
        }
    }
}

#[cfg(test)]
#[rustfmt::skip]
mod spec_tests {
    macro_rules! import_success {
        ($name:ident, $path:expr) => {
            make_spec_test!(
                ImportSuccess(
                    &("../dhall-lang/tests/import/success/".to_owned() + $path + "A.dhall"),
                    &("../dhall-lang/tests/import/success/".to_owned() + $path + "B.dhall")
                ),
                $name
            );
        };
    }

    // macro_rules! import_failure {
    //     ($name:ident, $path:expr) => {
    //         make_spec_test!(
    //             ImportFailure(&("../dhall-lang/tests/import/failure/".to_owned() + $path + ".dhall")),
    //             $name
    //         );
    //     };
    // }

    // import_success!(success_alternativeEnvNatural, "alternativeEnvNatural");
    // import_success!(success_alternativeEnvSimple, "alternativeEnvSimple");
    // import_success!(success_alternativeHashMismatch, "alternativeHashMismatch");
    import_success!(success_alternativeNatural, "alternativeNatural");
    import_success!(success_alternativeParseError, "alternativeParseError");
    import_success!(success_alternativeTypeError, "alternativeTypeError");
    // import_success!(success_asLocation, "asLocation");
    // import_success!(success_asText, "asText");
    // import_success!(success_customHeaders, "customHeaders");
    import_success!(success_fieldOrder, "fieldOrder");
    // note: this one needs special setup with env variables
    // import_success!(success_hashFromCache, "hashFromCache");
    // import_success!(success_headerForwarding, "headerForwarding");
    // import_success!(success_nestedHash, "nestedHash");
    // import_success!(success_noHeaderForwarding, "noHeaderForwarding");
    // import_failure!(failure_alternativeEnv, "alternativeEnv");
    // import_failure!(failure_alternativeEnvMissing, "alternativeEnvMissing");
    // import_failure!(failure_cycle, "cycle");
    // import_failure!(failure_hashMismatch, "hashMismatch");
    // import_failure!(failure_missing, "missing");
    // import_failure!(failure_referentiallyInsane, "referentiallyInsane");
}
