use std::collections::HashMap;
use std::path::{Path, PathBuf};

use crate::error::{Error, ImportError};
use crate::syntax;
use crate::syntax::{FilePath, ImportLocation, URL};
use crate::{Normalized, NormalizedExpr, Parsed, Resolved};

type Import = syntax::Import<NormalizedExpr>;

/// A root from which to resolve relative imports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ImportRoot {
    LocalDir(PathBuf),
}

type ImportCache = HashMap<Import, Normalized>;

pub(crate) type ImportStack = Vec<Import>;

struct ResolveEnv {
    cache: ImportCache,
    stack: ImportStack,
}

impl ResolveEnv {
    pub fn new() -> Self {
        ResolveEnv {
            cache: HashMap::new(),
            stack: Vec::new(),
        }
    }
    pub fn to_import_stack(&self) -> ImportStack {
        self.stack.clone()
    }
    pub fn check_cyclic_import(&self, import: &Import) -> bool {
        self.stack.contains(import)
    }
    pub fn get_from_cache(&self, import: &Import) -> Option<&Normalized> {
        self.cache.get(import)
    }
    pub fn push_on_stack(&mut self, import: Import) {
        self.stack.push(import)
    }
    pub fn pop_from_stack(&mut self) {
        self.stack.pop();
    }
    pub fn insert_cache(&mut self, import: Import, expr: Normalized) {
        self.cache.insert(import, expr);
    }
}

fn resolve_import(
    env: &mut ResolveEnv,
    import: &Import,
    root: &ImportRoot,
) -> Result<Normalized, ImportError> {
    use self::ImportRoot::*;
    use syntax::FilePrefix::*;
    use syntax::ImportLocation::*;
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
            Ok(load_import(env, &path_buf).map_err(|e| {
                ImportError::Recursive(import.clone(), Box::new(e))
            })?)
        }
        _ => unimplemented!("{:?}", import),
    }
}

fn load_import(env: &mut ResolveEnv, f: &Path) -> Result<Normalized, Error> {
    Ok(do_resolve_expr(env, Parsed::parse_file(f)?)?
        .typecheck()?
        .normalize())
}

fn do_resolve_expr(
    env: &mut ResolveEnv,
    parsed: Parsed,
) -> Result<Resolved, ImportError> {
    let Parsed(mut expr, root) = parsed;
    let mut resolve = |import: Import| -> Result<Normalized, ImportError> {
        if env.check_cyclic_import(&import) {
            return Err(ImportError::ImportCycle(
                env.to_import_stack(),
                import,
            ));
        }
        match env.get_from_cache(&import) {
            Some(expr) => Ok(expr.clone()),
            None => {
                // Push the current import on the stack
                env.push_on_stack(import.clone());

                // Resolve the import recursively
                let expr = resolve_import(env, &import, &root)?;

                // Remove import from the stack.
                env.pop_from_stack();

                // Add the import to the cache
                env.insert_cache(import, expr.clone());

                Ok(expr)
            }
        }
    };
    expr.traverse_resolve_mut(&mut resolve)?;
    Ok(Resolved(expr))
}

pub(crate) fn resolve(e: Parsed) -> Result<Resolved, ImportError> {
    do_resolve_expr(&mut ResolveEnv::new(), e)
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
