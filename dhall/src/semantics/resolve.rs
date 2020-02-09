use std::collections::HashMap;
use std::path::{Path, PathBuf};

use crate::error::{Error, ImportError};
use crate::syntax;
use crate::syntax::{BinOp, Expr, ExprKind, FilePath, ImportLocation, URL};
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

    pub fn handle_import(
        &mut self,
        import: Import,
        mut do_resolve: impl FnMut(
            &mut Self,
            &Import,
        ) -> Result<Normalized, ImportError>,
    ) -> Result<Normalized, ImportError> {
        if self.stack.contains(&import) {
            return Err(ImportError::ImportCycle(self.stack.clone(), import));
        }
        Ok(match self.cache.get(&import) {
            Some(expr) => expr.clone(),
            None => {
                // Push the current import on the stack
                self.stack.push(import.clone());

                // Resolve the import recursively
                let expr = do_resolve(self, &import)?;

                // Remove import from the stack.
                self.stack.pop();

                // Add the import to the cache
                self.cache.insert(import, expr.clone());

                expr
            }
        })
    }
}

fn resolve_one_import(
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
    let parsed = Parsed::parse_file(f)?;
    Ok(resolve_with_env(env, parsed)?.typecheck()?.normalize())
}

/// Traverse the expression, handling import alternatives and passing
/// found imports to the provided function.
fn traverse_resolve_expr(
    expr: &Expr<Normalized>,
    f: &mut impl FnMut(Import) -> Result<Normalized, ImportError>,
) -> Result<Expr<Normalized>, ImportError> {
    Ok(match expr.kind() {
        ExprKind::BinOp(BinOp::ImportAlt, l, r) => {
            match traverse_resolve_expr(l, f) {
                Ok(l) => l,
                Err(_) => {
                    match traverse_resolve_expr(r, f) {
                        Ok(r) => r,
                        // TODO: keep track of the other error too
                        Err(e) => return Err(e),
                    }
                }
            }
        }
        kind => {
            let kind = kind.traverse_ref(|e| traverse_resolve_expr(e, f))?;
            expr.rewrap(match kind {
                ExprKind::Import(import) => ExprKind::Embed(f(import)?),
                kind => kind,
            })
        }
    })
}

fn resolve_with_env(
    env: &mut ResolveEnv,
    parsed: Parsed,
) -> Result<Resolved, ImportError> {
    let Parsed(expr, root) = parsed;
    let resolved = traverse_resolve_expr(&expr, &mut |import| {
        env.handle_import(import, |env, import| {
            resolve_one_import(env, import, &root)
        })
    })?;
    Ok(Resolved(resolved))
}

pub(crate) fn resolve(parsed: Parsed) -> Result<Resolved, ImportError> {
    resolve_with_env(&mut ResolveEnv::new(), parsed)
}

pub(crate) fn skip_resolve_expr(
    parsed: Parsed,
) -> Result<Resolved, ImportError> {
    let Parsed(expr, _) = parsed;
    let resolved = traverse_resolve_expr(&expr, &mut |import| {
        Err(ImportError::UnexpectedImport(import))
    })?;
    Ok(Resolved(resolved))
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
