use std::collections::HashMap;
use std::path::{Path, PathBuf};

use crate::error::ErrorBuilder;
use crate::error::{Error, ImportError};
use crate::semantics::{mkerr, Hir, HirKind, NameEnv};
use crate::syntax;
use crate::syntax::{BinOp, Expr, ExprKind, FilePath, ImportLocation, URL};
use crate::{Parsed, ParsedExpr, Resolved};

type Import = syntax::Import<Hir>;

/// A root from which to resolve relative imports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ImportRoot {
    LocalDir(PathBuf),
}

type ImportCache = HashMap<Import, Hir>;

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
        mut do_resolve: impl FnMut(&mut Self, &Import) -> Result<Hir, Error>,
    ) -> Result<Hir, Error> {
        if self.stack.contains(&import) {
            return Err(
                ImportError::ImportCycle(self.stack.clone(), import).into()
            );
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
) -> Result<Hir, Error> {
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
            Ok(load_import(env, &path_buf)?)
        }
        _ => unimplemented!("{:?}", import),
    }
}

fn load_import(env: &mut ResolveEnv, f: &Path) -> Result<Hir, Error> {
    let parsed = Parsed::parse_file(f)?;
    Ok(resolve_with_env(env, parsed)?
        .typecheck()?
        .normalize()
        .to_hir())
}

/// Traverse the expression, handling import alternatives and passing
/// found imports to the provided function.
fn traverse_resolve_expr(
    name_env: &mut NameEnv,
    expr: &Expr,
    f: &mut impl FnMut(Import) -> Result<Hir, Error>,
) -> Result<Hir, Error> {
    Ok(match expr.kind() {
        ExprKind::Var(var) => match name_env.unlabel_var(&var) {
            Some(v) => Hir::new(HirKind::Var(v), expr.span()),
            None => mkerr(
                ErrorBuilder::new(format!("unbound variable `{}`", var))
                    .span_err(expr.span(), "not found in this scope")
                    .format(),
            )?,
        },
        ExprKind::BinOp(BinOp::ImportAlt, l, r) => {
            match traverse_resolve_expr(name_env, l, f) {
                Ok(l) => l,
                Err(_) => {
                    match traverse_resolve_expr(name_env, r, f) {
                        Ok(r) => r,
                        // TODO: keep track of the other error too
                        Err(e) => return Err(e),
                    }
                }
            }
        }
        // Desugar
        ExprKind::Completion(ty, compl) => {
            let ty_field_default = Expr::new(
                ExprKind::Field(ty.clone(), "default".into()),
                expr.span(),
            );
            let merged = Expr::new(
                ExprKind::BinOp(
                    BinOp::RightBiasedRecordMerge,
                    ty_field_default,
                    compl.clone(),
                ),
                expr.span(),
            );
            let ty_field_type = Expr::new(
                ExprKind::Field(ty.clone(), "Type".into()),
                expr.span(),
            );
            let desugared =
                Expr::new(ExprKind::Annot(merged, ty_field_type), expr.span());
            traverse_resolve_expr(name_env, &desugared, f)?
        }
        kind => {
            let kind = kind.traverse_ref_maybe_binder(|l, e| {
                if let Some(l) = l {
                    name_env.insert_mut(l);
                }
                let hir = traverse_resolve_expr(name_env, e, f)?;
                if let Some(_) = l {
                    name_env.remove_mut();
                }
                Ok::<_, Error>(hir)
            })?;
            let kind = match kind {
                ExprKind::Import(import) => f(import)?.kind().clone(),
                kind => HirKind::Expr(kind),
            };
            Hir::new(kind, expr.span())
        }
    })
}

fn resolve_with_env(
    env: &mut ResolveEnv,
    parsed: Parsed,
) -> Result<Resolved, Error> {
    let Parsed(expr, root) = parsed;
    let resolved =
        traverse_resolve_expr(&mut NameEnv::new(), &expr, &mut |import| {
            env.handle_import(import, |env, import| {
                resolve_one_import(env, import, &root)
            })
        })?;
    Ok(Resolved(resolved))
}

pub(crate) fn resolve(parsed: Parsed) -> Result<Resolved, Error> {
    resolve_with_env(&mut ResolveEnv::new(), parsed)
}

pub(crate) fn skip_resolve(expr: &ParsedExpr) -> Result<Hir, Error> {
    traverse_resolve_expr(&mut NameEnv::new(), expr, &mut |import| {
        Err(ImportError::UnexpectedImport(import).into())
    })
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
