use std::borrow::Cow;
use std::env;
use std::path::PathBuf;

use crate::error::ErrorBuilder;
use crate::error::{Error, ImportError};
use crate::semantics::{mkerr, Hir, HirKind, ImportEnv, NameEnv, Type};
use crate::syntax;
use crate::syntax::map::DupTreeMap;
use crate::syntax::{
    BinOp, Builtin, Expr, ExprKind, FilePath, FilePrefix, ImportLocation,
    ImportMode, Span, UnspannedExpr, URL,
};
use crate::{Parsed, ParsedExpr, Resolved};

// TODO: evaluate import headers
pub(crate) type Import = syntax::Import<()>;

/// Owned Hir with a type. Different from Tir because the Hir is owned.
pub(crate) type TypedHir = (Hir, Type);

/// A root from which to resolve relative imports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ImportRoot {
    LocalDir(PathBuf),
}

fn mkexpr(kind: UnspannedExpr) -> Expr {
    Expr::new(kind, Span::Artificial)
}

fn make_aslocation_uniontype() -> Expr {
    let text_type = mkexpr(ExprKind::Builtin(Builtin::Text));
    let mut union = DupTreeMap::default();
    union.insert("Local".into(), Some(text_type.clone()));
    union.insert("Remote".into(), Some(text_type.clone()));
    union.insert("Environment".into(), Some(text_type.clone()));
    union.insert("Missing".into(), None);
    mkexpr(ExprKind::UnionType(union))
}

fn compute_relative_path(
    root: &ImportRoot,
    prefix: &FilePrefix,
    path: &FilePath,
) -> PathBuf {
    let cwd = match root {
        ImportRoot::LocalDir(cwd) => cwd,
    };
    let mut cwd: Vec<String> = cwd
        .components()
        .map(|component| component.as_os_str().to_string_lossy().into_owned())
        .collect();
    let root = match prefix {
        FilePrefix::Here => cwd,
        FilePrefix::Parent => {
            cwd.push("..".to_string());
            cwd
        }
        FilePrefix::Absolute => vec![],
        FilePrefix::Home => vec![],
    };
    let path: Vec<_> = root
        .into_iter()
        .chain(path.file_path.iter().cloned())
        .collect();
    let path = (FilePath { file_path: path }).canonicalize().file_path;
    let prefix = match prefix {
        FilePrefix::Here | FilePrefix::Parent => ".",
        FilePrefix::Absolute => "/",
        FilePrefix::Home => "~",
    };
    Some(prefix.to_string()).into_iter().chain(path).collect()
}

fn resolve_one_import(
    env: &mut ImportEnv,
    import: &Import,
    root: &ImportRoot,
) -> Result<TypedHir, Error> {
    match import.mode {
        ImportMode::Code => {
            let parsed = match &import.location {
                ImportLocation::Local(prefix, path) => {
                    let path = compute_relative_path(root, prefix, path);
                    Parsed::parse_file(&path)?
                }
                ImportLocation::Env(var_name) => {
                    let val = match env::var(var_name) {
                        Ok(val) => val,
                        Err(_) => Err(ImportError::MissingEnvVar)?,
                    };
                    Parsed::parse_str(&val)?
                }
                ImportLocation::Missing => Err(ImportError::Missing)?,
                _ => unimplemented!("{:?}", import),
            };

            let typed = resolve_with_env(env, parsed)?.typecheck()?;
            Ok((typed.normalize().to_hir(), typed.ty().clone()))
        }
        ImportMode::RawText => {
            let text = match &import.location {
                ImportLocation::Local(prefix, path) => {
                    let path = compute_relative_path(root, prefix, path);
                    std::fs::read_to_string(path)?
                }
                ImportLocation::Env(var_name) => match env::var(var_name) {
                    Ok(val) => val,
                    Err(_) => Err(ImportError::MissingEnvVar)?,
                },
                ImportLocation::Missing => Err(ImportError::Missing)?,
                _ => unimplemented!("{:?}", import),
            };

            let hir = Hir::new(
                HirKind::Expr(ExprKind::TextLit(text.into())),
                Span::Artificial,
            );
            Ok((hir, Type::from_builtin(Builtin::Text)))
        }
        ImportMode::Location => {
            let (field_name, arg) = match &import.location {
                ImportLocation::Local(prefix, path) => {
                    let path = compute_relative_path(root, prefix, path)
                        .to_string_lossy()
                        .into_owned();
                    ("Local", Some(path))
                }
                ImportLocation::Env(name) => {
                    ("Environment", Some(name.clone()))
                }
                ImportLocation::Missing => ("Missing", None),
                _ => unimplemented!("{:?}", import),
            };

            let asloc_ty = make_aslocation_uniontype();
            let expr = mkexpr(ExprKind::Field(asloc_ty, field_name.into()));
            let expr = match arg {
                Some(arg) => mkexpr(ExprKind::App(
                    expr,
                    mkexpr(ExprKind::TextLit(arg.into())),
                )),
                None => expr,
            };

            let hir = skip_resolve(&expr)?;
            let ty = hir.typecheck_noenv()?.ty().clone();
            Ok((hir, ty))
        }
    }
}

/// Desugar the first level of the expression.
fn desugar(expr: &Expr) -> Cow<'_, Expr> {
    match expr.kind() {
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
            Cow::Owned(Expr::new(
                ExprKind::Annot(merged, ty_field_type),
                expr.span(),
            ))
        }
        _ => Cow::Borrowed(expr),
    }
}

/// Traverse the expression, handling import alternatives and passing
/// found imports to the provided function. Also resolving names.
fn traverse_resolve_expr(
    name_env: &mut NameEnv,
    expr: &Expr,
    f: &mut impl FnMut(Import) -> Result<TypedHir, Error>,
) -> Result<Hir, Error> {
    let expr = desugar(expr);
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
                ExprKind::Import(import) => {
                    // TODO: evaluate import headers
                    let import = import.traverse_ref(|_| Ok::<_, Error>(()))?;
                    let imported = f(import)?;
                    HirKind::Import(imported.0, imported.1)
                }
                kind => HirKind::Expr(kind),
            };
            Hir::new(kind, expr.span())
        }
    })
}

fn resolve_with_env(
    env: &mut ImportEnv,
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
    resolve_with_env(&mut ImportEnv::new(), parsed)
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

        for c in &self.file_path {
            match c.as_ref() {
                // canonicalize(directory₀) = directory₁
                // ───────────────────────────────────────
                // canonicalize(directory₀/.) = directory₁
                "." => continue,

                ".." => match file_path.last() {
                    // canonicalize(directory₀) = ε
                    // ────────────────────────────
                    // canonicalize(directory₀/..) = /..
                    None => file_path.push("..".to_string()),

                    // canonicalize(directory₀) = directory₁/..
                    // ──────────────────────────────────────────────
                    // canonicalize(directory₀/..) = directory₁/../..
                    Some(c) if c == ".." => file_path.push("..".to_string()),

                    // canonicalize(directory₀) = directory₁/component
                    // ───────────────────────────────────────────────  ; If "component" is not
                    // canonicalize(directory₀/..) = directory₁         ; ".."
                    Some(_) => {
                        file_path.pop();
                    }
                },

                // canonicalize(directory₀) = directory₁
                // ─────────────────────────────────────────────────────────  ; If no other
                // canonicalize(directory₀/component) = directory₁/component  ; rule matches
                _ => file_path.push(c.clone()),
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
