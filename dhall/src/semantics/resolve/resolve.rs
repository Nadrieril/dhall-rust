use itertools::Itertools;
use std::borrow::Cow;
use std::env;
use std::path::PathBuf;
use url::Url;

use crate::error::ErrorBuilder;
use crate::error::{Error, ImportError};
use crate::semantics::{mkerr, Hir, HirKind, ImportEnv, NameEnv, Type};
use crate::syntax;
use crate::syntax::map::DupTreeMap;
use crate::syntax::{
    BinOp, Builtin, Expr, ExprKind, FilePath, FilePrefix, ImportMode,
    ImportTarget, Span, UnspannedExpr, URL,
};
use crate::{Parsed, ParsedExpr, Resolved};

// TODO: evaluate import headers
pub(crate) type Import = syntax::Import<()>;

/// Owned Hir with a type. Different from Tir because the Hir is owned.
pub(crate) type TypedHir = (Hir, Type);

/// The location of some data, usually some dhall code.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ImportLocation {
    /// Local file
    Local(PathBuf),
    /// Remote file
    Remote(Url),
    /// Environment variable
    Env(String),
    /// Data without a location
    Missing,
}

impl ImportLocation {
    /// Given an import pointing to `target` found in the current location, compute the next
    /// location, or error if not allowed.
    fn chain(
        &self,
        target: &ImportTarget<()>,
    ) -> Result<ImportLocation, Error> {
        Ok(match target {
            ImportTarget::Local(prefix, path) => {
                self.chain_local(prefix, path)?
            }
            ImportTarget::Remote(remote) => {
                let mut url = Url::parse(&format!(
                    "{}://{}",
                    remote.scheme, remote.authority
                ))?;
                url.set_path(&remote.path.file_path.iter().join("/"));
                url.set_query(remote.query.as_ref().map(String::as_ref));
                ImportLocation::Remote(url)
            }
            ImportTarget::Env(var_name) => {
                ImportLocation::Env(var_name.clone())
            }
            ImportTarget::Missing => ImportLocation::Missing,
        })
    }

    fn chain_local(
        &self,
        prefix: &FilePrefix,
        path: &FilePath,
    ) -> Result<ImportLocation, Error> {
        Ok(match self {
            ImportLocation::Local(..)
            | ImportLocation::Env(..)
            | ImportLocation::Missing => {
                let dir = match self {
                    ImportLocation::Local(path) => {
                        path.parent().unwrap().to_owned()
                    }
                    ImportLocation::Env(..) | ImportLocation::Missing => {
                        std::env::current_dir()?
                    }
                    _ => unreachable!(),
                };
                let mut dir: Vec<String> = dir
                    .components()
                    .map(|component| {
                        component.as_os_str().to_string_lossy().into_owned()
                    })
                    .collect();
                let root = match prefix {
                    FilePrefix::Here => dir,
                    FilePrefix::Parent => {
                        dir.push("..".to_string());
                        dir
                    }
                    FilePrefix::Absolute => vec![],
                    FilePrefix::Home => vec![],
                };
                let path: Vec<_> = root
                    .into_iter()
                    .chain(path.file_path.iter().cloned())
                    .collect();
                let path =
                    (FilePath { file_path: path }).canonicalize().file_path;
                let prefix = match prefix {
                    FilePrefix::Here | FilePrefix::Parent => ".",
                    FilePrefix::Absolute => "/",
                    FilePrefix::Home => "~",
                };
                let path =
                    Some(prefix.to_string()).into_iter().chain(path).collect();
                ImportLocation::Local(path)
            }
            ImportLocation::Remote(url) => {
                let mut url = url.clone();
                match prefix {
                    FilePrefix::Here => {}
                    FilePrefix::Parent => {
                        url = url.join("..")?;
                    }
                    FilePrefix::Absolute => panic!("error"),
                    FilePrefix::Home => panic!("error"),
                }
                url = url.join(&path.file_path.join("/"))?;
                ImportLocation::Remote(url)
            }
        })
    }
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

fn resolve_one_import(
    env: &mut ImportEnv,
    import: &Import,
    location: ImportLocation,
) -> Result<TypedHir, Error> {
    match import.mode {
        ImportMode::Code => {
            let parsed = match location {
                ImportLocation::Local(path) => Parsed::parse_file(&path)?,
                ImportLocation::Remote(url) => Parsed::parse_remote(url)?,
                ImportLocation::Env(var_name) => {
                    let val = match env::var(var_name) {
                        Ok(val) => val,
                        Err(_) => Err(ImportError::MissingEnvVar)?,
                    };
                    Parsed::parse_str(&val)?
                }
                ImportLocation::Missing => Err(ImportError::Missing)?,
            };

            let typed = resolve_with_env(env, parsed)?.typecheck()?;
            Ok((typed.normalize().to_hir(), typed.ty().clone()))
        }
        ImportMode::RawText => {
            let text = match location {
                ImportLocation::Local(path) => std::fs::read_to_string(&path)?,
                ImportLocation::Remote(url) => {
                    reqwest::blocking::get(url).unwrap().text().unwrap()
                }
                ImportLocation::Env(var_name) => match env::var(var_name) {
                    Ok(val) => val,
                    Err(_) => Err(ImportError::MissingEnvVar)?,
                },
                ImportLocation::Missing => Err(ImportError::Missing)?,
            };

            let hir = Hir::new(
                HirKind::Expr(ExprKind::TextLit(text.into())),
                Span::Artificial,
            );
            Ok((hir, Type::from_builtin(Builtin::Text)))
        }
        ImportMode::Location => {
            let (field_name, arg) = match location {
                ImportLocation::Local(path) => {
                    ("Local", Some(path.to_string_lossy().into_owned()))
                }
                ImportLocation::Remote(url) => {
                    ("Remote", Some(url.into_string()))
                }
                ImportLocation::Env(name) => ("Environment", Some(name)),
                ImportLocation::Missing => ("Missing", None),
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
    let Parsed(expr, location) = parsed;
    let resolved =
        traverse_resolve_expr(&mut NameEnv::new(), &expr, &mut |import| {
            let location = location.chain(&import.location)?;
            env.handle_import(location.clone(), |env| {
                resolve_one_import(env, &import, location)
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

impl<SE: Copy> Canonicalize for ImportTarget<SE> {
    fn canonicalize(&self) -> ImportTarget<SE> {
        match self {
            ImportTarget::Local(prefix, file) => {
                ImportTarget::Local(*prefix, file.canonicalize())
            }
            ImportTarget::Remote(url) => ImportTarget::Remote(URL {
                scheme: url.scheme,
                authority: url.authority.clone(),
                path: url.path.canonicalize(),
                query: url.query.clone(),
                headers: url.headers.clone(),
            }),
            ImportTarget::Env(name) => ImportTarget::Env(name.to_string()),
            ImportTarget::Missing => ImportTarget::Missing,
        }
    }
}
