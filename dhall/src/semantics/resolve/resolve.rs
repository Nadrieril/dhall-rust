use itertools::Itertools;
use std::borrow::Cow;
use std::collections::BTreeMap;
use std::env;
use std::path::PathBuf;
use url::Url;

use crate::builtins::Builtin;
use crate::error::ErrorBuilder;
use crate::error::{Error, ImportError};
use crate::operations::{BinOp, OpKind};
use crate::semantics::{mkerr, Cache, Hir, HirKind, ImportEnv, NameEnv, Type};
use crate::syntax;
use crate::syntax::{
    Expr, ExprKind, FilePath, FilePrefix, Hash, ImportMode, ImportTarget, Span,
    UnspannedExpr, URL,
};
use crate::{Parsed, Resolved};

// TODO: evaluate import headers
pub type Import = syntax::Import<()>;

/// Owned Hir with a type. Different from Tir because the Hir is owned.
pub type TypedHir = (Hir, Type);

/// The location of some data, usually some dhall code.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ImportLocation {
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
    /// `sanity_check` indicates whether to check if that location is allowed to be referenced,
    /// for example to prevent a remote file from reading an environment variable.
    fn chain(
        &self,
        target: &ImportTarget<()>,
        sanity_check: bool,
    ) -> Result<ImportLocation, Error> {
        Ok(match target {
            ImportTarget::Local(prefix, path) => {
                self.chain_local(*prefix, path)?
            }
            ImportTarget::Remote(remote) => {
                if sanity_check {
                    if let ImportLocation::Remote(..) = self {
                        // TODO: allow if CORS check passes
                        return Err(ImportError::SanityCheck.into());
                    }
                }
                let mut url = Url::parse(&format!(
                    "{}://{}",
                    remote.scheme, remote.authority
                ))?;
                url.set_path(&remote.path.file_path.iter().join("/"));
                url.set_query(remote.query.as_ref().map(String::as_ref));
                ImportLocation::Remote(url)
            }
            ImportTarget::Env(var_name) => {
                if sanity_check {
                    if let ImportLocation::Remote(..) = self {
                        return Err(ImportError::SanityCheck.into());
                    }
                }
                ImportLocation::Env(var_name.clone())
            }
            ImportTarget::Missing => ImportLocation::Missing,
        })
    }

    fn chain_local(
        &self,
        prefix: FilePrefix,
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

    fn fetch_dhall(self) -> Result<Parsed, Error> {
        Ok(match self {
            ImportLocation::Local(path) => Parsed::parse_file(&path)?,
            ImportLocation::Remote(url) => Parsed::parse_remote(url)?,
            ImportLocation::Env(var_name) => {
                let val = match env::var(var_name) {
                    Ok(val) => val,
                    Err(_) => return Err(ImportError::MissingEnvVar.into()),
                };
                Parsed::parse_str(&val)?
            }
            ImportLocation::Missing => return Err(ImportError::Missing.into()),
        })
    }

    fn fetch_text(self) -> Result<String, Error> {
        Ok(match self {
            ImportLocation::Local(path) => std::fs::read_to_string(&path)?,
            ImportLocation::Remote(url) => download_http_text(url)?,
            ImportLocation::Env(var_name) => match env::var(var_name) {
                Ok(val) => val,
                Err(_) => return Err(ImportError::MissingEnvVar.into()),
            },
            ImportLocation::Missing => return Err(ImportError::Missing.into()),
        })
    }

    fn into_location(self) -> Expr {
        let (field_name, arg) = match self {
            ImportLocation::Local(path) => {
                ("Local", Some(path.to_string_lossy().into_owned()))
            }
            ImportLocation::Remote(url) => ("Remote", Some(url.into_string())),
            ImportLocation::Env(name) => ("Environment", Some(name)),
            ImportLocation::Missing => ("Missing", None),
        };

        let asloc_ty = make_aslocation_uniontype();
        let expr =
            mkexpr(ExprKind::Op(OpKind::Field(asloc_ty, field_name.into())));
        match arg {
            Some(arg) => mkexpr(ExprKind::Op(OpKind::App(
                expr,
                mkexpr(ExprKind::TextLit(arg.into())),
            ))),
            None => expr,
        }
    }
}

fn mkexpr(kind: UnspannedExpr) -> Expr {
    Expr::new(kind, Span::Artificial)
}

// TODO: error handling
#[cfg(not(target_arch = "wasm32"))]
pub(crate) fn download_http_text(url: Url) -> Result<String, Error> {
    Ok(reqwest::blocking::get(url).unwrap().text().unwrap())
}
#[cfg(target_arch = "wasm32")]
pub(crate) fn download_http_text(url: Url) -> Result<String, Error> {
    blocking::block_on(async {
        Ok(reqwest::get(url).await.unwrap().text().await.unwrap())
    })
}

fn make_aslocation_uniontype() -> Expr {
    let text_type = mkexpr(ExprKind::Builtin(Builtin::Text));
    let mut union = BTreeMap::default();
    union.insert("Local".into(), Some(text_type.clone()));
    union.insert("Remote".into(), Some(text_type.clone()));
    union.insert("Environment".into(), Some(text_type));
    union.insert("Missing".into(), None);
    mkexpr(ExprKind::UnionType(union))
}

fn resolve_one_import(
    env: &mut ImportEnv,
    cache: &Cache,
    import: &Import,
    location: &ImportLocation,
    span: Span,
) -> Result<TypedHir, Error> {
    let do_sanity_check = import.mode != ImportMode::Location;
    let location = location.chain(&import.location, do_sanity_check)?;
    env.handle_import(location.clone(), |env| match import.mode {
        ImportMode::Code => {
            let (hir, ty) = cache.caching_import(
                import,
                || location.fetch_dhall(),
                |parsed| {
                    let typed =
                        resolve_with_env(env, cache, parsed)?.typecheck()?;
                    let hir = typed.normalize().to_hir();
                    Ok((hir, typed.ty))
                },
            )?;
            match &import.hash {
                Some(Hash::SHA256(hash)) => {
                    let actual_hash = hir.to_expr_alpha().hash()?;
                    if hash[..] != actual_hash[..] {
                        mkerr(
                            ErrorBuilder::new("hash mismatch")
                                .span_err(span, "hash mismatch")
                                .note(format!(
                                    "Expected sha256:{}",
                                    hex::encode(hash)
                                ))
                                .note(format!(
                                    "Found    sha256:{}",
                                    hex::encode(actual_hash)
                                ))
                                .format(),
                        )?
                    }
                }
                None => {}
            }
            Ok((hir, ty))
        }
        ImportMode::RawText => {
            let text = location.fetch_text()?;
            let hir = Hir::new(
                HirKind::Expr(ExprKind::TextLit(text.into())),
                Span::Artificial,
            );
            Ok((hir, Type::from_builtin(Builtin::Text)))
        }
        ImportMode::Location => {
            let expr = location.into_location();
            let hir = skip_resolve_expr(&expr)?;
            let ty = hir.typecheck_noenv()?.ty().clone();
            Ok((hir, ty))
        }
    })
}

/// Desugar the first level of the expression.
fn desugar(expr: &Expr) -> Cow<'_, Expr> {
    match expr.kind() {
        ExprKind::Op(OpKind::Completion(ty, compl)) => {
            let ty_field_default = Expr::new(
                ExprKind::Op(OpKind::Field(ty.clone(), "default".into())),
                expr.span(),
            );
            let merged = Expr::new(
                ExprKind::Op(OpKind::BinOp(
                    BinOp::RightBiasedRecordMerge,
                    ty_field_default,
                    compl.clone(),
                )),
                expr.span(),
            );
            let ty_field_type = Expr::new(
                ExprKind::Op(OpKind::Field(ty.clone(), "Type".into())),
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
    f: &mut impl FnMut(Import, Span) -> Result<TypedHir, Error>,
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
        ExprKind::Op(OpKind::BinOp(BinOp::ImportAlt, l, r)) => {
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
                if l.is_some() {
                    name_env.remove_mut();
                }
                Ok::<_, Error>(hir)
            })?;
            let kind = match kind {
                ExprKind::Import(import) => {
                    // TODO: evaluate import headers
                    let import = import.traverse_ref(|_| Ok::<_, Error>(()))?;
                    let imported = f(import, expr.span())?;
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
    cache: &Cache,
    parsed: Parsed,
) -> Result<Resolved, Error> {
    let Parsed(expr, location) = parsed;
    let resolved = traverse_resolve_expr(
        &mut NameEnv::new(),
        &expr,
        &mut |import, span| {
            resolve_one_import(env, cache, &import, &location, span)
        },
    )?;
    Ok(Resolved(resolved))
}

pub fn resolve(parsed: Parsed) -> Result<Resolved, Error> {
    let cache = Cache::new();
    resolve_with_env(&mut ImportEnv::new(), &cache, parsed)
}

pub fn skip_resolve_expr(expr: &Expr) -> Result<Hir, Error> {
    traverse_resolve_expr(&mut NameEnv::new(), expr, &mut |import, _span| {
        Err(ImportError::UnexpectedImport(import).into())
    })
}

pub fn skip_resolve(parsed: Parsed) -> Result<Resolved, Error> {
    let Parsed(expr, _) = parsed;
    let resolved = skip_resolve_expr(&expr)?;
    Ok(Resolved(resolved))
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
                headers: url.headers,
            }),
            ImportTarget::Env(name) => ImportTarget::Env(name.to_string()),
            ImportTarget::Missing => ImportTarget::Missing,
        }
    }
}
