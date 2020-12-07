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
use crate::semantics::{mkerr, Hir, HirKind, ImportEnv, NameEnv, Type};
use crate::syntax;
use crate::syntax::{
    Expr, ExprKind, FilePath, FilePrefix, Hash, ImportMode, ImportTarget, Span,
    UnspannedExpr, URL,
};
use crate::{Ctxt, ImportId, ImportResultId, Parsed, Resolved, Typed};

// TODO: evaluate import headers
pub type Import = syntax::Import<()>;

/// The location of some data, usually some dhall code.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ImportLocationKind {
    /// Local file
    Local(PathBuf),
    /// Remote file
    Remote(Url),
    /// Environment variable
    Env(String),
    /// Data without a location; chaining will start from current directory.
    Missing,
    /// Token to signal that thi sfile should contain no imports.
    NoImport,
}

/// The location of some data.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ImportLocation {
    kind: ImportLocationKind,
    mode: ImportMode,
}

impl ImportLocationKind {
    fn chain_local(
        &self,
        prefix: FilePrefix,
        path: &FilePath,
    ) -> Result<Self, Error> {
        Ok(match self {
            ImportLocationKind::Local(..)
            | ImportLocationKind::Env(..)
            | ImportLocationKind::Missing => {
                let dir = match self {
                    ImportLocationKind::Local(path) => {
                        path.parent().unwrap().to_owned()
                    }
                    ImportLocationKind::Env(..)
                    | ImportLocationKind::Missing => std::env::current_dir()?,
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
                ImportLocationKind::Local(path)
            }
            ImportLocationKind::Remote(url) => {
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
                ImportLocationKind::Remote(url)
            }
            ImportLocationKind::NoImport => unreachable!(),
        })
    }

    fn fetch_dhall(&self) -> Result<Parsed, Error> {
        Ok(match self {
            ImportLocationKind::Local(path) => Parsed::parse_file(path)?,
            ImportLocationKind::Remote(url) => {
                Parsed::parse_remote(url.clone())?
            }
            ImportLocationKind::Env(var_name) => {
                let val = match env::var(var_name) {
                    Ok(val) => val,
                    Err(_) => return Err(ImportError::MissingEnvVar.into()),
                };
                Parsed::parse_str(&val)?
            }
            ImportLocationKind::Missing => {
                return Err(ImportError::Missing.into())
            }
            ImportLocationKind::NoImport => unreachable!(),
        })
    }

    fn fetch_text(&self) -> Result<String, Error> {
        Ok(match self {
            ImportLocationKind::Local(path) => std::fs::read_to_string(path)?,
            ImportLocationKind::Remote(url) => download_http_text(url.clone())?,
            ImportLocationKind::Env(var_name) => match env::var(var_name) {
                Ok(val) => val,
                Err(_) => return Err(ImportError::MissingEnvVar.into()),
            },
            ImportLocationKind::Missing => {
                return Err(ImportError::Missing.into())
            }
            ImportLocationKind::NoImport => unreachable!(),
        })
    }

    fn to_location(&self) -> Expr {
        let (field_name, arg) = match self {
            ImportLocationKind::Local(path) => {
                ("Local", Some(path.to_string_lossy().into_owned()))
            }
            ImportLocationKind::Remote(url) => {
                ("Remote", Some(url.to_string()))
            }
            ImportLocationKind::Env(name) => {
                ("Environment", Some(name.clone()))
            }
            ImportLocationKind::Missing => ("Missing", None),
            ImportLocationKind::NoImport => unreachable!(),
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

impl ImportLocation {
    pub fn dhall_code_of_unknown_origin() -> Self {
        ImportLocation {
            kind: ImportLocationKind::Missing,
            mode: ImportMode::Code,
        }
    }
    pub fn dhall_code_without_imports() -> Self {
        ImportLocation {
            kind: ImportLocationKind::NoImport,
            mode: ImportMode::Code,
        }
    }
    pub fn local_dhall_code(path: PathBuf) -> Self {
        ImportLocation {
            kind: ImportLocationKind::Local(path),
            mode: ImportMode::Code,
        }
    }
    pub fn remote_dhall_code(url: Url) -> Self {
        ImportLocation {
            kind: ImportLocationKind::Remote(url),
            mode: ImportMode::Code,
        }
    }

    /// Given an import pointing to `target` found in the current location, compute the next
    /// location, or error if not allowed.
    /// `sanity_check` indicates whether to check if that location is allowed to be referenced,
    /// for example to prevent a remote file from reading an environment variable.
    fn chain(&self, import: &Import) -> Result<ImportLocation, Error> {
        // Makes no sense to chain an import if the current file is not a dhall file.
        assert!(matches!(self.mode, ImportMode::Code));
        if matches!(self.kind, ImportLocationKind::NoImport) {
            Err(ImportError::UnexpectedImport(import.clone()))?;
        }

        let kind = match &import.location {
            ImportTarget::Local(prefix, path) => {
                self.kind.chain_local(*prefix, path)?
            }
            ImportTarget::Remote(remote) => {
                if matches!(self.kind, ImportLocationKind::Remote(..))
                    && !matches!(import.mode, ImportMode::Location)
                {
                    // TODO: allow if CORS check passes
                    return Err(ImportError::SanityCheck.into());
                }
                let mut url = Url::parse(&format!(
                    "{}://{}",
                    remote.scheme, remote.authority
                ))?;
                url.set_path(&remote.path.file_path.iter().join("/"));
                url.set_query(remote.query.as_ref().map(String::as_ref));
                ImportLocationKind::Remote(url)
            }
            ImportTarget::Env(var_name) => {
                if matches!(self.kind, ImportLocationKind::Remote(..))
                    && !matches!(import.mode, ImportMode::Location)
                {
                    return Err(ImportError::SanityCheck.into());
                }
                ImportLocationKind::Env(var_name.clone())
            }
            ImportTarget::Missing => ImportLocationKind::Missing,
        };
        Ok(ImportLocation {
            kind,
            mode: import.mode,
        })
    }

    /// Fetches the expression corresponding to this location.
    fn fetch<'cx>(
        &self,
        env: &mut ImportEnv<'cx>,
        span: Span,
    ) -> Result<Typed<'cx>, Error> {
        let cx = env.cx();
        let typed = match self.mode {
            ImportMode::Code => {
                let parsed = self.kind.fetch_dhall()?;
                let typed = resolve_with_env(env, parsed)?.typecheck(cx)?;
                Typed {
                    // TODO: manage to keep the Nir around. Will need fixing variables.
                    hir: typed.normalize(cx).to_hir(),
                    ty: typed.ty,
                }
            }
            ImportMode::RawText => {
                let text = self.kind.fetch_text()?;
                Typed {
                    hir: Hir::new(
                        HirKind::Expr(ExprKind::TextLit(text.into())),
                        span,
                    ),
                    ty: Type::from_builtin(cx, Builtin::Text),
                }
            }
            ImportMode::Location => {
                let expr = self.kind.to_location();
                Parsed::from_expr_without_imports(expr)
                    .resolve(cx)
                    .unwrap()
                    .typecheck(cx)
                    .unwrap()
            }
        };
        Ok(typed)
    }
}

fn mkexpr(kind: UnspannedExpr) -> Expr {
    Expr::new(kind, Span::Artificial)
}

// TODO: error handling
#[cfg(all(not(target_arch = "wasm32"), feature = "reqwest"))]
pub(crate) fn download_http_text(url: Url) -> Result<String, Error> {
    Ok(reqwest::blocking::get(url).unwrap().text().unwrap())
}
#[cfg(all(not(target_arch = "wasm32"), not(feature = "reqwest")))]
pub(crate) fn download_http_text(_url: Url) -> Result<String, Error> {
    panic!("Remote imports are disabled in this build of dhall-rust")
}
#[cfg(target_arch = "wasm32")]
pub(crate) fn download_http_text(_url: Url) -> Result<String, Error> {
    panic!("Remote imports are not supported on wasm yet")
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

pub fn check_hash<'cx>(
    cx: Ctxt<'cx>,
    import: ImportId<'cx>,
    result: ImportResultId<'cx>,
) -> Result<(), Error> {
    let import = &cx[import];
    if let (ImportMode::Code, Some(Hash::SHA256(hash))) =
        (import.import.mode, &import.import.hash)
    {
        let expr = cx[result].hir.to_expr_alpha(cx);
        let actual_hash = expr.sha256_hash()?;
        if hash[..] != actual_hash[..] {
            mkerr(
                ErrorBuilder::new("hash mismatch")
                    .span_err(import.span.clone(), "hash mismatch")
                    .note(format!("Expected sha256:{}", hex::encode(hash)))
                    .note(format!(
                        "Found    sha256:{}",
                        hex::encode(actual_hash)
                    ))
                    .format(),
            )?
        }
    }
    Ok(())
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
fn traverse_resolve_expr<'cx>(
    name_env: &mut NameEnv,
    expr: &Expr,
    f: &mut impl FnMut(Import, Span) -> Result<ImportId<'cx>, Error>,
) -> Result<Hir<'cx>, Error> {
    let expr = desugar(expr);
    Ok(match expr.kind() {
        ExprKind::Var(var) => match name_env.unlabel_var(&var) {
            Some(v) => Hir::new(HirKind::Var(v), expr.span()),
            None => Hir::new(HirKind::MissingVar(var.clone()), expr.span()),
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
                    let import_id = f(import, expr.span())?;
                    HirKind::Import(import_id)
                }
                kind => HirKind::Expr(kind),
            };
            Hir::new(kind, expr.span())
        }
    })
}

/// Fetch the import and store the result in the global context.
fn fetch_import<'cx>(
    env: &mut ImportEnv<'cx>,
    import_id: ImportId<'cx>,
) -> Result<ImportResultId<'cx>, Error> {
    let cx = env.cx();
    let import = &cx[import_id].import;
    let span = cx[import_id].span.clone();
    let location = cx[import_id].base_location.chain(import)?;

    // If the import is in the in-memory cache, or the hash is in the on-disk cache, return
    // the cached contents.
    if let Some(res_id) = env.get_from_mem_cache(&location) {
        // The same location may be used with different or no hashes. Thus we need to check
        // the hashes every time.
        env.check_hash(import_id, res_id)?;
        env.write_to_disk_cache(&import.hash, res_id);
        return Ok(res_id);
    }
    if let Some(typed) = env.get_from_disk_cache(&import.hash) {
        // No need to check the hash, it was checked before reading the file.
        // We also don't write to the in-memory cache, because the location might be completely
        // unrelated to the cached file (e.g. `missing sha256:...` is valid).
        // This actually means that importing many times a same hashed import will take
        // longer than importing many times a same non-hashed import.
        let res_id = cx.push_import_result(typed);
        return Ok(res_id);
    }

    // Resolve this import, making sure that recursive imports don't cycle back to the
    // current one.
    let res = env.with_cycle_detection(location.clone(), |env| {
        location.fetch(env, span.clone())
    });
    let typed = match res {
        Ok(typed) => typed,
        Err(e) => mkerr(
            ErrorBuilder::new("error")
                .span_err(span.clone(), e.to_string())
                .format(),
        )?,
    };

    // Add the resolved import to the caches
    let res_id = cx.push_import_result(typed);
    env.check_hash(import_id, res_id)?;
    env.write_to_disk_cache(&import.hash, res_id);
    // Cache the mapping from this location to the result.
    env.write_to_mem_cache(location, res_id);

    Ok(res_id)
}

fn resolve_with_env<'cx>(
    env: &mut ImportEnv<'cx>,
    parsed: Parsed,
) -> Result<Resolved<'cx>, Error> {
    let Parsed(expr, base_location) = parsed;
    let resolved = traverse_resolve_expr(
        &mut NameEnv::new(),
        &expr,
        &mut |import, span| {
            let import_id =
                env.cx().push_import(base_location.clone(), import, span);
            let res_id = fetch_import(env, import_id)?;
            env.cx()[import_id].set_resultid(res_id);
            Ok(import_id)
        },
    )?;
    Ok(Resolved(resolved))
}

/// Resolves all imports and names. Returns errors if importing failed. Name errors are deferred to
/// typechecking.
pub fn resolve<'cx>(
    cx: Ctxt<'cx>,
    parsed: Parsed,
) -> Result<Resolved<'cx>, Error> {
    resolve_with_env(&mut ImportEnv::new(cx), parsed)
}

/// Resolves names and errors if we find any imports.
pub fn skip_resolve<'cx>(
    cx: Ctxt<'cx>,
    parsed: Parsed,
) -> Result<Resolved<'cx>, Error> {
    let parsed = Parsed::from_expr_without_imports(parsed.0);
    Ok(resolve(cx, parsed)?)
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
