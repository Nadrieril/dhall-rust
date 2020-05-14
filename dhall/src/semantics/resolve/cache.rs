use std::env;
use std::io::Write;
use std::path::{Path, PathBuf};

use crate::error::{CacheError, Error, ErrorKind};
use crate::parse::parse_binary_file;
use crate::semantics::{Import, TypedHir};
use crate::syntax::Hash;
use crate::syntax::{binary, Expr};
use crate::Parsed;
use std::fs::File;

#[cfg(unix)]
const ALTERNATE_ENV_VAR: &str = "HOME";

#[cfg(windows)]
const ALTERNATE_ENV_VAR: &str = "LOCALAPPDATA";

fn alternate_env_var_cache_dir() -> Option<PathBuf> {
    env::var(ALTERNATE_ENV_VAR)
        .map(PathBuf::from)
        .map(|env_dir| env_dir.join(".cache").join("dhall"))
        .ok()
}

fn env_var_cache_dir() -> Option<PathBuf> {
    env::var("XDG_CACHE_HOME")
        .map(PathBuf::from)
        .map(|cache_home| cache_home.join("dhall"))
        .ok()
}

fn load_cache_dir() -> Result<PathBuf, CacheError> {
    env_var_cache_dir()
        .or_else(alternate_env_var_cache_dir)
        .ok_or(CacheError::MissingConfiguration)
}

pub struct Cache {
    cache_dir: Option<PathBuf>,
}

impl Cache {
    pub fn new() -> Cache {
        // Should warn that we can't initialize cache on error
        let cache_dir = load_cache_dir().and_then(|path| {
            std::fs::create_dir_all(path.as_path())
                .map(|_| path)
                .map_err(|e| CacheError::InitialisationError { cause: e })
        });
        Cache {
            cache_dir: cache_dir.ok(),
        }
    }
}

impl Cache {
    fn cache_file(&self, import: &Import) -> Option<PathBuf> {
        self.cache_dir
            .as_ref()
            .and_then(|cache_dir| {
                import.hash.as_ref().map(|hash| (cache_dir, hash))
            })
            .map(|(cache_dir, hash)| cache_dir.join(cache_filename(hash)))
    }

    fn search_cache_file(&self, import: &Import) -> Option<PathBuf> {
        self.cache_file(import)
            .filter(|cache_file| cache_file.exists())
    }

    fn search_cache(&self, import: &Import) -> Option<Result<Parsed, Error>> {
        self.search_cache_file(import)
            .map(|cache_file| parse_binary_file(cache_file.as_path()))
    }

    // Side effect since we don't use the result
    fn delete_cache(&self, import: &Import) {
        self.search_cache_file(import)
            .map(|cache_file| std::fs::remove_file(cache_file.as_path()));
    }

    // Side effect since we don't use the result
    fn save_expr(&self, import: &Import, expr: &Expr) {
        self.cache_file(import)
            .map(|cache_file| save_expr(cache_file.as_path(), expr));
    }

    pub fn caching_import<F, R>(
        &self,
        import: &Import,
        fetcher: F,
        mut resolver: R,
    ) -> Result<TypedHir, Error>
    where
        F: FnOnce() -> Result<Parsed, Error>,
        R: FnMut(Parsed) -> Result<TypedHir, Error>,
    {
        // Lookup the cache
        self.search_cache(import)
            // On cache found
            .and_then(|cache_result| {
                // Try to resolve the cache imported content
                match cache_result.and_then(|parsed| resolver(parsed)).and_then(
                    |typed_hir| {
                        check_hash(import.hash.as_ref().unwrap(), typed_hir)
                    },
                ) {
                    // Cache content is invalid (can't be parsed / can't be resolved / content sha invalid )
                    Err(_) => {
                        // Delete cache file since it's invalid
                        self.delete_cache(import);
                        // Result as there were no cache
                        None
                    }
                    // Cache valid
                    r => Some(r),
                }
            })
            .unwrap_or_else(|| {
                // Fetch and resolve as provided
                let imported = fetcher().and_then(resolver);
                // Save in cache the result if ok
                let _ = imported.as_ref().map(|(hir, _)| {
                    self.save_expr(import, &hir.to_expr_noopts())
                });
                imported
            })
    }
}

fn save_expr(file_path: &Path, expr: &Expr) -> Result<(), Error> {
    File::create(file_path)?.write_all(binary::encode(expr)?.as_slice())?;
    Ok(())
}

fn check_hash(hash: &Hash, typed_hir: TypedHir) -> Result<TypedHir, Error> {
    if hash.as_ref()[..] != typed_hir.0.to_expr_alpha().hash()?[..] {
        Err(Error::new(ErrorKind::Cache(CacheError::CacheHashInvalid)))
    } else {
        Ok(typed_hir)
    }
}

fn cache_filename<A: AsRef<[u8]>>(v: A) -> String {
    format!("1220{}", hex::encode(v.as_ref()))
}

impl AsRef<[u8]> for Hash {
    fn as_ref(&self) -> &[u8] {
        match self {
            Hash::SHA256(sha) => sha.as_slice(),
        }
    }
}
