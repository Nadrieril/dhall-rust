use std::env;
use std::io::Write;
use std::path::{Path, PathBuf};

use crate::error::{CacheError, Error, ErrorKind};
use crate::parse::parse_binary_file;
use crate::semantics::{Import, TypedHir};
use crate::syntax::Hash;
use crate::syntax::{binary, Expr};
use crate::Parsed;
use std::env::VarError;
use std::ffi::OsStr;
use std::fs::File;

#[cfg(unix)]
const ALTERNATE_ENV_VAR: &str = "HOME";

#[cfg(windows)]
const ALTERNATE_ENV_VAR: &str = "LOCALAPPDATA";

fn alternate_env_var_cache_dir(
    provider: impl Fn(&str) -> Result<String, VarError>,
) -> Option<PathBuf> {
    provider(ALTERNATE_ENV_VAR)
        .map(PathBuf::from)
        .map(|env_dir| env_dir.join(".cache").join("dhall"))
        .ok()
}

fn env_var_cache_dir(
    provider: impl Fn(&str) -> Result<String, VarError>,
) -> Option<PathBuf> {
    provider("XDG_CACHE_HOME")
        .map(PathBuf::from)
        .map(|cache_home| cache_home.join("dhall"))
        .ok()
}

fn load_cache_dir(
    provider: impl Fn(&str) -> Result<String, VarError> + Copy,
) -> Result<PathBuf, CacheError> {
    env_var_cache_dir(provider)
        .or_else(|| alternate_env_var_cache_dir(provider))
        .ok_or(CacheError::MissingConfiguration)
}

#[derive(Debug, PartialEq)]
pub struct Cache {
    cache_dir: Option<PathBuf>,
}

impl Cache {
    fn new_with_provider(
        provider: impl Fn(&str) -> Result<String, VarError> + Copy,
    ) -> Cache {
        // Should warn that we can't initialize cache on error
        let cache_dir = load_cache_dir(provider).and_then(|path| {
            if !path.exists() {
                std::fs::create_dir_all(path.as_path())
                    .map(|_| path)
                    .map_err(|e| CacheError::InitialisationError { cause: e })
            } else {
                Ok(path)
            }
        });
        Cache {
            cache_dir: cache_dir.ok(),
        }
    }

    pub fn new() -> Cache {
        Cache::new_with_provider(|name| env::var(OsStr::new(name)))
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

#[cfg(test)]
mod test {
    use super::*;
    use crate::semantics::parse::parse_str;
    use crate::syntax::{
        parse_expr, ExprKind, ImportMode, ImportTarget, NumKind, Span,
    };
    use rand::distributions::Alphanumeric;
    use rand::Rng;
    use std::env::temp_dir;

    #[cfg(unix)]
    #[test]
    fn alternate_env_var_cache_dir_should_result_unix_folder_path() {
        let actual =
            alternate_env_var_cache_dir(|_| Ok("/home/user".to_string()));
        assert_eq!(actual, Some(PathBuf::from("/home/user/.cache/dhall")));
    }

    #[test]
    fn alternate_env_var_cache_dir_should_result_none_on_missing_var() {
        let actual = alternate_env_var_cache_dir(|_| Err(VarError::NotPresent));
        assert_eq!(actual, None);
    }

    #[test]
    fn env_var_cache_dir_should_result_xdg_cache_home() {
        let actual = env_var_cache_dir(|_| {
            Ok("/home/user/custom/path/for/cache".to_string())
        });
        assert_eq!(
            actual,
            Some(PathBuf::from("/home/user/custom/path/for/cache/dhall"))
        );
    }

    #[test]
    fn env_var_cache_dir_should_result_none_on_missing_var() {
        let actual = env_var_cache_dir(|_| Err(VarError::NotPresent));
        assert_eq!(actual, None);
    }

    #[test]
    fn load_cache_dir_should_result_xdg_cache_first() {
        let actual = load_cache_dir(|var| match var {
            "XDG_CACHE_HOME" => Ok("/home/user/custom".to_string()),
            _ => Err(VarError::NotPresent),
        });
        assert_eq!(actual.unwrap(), PathBuf::from("/home/user/custom/dhall"));
    }

    #[cfg(unix)]
    #[test]
    fn load_cache_dir_should_result_alternate() {
        let actual = load_cache_dir(|var| match var {
            ALTERNATE_ENV_VAR => Ok("/home/user".to_string()),
            _ => Err(VarError::NotPresent),
        });
        assert_eq!(actual.unwrap(), PathBuf::from("/home/user/.cache/dhall"));
    }

    #[test]
    fn load_cache_dir_should_result_none() {
        let actual = load_cache_dir(|_| Err(VarError::NotPresent));
        assert!(matches!(
            actual.unwrap_err(),
            CacheError::MissingConfiguration
        ));
    }

    #[test]
    fn new_with_provider_should_create_cache_folder() {
        let test_id = rand::thread_rng()
            .sample_iter(Alphanumeric)
            .take(36)
            .collect::<String>();
        let dir = temp_dir().join(test_id);

        std::fs::create_dir_all(dir.as_path()).unwrap();

        let actual = Cache::new_with_provider(|_| {
            Ok(dir.clone().to_str().map(String::from).unwrap())
        });
        assert_eq!(
            actual,
            Cache {
                cache_dir: Some(dir.join("dhall"))
            }
        );
        assert!(dir.join("dhall").exists());
        std::fs::remove_dir_all(dir.as_path()).unwrap();
    }

    #[test]
    fn new_with_provider_should_return_cache_for_existing_folder() {
        let test_id = rand::thread_rng()
            .sample_iter(Alphanumeric)
            .take(36)
            .collect::<String>();
        let dir = temp_dir().join(test_id);

        std::fs::create_dir_all(dir.as_path()).unwrap();
        File::create(dir.join("dhall")).unwrap();

        assert!(dir.join("dhall").exists());

        let actual = Cache::new_with_provider(|_| {
            Ok(dir.clone().to_str().map(String::from).unwrap())
        });
        assert_eq!(
            actual,
            Cache {
                cache_dir: Some(dir.join("dhall"))
            }
        );
        std::fs::remove_dir_all(dir.as_path()).unwrap();
    }

    #[test]
    fn caching_import_should_load_cache() -> Result<(), Error> {
        let test_id = rand::thread_rng()
            .sample_iter(Alphanumeric)
            .take(36)
            .collect::<String>();
        let dir = temp_dir().join(test_id);

        std::fs::create_dir_all(dir.as_path())?;

        let cache = Cache::new_with_provider(|_| {
            Ok(dir.clone().to_str().map(String::from).unwrap())
        });

        // Create cache file
        let expr =
            Expr::new(ExprKind::Num(NumKind::Natural(1)), Span::Artificial);
        File::create(dir.join("dhall").join("1220d60d8415e36e86dae7f42933d3b0c4fe3ca238f057fba206c7e9fbf5d784fe15"))?
            .write_all(binary::encode(&expr)?.as_ref())?;

        let import = Import {
            mode: ImportMode::Code,
            location: ImportTarget::Missing,
            hash: Some(Hash::SHA256(hex::decode("d60d8415e36e86dae7f42933d3b0c4fe3ca238f057fba206c7e9fbf5d784fe15").unwrap())),
        };

        let mut resolve_counter = 0;

        let result = cache.caching_import(
            &import,
            || panic!("Should not fetch import"),
            |parsed| {
                resolve_counter += 1;
                let result = parsed.resolve()?.typecheck()?;
                Ok((result.normalize().to_hir(), result.ty))
            },
        );

        assert!(result.is_ok());
        assert_eq!(resolve_counter, 1);

        std::fs::remove_dir_all(dir.as_path()).unwrap();
        Ok(())
    }

    #[test]
    fn caching_import_should_skip_cache_if_missing_cache_folder(
    ) -> Result<(), Error> {
        let cache = Cache::new_with_provider(|_| Err(VarError::NotPresent));

        let import = Import {
            mode: ImportMode::Code,
            location: ImportTarget::Missing,
            hash: Some(Hash::SHA256(hex::decode("d60d8415e36e86dae7f42933d3b0c4fe3ca238f057fba206c7e9fbf5d784fe15").unwrap())),
        };

        let mut resolve_counter = 0;
        let mut fetcher_counter = 0;

        let result = cache.caching_import(
            &import,
            || {
                fetcher_counter += 1;
                parse_str("1")
            },
            |parsed| {
                resolve_counter += 1;
                let result = parsed.resolve()?.typecheck()?;
                Ok((result.normalize().to_hir(), result.ty))
            },
        );

        assert!(result.is_ok(), "caching_import Should be valid");
        assert_eq!(resolve_counter, 1);
        assert_eq!(fetcher_counter, 1);
        Ok(())
    }

    #[test]
    fn caching_import_should_skip_cache_on_no_hash_import() -> Result<(), Error>
    {
        let cache = Cache::new_with_provider(|_| Err(VarError::NotPresent));

        let import = Import {
            mode: ImportMode::Code,
            location: ImportTarget::Missing,
            hash: None,
        };

        let mut resolve_counter = 0;
        let mut fetcher_counter = 0;

        let result = cache.caching_import(
            &import,
            || {
                fetcher_counter += 1;
                parse_str("1")
            },
            |parsed| {
                resolve_counter += 1;
                let result = parsed.resolve()?.typecheck()?;
                Ok((result.normalize().to_hir(), result.ty))
            },
        );

        assert!(result.is_ok(), "caching_import Should be valid");
        assert_eq!(resolve_counter, 1);
        assert_eq!(fetcher_counter, 1);
        Ok(())
    }

    #[test]
    fn caching_import_should_fetch_import_if_no_cache() -> Result<(), Error> {
        let test_id = rand::thread_rng()
            .sample_iter(Alphanumeric)
            .take(36)
            .collect::<String>();
        let dir = temp_dir().join(test_id);

        std::fs::create_dir_all(dir.as_path())?;

        let cache = Cache::new_with_provider(|_| {
            Ok(dir.clone().to_str().map(String::from).unwrap())
        });

        let import = Import {
            mode: ImportMode::Code,
            location: ImportTarget::Missing,
            hash: Some(Hash::SHA256(hex::decode("d60d8415e36e86dae7f42933d3b0c4fe3ca238f057fba206c7e9fbf5d784fe15").unwrap())),
        };

        let mut fetcher_counter = 0;
        let mut resolve_counter = 0;

        let result = cache.caching_import(
            &import,
            || {
                fetcher_counter += 1;
                parse_str("1")
            },
            |parsed| {
                resolve_counter += 1;
                let result = parsed.resolve()?.typecheck()?;
                Ok((result.normalize().to_hir(), result.ty))
            },
        );

        assert!(result.is_ok(), "caching_import Should be valid");
        assert_eq!(resolve_counter, 1);
        assert_eq!(fetcher_counter, 1);

        std::fs::remove_dir_all(dir.as_path()).unwrap();
        Ok(())
    }

    #[test]
    fn caching_import_should_fetch_import_on_cache_parsed_error(
    ) -> Result<(), Error> {
        let test_id = rand::thread_rng()
            .sample_iter(Alphanumeric)
            .take(36)
            .collect::<String>();
        let dir = temp_dir().join(test_id);

        std::fs::create_dir_all(dir.as_path())?;

        let cache = Cache::new_with_provider(|_| {
            Ok(dir.clone().to_str().map(String::from).unwrap())
        });

        File::create(dir.join("dhall").join("1220d60d8415e36e86dae7f42933d3b0c4fe3ca238f057fba206c7e9fbf5d784fe15"))?
            .write_all("Invalid content".as_bytes())?;

        let import = Import {
            mode: ImportMode::Code,
            location: ImportTarget::Missing,
            hash: Some(Hash::SHA256(hex::decode("d60d8415e36e86dae7f42933d3b0c4fe3ca238f057fba206c7e9fbf5d784fe15").unwrap())),
        };

        let mut fetcher_counter = 0;
        let mut resolve_counter = 0;

        let result = cache.caching_import(
            &import,
            || {
                fetcher_counter += 1;
                parse_str("1")
            },
            |parsed| {
                resolve_counter += 1;
                let result = parsed.resolve()?.typecheck()?;
                Ok((result.normalize().to_hir(), result.ty))
            },
        );

        assert!(result.is_ok(), "caching_import Should be valid");
        assert_eq!(fetcher_counter, 1, "Should fetch since cache is invalid");
        assert_eq!(
            resolve_counter, 1,
            "Should resolve only 1 time because cache can't be parsed"
        );

        std::fs::remove_dir_all(dir.as_path()).unwrap();
        Ok(())
    }

    #[test]
    fn caching_import_should_fetch_import_on_cache_resolve_error(
    ) -> Result<(), Error> {
        let test_id = rand::thread_rng()
            .sample_iter(Alphanumeric)
            .take(36)
            .collect::<String>();
        let dir = temp_dir().join(test_id);

        std::fs::create_dir_all(dir.as_path())?;

        let cache = Cache::new_with_provider(|_| {
            Ok(dir.clone().to_str().map(String::from).unwrap())
        });

        let expr =
            Expr::new(ExprKind::Num(NumKind::Natural(2)), Span::Artificial);
        File::create(dir.join("dhall").join("1220d60d8415e36e86dae7f42933d3b0c4fe3ca238f057fba206c7e9fbf5d784fe15"))?
            .write_all(binary::encode(&expr)?.as_slice())?;

        let import = Import {
            mode: ImportMode::Code,
            location: ImportTarget::Missing,
            hash: Some(Hash::SHA256(hex::decode("d60d8415e36e86dae7f42933d3b0c4fe3ca238f057fba206c7e9fbf5d784fe15").unwrap())),
        };

        let mut fetcher_counter = 0;
        let mut resolve_counter = 0;

        let result = cache.caching_import(
            &import,
            || {
                fetcher_counter += 1;
                parse_str("1")
            },
            |parsed| {
                resolve_counter += 1;
                match resolve_counter {
                    1 => Err(Error::new(ErrorKind::Cache(
                        CacheError::CacheHashInvalid,
                    ))),
                    _ => {
                        let result = parsed.resolve()?.typecheck()?;
                        Ok((result.normalize().to_hir(), result.ty))
                    }
                }
            },
        );

        assert!(result.is_ok(), "caching_import Should be valid");
        assert_eq!(fetcher_counter, 1, "Should fetch since cache is invalid");
        assert_eq!(
            resolve_counter, 2,
            "Should resolve 2 time (one for cache that fail, one for fetch)"
        );

        std::fs::remove_dir_all(dir.as_path()).unwrap();
        Ok(())
    }

    #[test]
    fn caching_import_should_fetch_import_on_invalid_hash_cache_content(
    ) -> Result<(), Error> {
        let test_id = rand::thread_rng()
            .sample_iter(Alphanumeric)
            .take(36)
            .collect::<String>();
        let dir = temp_dir().join(test_id);

        std::fs::create_dir_all(dir.as_path())?;

        let cache = Cache::new_with_provider(|_| {
            Ok(dir.clone().to_str().map(String::from).unwrap())
        });

        let expr =
            Expr::new(ExprKind::Num(NumKind::Natural(2)), Span::Artificial);
        File::create(dir.join("dhall").join("1220d60d8415e36e86dae7f42933d3b0c4fe3ca238f057fba206c7e9fbf5d784fe15"))?
            .write_all(binary::encode(&expr)?.as_slice())?;

        let import = Import {
            mode: ImportMode::Code,
            location: ImportTarget::Missing,
            hash: Some(Hash::SHA256(hex::decode("d60d8415e36e86dae7f42933d3b0c4fe3ca238f057fba206c7e9fbf5d784fe15").unwrap())),
        };

        let mut fetcher_counter = 0;
        let mut resolve_counter = 0;

        let result = cache.caching_import(
            &import,
            || {
                fetcher_counter += 1;
                parse_str("1")
            },
            |parsed| {
                resolve_counter += 1;
                let result = parsed.resolve()?.typecheck()?;
                Ok((result.normalize().to_hir(), result.ty))
            },
        );

        assert!(result.is_ok(), "caching_import Should be valid");
        assert_eq!(fetcher_counter, 1, "Should fetch since cache is invalid");
        assert_eq!(
            resolve_counter, 2,
            "Should resolve 2 time (one for cache, one for fetch)"
        );

        std::fs::remove_dir_all(dir.as_path()).unwrap();
        Ok(())
    }

    #[test]
    fn caching_import_should_save_import_if_missing() -> Result<(), Error> {
        let test_id = rand::thread_rng()
            .sample_iter(Alphanumeric)
            .take(36)
            .collect::<String>();
        let dir = temp_dir().join(test_id);

        std::fs::create_dir_all(dir.as_path())?;

        let cache = Cache::new_with_provider(|_| {
            Ok(dir.clone().to_str().map(String::from).unwrap())
        });
        let import = Import {
            mode: ImportMode::Code,
            location: ImportTarget::Missing,
            hash: Some(Hash::SHA256(hex::decode("d60d8415e36e86dae7f42933d3b0c4fe3ca238f057fba206c7e9fbf5d784fe15").unwrap())),
        };

        let mut fetcher_counter = 0;
        let mut resolve_counter = 0;

        let result = cache.caching_import(
            &import,
            || {
                fetcher_counter += 1;
                parse_str("1")
            },
            |parsed| {
                resolve_counter += 1;
                let result = parsed.resolve()?.typecheck()?;
                Ok((result.normalize().to_hir(), result.ty))
            },
        );

        assert!(result.is_ok(), "caching_import Should be valid");
        assert_eq!(fetcher_counter, 1, "Should fetch since cache is mising");
        assert_eq!(resolve_counter, 1, "Should resolve 1 time");

        let cache_file = dir.join("dhall").join("1220d60d8415e36e86dae7f42933d3b0c4fe3ca238f057fba206c7e9fbf5d784fe15");
        assert!(cache_file.exists());

        std::fs::remove_dir_all(dir.as_path()).unwrap();
        Ok(())
    }

    #[test]
    fn cache_filename_should_result_for_hash() {
        let hash =
            Hash::SHA256(parse_expr("1").unwrap().hash().unwrap().into_vec());
        assert_eq!("1220d60d8415e36e86dae7f42933d3b0c4fe3ca238f057fba206c7e9fbf5d784fe15".to_string(), cache_filename(hash));
    }

    #[test]
    fn check_hash_should_be_ok_for_same_hash() -> Result<(), Error> {
        let typed = parse_str("1")?.resolve()?.typecheck()?;
        let hash = Hash::SHA256(parse_expr("1")?.hash()?.into_vec());

        let expected = (typed.normalize().to_hir(), typed.ty);
        let actual = check_hash(&hash, expected.clone());
        assert_eq!(actual.unwrap(), expected);
        Ok(())
    }

    #[test]
    fn check_hash_should_be_ok_for_unmatching_hash() -> Result<(), Error> {
        let typed = parse_str("1")?.resolve()?.typecheck()?;
        let hash = Hash::SHA256(parse_expr("2")?.hash()?.into_vec());

        let expected = (typed.normalize().to_hir(), typed.ty);
        let actual = check_hash(&hash, expected);
        assert!(actual.is_err());
        Ok(())
    }
}
