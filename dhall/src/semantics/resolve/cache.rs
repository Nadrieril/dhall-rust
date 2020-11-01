use std::env;
use std::io::Write;
use std::path::{Path, PathBuf};

use crate::error::{CacheError, Error};
use crate::parse::parse_binary;
use crate::syntax::{binary, Hash};
use crate::Typed;
use std::ffi::OsStr;
use std::fs::File;

#[cfg(any(unix, windows))]
const CACHE_ENV_VAR: &str = "XDG_CACHE_HOME";
#[cfg(unix)]
const ALTERNATE_CACHE_ENV_VAR: &str = "HOME";
#[cfg(windows)]
const ALTERNATE_CACHE_ENV_VAR: &str = "LOCALAPPDATA";

#[cfg(any(unix, windows))]
fn default_cache_dir() -> Result<PathBuf, CacheError> {
    let cache_base_path = match env::var(OsStr::new(CACHE_ENV_VAR)) {
        Ok(path) => PathBuf::from(path),
        Err(_) => match env::var(OsStr::new(ALTERNATE_CACHE_ENV_VAR)) {
            Ok(path) => PathBuf::from(path).join(".cache"),
            Err(_) => return Err(CacheError::MissingConfiguration),
        },
    };
    Ok(cache_base_path.join("dhall"))
}

#[cfg(not(any(unix, windows)))]
fn default_cache_dir() -> Result<PathBuf, CacheError> {
    Err(CacheError::MissingConfiguration)
}

#[derive(Debug, Clone, PartialEq)]
pub struct Cache {
    cache_dir: PathBuf,
}

impl Cache {
    pub fn new() -> Result<Cache, Error> {
        let cache_dir = default_cache_dir()?;
        if !cache_dir.exists() {
            std::fs::create_dir_all(&cache_dir)
                .map_err(|e| CacheError::InitialisationError { cause: e })?;
        }
        Ok(Cache { cache_dir })
    }

    fn entry_path(&self, hash: &Hash) -> PathBuf {
        self.cache_dir.join(filename_for_hash(hash))
    }

    pub fn get(&self, hash: &Hash) -> Result<Typed, Error> {
        let path = self.entry_path(hash);
        let res = read_cache_file(&path, hash);
        if res.is_err() && path.exists() {
            // Delete cache file since it's invalid. We ignore the error.
            let _ = std::fs::remove_file(&path);
        }
        res
    }

    pub fn insert(&self, hash: &Hash, expr: &Typed) -> Result<(), Error> {
        let path = self.entry_path(hash);
        write_cache_file(&path, expr)
    }
}

/// Read a file from the cache, also checking that its hash is valid.
fn read_cache_file(path: &Path, hash: &Hash) -> Result<Typed, Error> {
    let data = crate::utils::read_binary_file(path)?;

    match hash {
        Hash::SHA256(hash) => {
            let actual_hash = crate::utils::sha256_hash(&data);
            if hash[..] != actual_hash[..] {
                return Err(CacheError::CacheHashInvalid.into());
            }
        }
    }

    Ok(parse_binary(&data)?.skip_resolve()?.typecheck()?)
}

/// Write a file to the cache.
fn write_cache_file(path: &Path, expr: &Typed) -> Result<(), Error> {
    let data = binary::encode(&expr.to_expr())?;
    File::create(path)?.write_all(data.as_slice())?;
    Ok(())
}

fn filename_for_hash(hash: &Hash) -> String {
    match hash {
        Hash::SHA256(sha) => format!("1220{}", hex::encode(&sha)),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::syntax::parse_expr;

    #[test]
    fn filename_for_hash_should_work() {
        let hash =
            Hash::SHA256(parse_expr("1").unwrap().sha256_hash().unwrap());
        assert_eq!("1220d60d8415e36e86dae7f42933d3b0c4fe3ca238f057fba206c7e9fbf5d784fe15".to_string(), filename_for_hash(&hash));
    }
}
