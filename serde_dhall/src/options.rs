use std::path::{Path, PathBuf};

use dhall::Parsed;

use crate::SimpleType;
use crate::{Deserialize, Error, Result, StaticType, Value};

#[derive(Debug, Clone)]
enum Source<'a> {
    Str(&'a str),
    File(PathBuf),
    // Url(&'a str),
}

/// Options and flags which can be used to configure how a dhall value is read.
///
/// This builder exposes the ability to configure how a value is deserialized and what operations
/// are permitted during evaluation. The functions in the crate root are aliases for
/// commonly used options using this builder.
///
/// Generally speaking, when using `Options`, you'll create it with `from_str` or `from_file`, then
/// chain calls to methods to set each option, then call `parse`. This will give you a
/// `serde_dhall::Result<T>` where `T` a deserializable type of your choice.
///
/// # Examples
///
/// Reading from a file:
///
/// ```no_run
/// # fn main() -> serde_dhall::Result<()> {
/// use serde_dhall::options;
///
/// let data = options::from_file("foo.dhall").parse()?;
/// # Ok(())
/// # }
/// ```
///
/// Reading from a file and checking the value against a provided type:
///
/// ```no_run
/// # fn main() -> serde_dhall::Result<()> {
/// use serde_dhall::options;
///
/// let ty = options::from_str("{ x: Natural, y: Natural }").parse()?;
/// let data = options::from_file("foo.dhall")
///             .type_annotation(&ty)
///             .parse()?;
/// # Ok(())
/// # }
/// ```
/// /// TODO
#[derive(Debug, Clone)]
pub struct Options<'a, T> {
    source: Source<'a>,
    annot: Option<SimpleType>,
    allow_imports: bool,
    // allow_remote_imports: bool,
    // use_cache: bool,
    target_type: std::marker::PhantomData<T>,
}

impl<'a, T> Options<'a, T> {
    fn default_with_source(source: Source<'a>) -> Self {
        Options {
            source,
            annot: None,
            allow_imports: true,
            // allow_remote_imports: true,
            // use_cache: true,
            target_type: std::marker::PhantomData,
        }
    }
    /// TODO
    fn from_str(s: &'a str) -> Self {
        Self::default_with_source(Source::Str(s))
    }
    /// TODO
    fn from_file<P: AsRef<Path>>(path: P) -> Self {
        Self::default_with_source(Source::File(path.as_ref().to_owned()))
    }
    // fn from_url(url: &'a str) -> Self {
    //     Self::default_with_source(Source::Url(url))
    // }

    /// TODO
    pub fn imports(&mut self, imports: bool) -> &mut Self {
        self.allow_imports = imports;
        self
    }
    // pub fn remote_imports(&mut self, imports: bool) -> &mut Self {
    //     self.allow_remote_imports = imports;
    //     if imports {
    //         self.allow_imports = true;
    //     }
    //     self
    // }
    //
    /// TODO
    pub fn type_annotation(&mut self, ty: &SimpleType) -> &mut Self {
        self.annot = Some(ty.clone());
        self
    }
    /// TODO
    pub fn static_type_annotation(&mut self) -> &mut Self
    where
        T: StaticType,
    {
        self.annot = Some(T::static_type());
        self
    }

    fn _parse(&self) -> dhall::error::Result<Value> {
        let parsed = match &self.source {
            Source::Str(s) => Parsed::parse_str(s)?,
            Source::File(p) => Parsed::parse_file(p.as_ref())?,
        };
        let resolved = if self.allow_imports {
            parsed.resolve()?
        } else {
            parsed.skip_resolve()?
        };
        let typed = match &self.annot {
            None => resolved.typecheck()?,
            Some(ty) => resolved.typecheck_with(ty.to_value().as_hir())?,
        };
        Ok(Value::from_nir(typed.normalize().as_nir()))
    }
    /// TODO
    pub fn parse(&self) -> Result<T>
    where
        T: Deserialize,
    {
        let val = self._parse().map_err(Error::Dhall)?;
        T::from_dhall(&val)
    }
}

/// TODO
pub fn from_str<'a, T>(s: &'a str) -> Options<'a, T> {
    Options::from_str(s)
}
/// TODO
pub fn from_file<'a, T, P: AsRef<Path>>(path: P) -> Options<'a, T> {
    Options::from_file(path)
}
// pub fn from_url<'a, T>(url: &'a str) -> Options<'a, T> {
//     Options::from_url(url)
// }
