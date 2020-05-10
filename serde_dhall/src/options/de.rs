use std::path::{Path, PathBuf};

use dhall::Parsed;

use crate::SimpleType;
use crate::{Error, ErrorKind, FromDhall, Result, StaticType, Value};

#[derive(Debug, Clone)]
enum Source<'a> {
    Str(&'a str),
    File(PathBuf),
    // Url(&'a str),
}

#[derive(Debug, Clone, Copy)]
pub struct NoAnnot;
#[derive(Debug, Clone, Copy)]
pub struct ManualAnnot<'ty>(&'ty SimpleType);
#[derive(Debug, Clone, Copy)]
pub struct StaticAnnot;

pub trait OptionalAnnot<A> {
    fn get_annot(a: &A) -> Option<SimpleType>;
}
impl<T> OptionalAnnot<NoAnnot> for T {
    fn get_annot(_: &NoAnnot) -> Option<SimpleType> {
        None
    }
}
impl<'ty, T> OptionalAnnot<ManualAnnot<'ty>> for T {
    fn get_annot(a: &ManualAnnot<'ty>) -> Option<SimpleType> {
        Some(a.0.clone())
    }
}
impl<T: StaticType> OptionalAnnot<StaticAnnot> for T {
    fn get_annot(_: &StaticAnnot) -> Option<SimpleType> {
        Some(T::static_type())
    }
}

/// Controls how a Dhall value is read.
///
/// This builder exposes the ability to configure how a value is deserialized and what operations
/// are permitted during evaluation.
///
/// Generally speaking, when using [`Deserializer`], you'll create it with [`from_str`] or [`from_file`], then
/// chain calls to methods to set each option, then call [`parse`]. This will give you a
/// [`Result<T>`] where `T` is a deserializable type of your choice.
///
/// [`Deserializer`]: struct.Deserializer.html
/// [`from_str`]: fn.from_str.html
/// [`from_file`]: fn.from_file.html
/// [`parse`]: struct.Deserializer.html#method.parse
/// [`Result<T>`]: type.Result.html
///
/// # Examples
///
/// Reading from a file:
///
/// ```no_run
/// # fn main() -> serde_dhall::Result<()> {
/// use serde_dhall::from_file;
///
/// let data = from_file("foo.dhall").parse::<u64>()?;
/// # Ok(())
/// # }
/// ```
///
/// Reading from a file and checking the value against a provided type:
///
/// ```no_run
/// # fn main() -> serde_dhall::Result<()> {
/// use std::collections::HashMap;
/// use serde_dhall::{from_file, from_str};
///
/// let ty = from_str("{ x: Natural, y: Natural }").parse()?;
/// let data = from_file("foo.dhall")
///             .type_annotation(&ty)
///             .parse::<HashMap<String, u64>>()?;
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone)]
pub struct Deserializer<'a, A> {
    source: Source<'a>,
    annot: A,
    allow_imports: bool,
    // allow_remote_imports: bool,
    // use_cache: bool,
}

impl<'a> Deserializer<'a, NoAnnot> {
    fn default_with_source(source: Source<'a>) -> Self {
        Deserializer {
            source,
            annot: NoAnnot,
            allow_imports: true,
            // allow_remote_imports: true,
            // use_cache: true,
        }
    }
    fn from_str(s: &'a str) -> Self {
        Self::default_with_source(Source::Str(s))
    }
    fn from_file<P: AsRef<Path>>(path: P) -> Self {
        Self::default_with_source(Source::File(path.as_ref().to_owned()))
    }
    // fn from_url(url: &'a str) -> Self {
    //     Self::default_with_source(Source::Url(url))
    // }

    /// Ensures that the parsed value matches the provided type.
    ///
    /// In many cases the Dhall type that corresponds to a Rust type can be inferred automatically.
    /// See the [`StaticType`] trait and the [`static_type_annotation`] method for that.
    ///
    /// # Example
    ///
    /// ```
    /// # fn main() -> serde_dhall::Result<()> {
    /// use std::collections::HashMap;
    /// use serde::Deserialize;
    /// use serde_dhall::{from_str, SimpleType};
    ///
    /// // Parse a Dhall type
    /// let type_str = "{ x: Natural, y: Natural }";
    /// let ty = from_str(type_str).parse::<SimpleType>()?;
    ///
    /// // Parse some Dhall data.
    /// let data = "{ x = 1, y = 1 + 1 }";
    /// let point = from_str(data)
    ///     .type_annotation(&ty)
    ///     .parse::<HashMap<String, u64>>()?;
    /// assert_eq!(point.get("y"), Some(&2));
    ///
    /// // Invalid data fails the type validation; deserialization would have succeeded otherwise.
    /// let invalid_data = "{ x = 1, z = 3 }";
    /// assert!(
    ///     from_str(invalid_data)
    ///         .type_annotation(&ty)
    ///         .parse::<HashMap<String, u64>>()
    ///         .is_err()
    /// );
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [`static_type_annotation`]: struct.Deserializer.html#method.static_type_annotation
    /// [`StaticType`]: trait.StaticType.html
    pub fn type_annotation<'ty>(
        self,
        ty: &'ty SimpleType,
    ) -> Deserializer<'a, ManualAnnot<'ty>> {
        Deserializer {
            annot: ManualAnnot(ty),
            source: self.source,
            allow_imports: self.allow_imports,
        }
    }

    /// Ensures that the parsed value matches the type of `T`.
    ///
    /// `T` must implement the [`StaticType`] trait. If it doesn't, you can use [`type_annotation`]
    /// to provide a type manually.
    ///
    /// # Example
    ///
    /// ```
    /// # fn main() -> serde_dhall::Result<()> {
    /// use serde::Deserialize;
    /// use serde_dhall::StaticType;
    ///
    /// #[derive(Deserialize, StaticType)]
    /// struct Point {
    ///     x: u64,
    ///     y: Option<u64>,
    /// }
    ///
    /// // Some Dhall data
    /// let data = "{ x = 1, y = Some (1 + 1) }";
    ///
    /// // Convert the Dhall string to a Point.
    /// let point = serde_dhall::from_str(data)
    ///     .static_type_annotation()
    ///     .parse::<Point>()?;
    /// assert_eq!(point.x, 1);
    /// assert_eq!(point.y, Some(2));
    ///
    /// // Invalid data fails the type validation; deserialization would have succeeded otherwise.
    /// let invalid_data = "{ x = 1 }";
    /// assert!(
    ///     serde_dhall::from_str(invalid_data)
    ///         .static_type_annotation()
    ///         .parse::<Point>()
    ///         .is_err()
    /// );
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [`type_annotation`]: struct.Deserializer.html#method.type_annotation
    /// [`StaticType`]: trait.StaticType.html
    pub fn static_type_annotation(self) -> Deserializer<'a, StaticAnnot> {
        Deserializer {
            annot: StaticAnnot,
            source: self.source,
            allow_imports: self.allow_imports,
        }
    }
}

impl<'a, A> Deserializer<'a, A> {
    /// Sets whether to enable imports.
    ///
    /// By default, imports are enabled.
    ///
    /// # Example
    ///
    /// ```
    /// # fn main() -> serde_dhall::Result<()> {
    /// use serde::Deserialize;
    /// use serde_dhall::SimpleType;
    ///
    /// let data = "12 + ./other_file.dhall : Natural";
    /// assert!(
    ///     serde_dhall::from_str(data)
    ///         .imports(false)
    ///         .parse::<u64>()
    ///         .is_err()
    /// );
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [`static_type_annotation`]: struct.Deserializer.html#method.static_type_annotation
    /// [`StaticType`]: trait.StaticType.html
    pub fn imports(self, imports: bool) -> Self {
        Deserializer {
            allow_imports: imports,
            ..self
        }
    }

    // /// TODO
    // pub fn remote_imports(&mut self, imports: bool) -> &mut Self {
    //     self.allow_remote_imports = imports;
    //     if imports {
    //         self.allow_imports = true;
    //     }
    //     self
    // }

    fn _parse<T>(&self) -> dhall::error::Result<Value>
    where
        T: OptionalAnnot<A>,
    {
        let parsed = match &self.source {
            Source::Str(s) => Parsed::parse_str(s)?,
            Source::File(p) => Parsed::parse_file(p.as_ref())?,
        };
        let resolved = if self.allow_imports {
            parsed.resolve()?
        } else {
            parsed.skip_resolve()?
        };
        let typed = match &T::get_annot(&self.annot) {
            None => resolved.typecheck()?,
            Some(ty) => resolved.typecheck_with(ty.to_value().as_hir())?,
        };
        Ok(Value::from_nir(typed.normalize().as_nir()))
    }

    /// Parses the chosen dhall value with the options provided.
    ///
    /// If you enabled static annotations, `T` is required to implement [`StaticType`].
    ///
    ///
    /// # Example
    ///
    /// ```
    /// # fn main() -> serde_dhall::Result<()> {
    /// let data = serde_dhall::from_str("6 * 7").parse::<u64>()?;
    /// assert_eq!(data, 42);
    /// # Ok(())
    /// # }
    /// ```
    /// [`StaticType`]: trait.StaticType.html
    pub fn parse<T>(&self) -> Result<T>
    where
        T: FromDhall + OptionalAnnot<A>,
    {
        let val = self
            ._parse::<T>()
            .map_err(ErrorKind::Dhall)
            .map_err(Error)?;
        T::from_dhall(&val)
    }
}

/// Deserialize a value from a string of Dhall text.
///
/// This returns a [`Deserializer`] object. Call the [`parse`] method to get the deserialized
/// value, or use other [`Deserializer`] methods to control the deserialization process.
///
/// Imports will be resolved relative to the current directory.
///
/// # Example
///
/// ```rust
/// # fn main() -> serde_dhall::Result<()> {
/// use serde::Deserialize;
///
/// // We use serde's derive feature
/// #[derive(Deserialize)]
/// struct Point {
///     x: u64,
///     y: u64,
/// }
///
/// // Some Dhall data
/// let data = "{ x = 1, y = 1 + 1 } : { x: Natural, y: Natural }";
///
/// // Parse the Dhall string as a Point.
/// let point: Point = serde_dhall::from_str(data).parse()?;
///
/// assert_eq!(point.x, 1);
/// assert_eq!(point.y, 2);
/// # Ok(())
/// # }
/// ```
///
/// [`Deserializer`]: struct.Deserializer.html
/// [`parse`]: struct.Deserializer.html#method.parse
pub fn from_str(s: &str) -> Deserializer<'_, NoAnnot> {
    Deserializer::from_str(s)
}

/// Deserialize a value from a Dhall file.
///
/// This returns a [`Deserializer`] object. Call the [`parse`] method to get the deserialized
/// value, or use other [`Deserializer`] methods to control the deserialization process.
///
/// Imports will be resolved relative to the provided file's path.
///
/// # Example
///
/// ```no_run
/// # fn main() -> serde_dhall::Result<()> {
/// use serde::Deserialize;
///
/// // We use serde's derive feature
/// #[derive(Deserialize)]
/// struct Point {
///     x: u64,
///     y: u64,
/// }
///
/// // Parse the Dhall file as a Point.
/// let point: Point = serde_dhall::from_file("foo.dhall").parse()?;
/// # Ok(())
/// # }
/// ```
///
/// [`Deserializer`]: struct.Deserializer.html
/// [`parse`]: struct.Deserializer.html#method.parse
pub fn from_file<'a, P: AsRef<Path>>(path: P) -> Deserializer<'a, NoAnnot> {
    Deserializer::from_file(path)
}

// pub fn from_url(url: &str) -> Deserializer<'_, NoAnnot> {
//     Deserializer::from_url(url)
// }
