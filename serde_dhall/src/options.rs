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

/// Controls how a dhall value is read.
///
/// This builder exposes the ability to configure how a value is deserialized and what operations
/// are permitted during evaluation.
///
/// Generally speaking, when using `Deserializer`, you'll create it with `from_str` or `from_file`, then
/// chain calls to methods to set each option, then call `parse`. This will give you a
/// `serde_dhall::Result<T>` where `T` is a deserializable type of your choice.
///
/// # Examples
///
/// Reading from a file:
///
/// ```no_run
/// # fn main() -> serde_dhall::Result<()> {
/// use serde_dhall::from_file;
///
/// let data = from_file("foo.dhall").parse()?;
/// # Ok(())
/// # }
/// ```
///
/// Reading from a file and checking the value against a provided type:
///
/// ```no_run
/// # fn main() -> serde_dhall::Result<()> {
/// use serde_dhall::{from_file, from_str};
///
/// let ty = from_str("{ x: Natural, y: Natural }").parse()?;
/// let data = from_file("foo.dhall")
///             .type_annotation(&ty)
///             .parse()?;
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
pub struct Deserializer<'a, T> {
    source: Source<'a>,
    annot: Option<SimpleType>,
    allow_imports: bool,
    // allow_remote_imports: bool,
    // use_cache: bool,
    target_type: std::marker::PhantomData<T>,
}

impl<'a, T> Deserializer<'a, T> {
    fn default_with_source(source: Source<'a>) -> Self {
        Deserializer {
            source,
            annot: None,
            allow_imports: true,
            // allow_remote_imports: true,
            // use_cache: true,
            target_type: std::marker::PhantomData,
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

    /// Sets whether to enable imports.
    ///
    /// By default, imports are enabled.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> serde_dhall::Result<()> {
    /// use serde::Deserialize;
    /// use serde_dhall::SimpleType;
    ///
    /// let data = "12 + ./other_file.dhall : Natural";
    /// assert!(
    ///     serde_dhall::from_str::<u64>(data)
    ///         .imports(false)
    ///         .parse()
    ///         .is_err()
    /// );
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [`static_type_annotation`]: struct.Deserializer.html#method.static_type_annotation
    /// [`StaticType`]: trait.StaticType.html
    pub fn imports(&mut self, imports: bool) -> &mut Self {
        self.allow_imports = imports;
        self
    }

    // /// TODO
    // pub fn remote_imports(&mut self, imports: bool) -> &mut Self {
    //     self.allow_remote_imports = imports;
    //     if imports {
    //         self.allow_imports = true;
    //     }
    //     self
    // }

    /// Ensures that the parsed value matches the provided type.
    ///
    /// In many cases the Dhall type that corresponds to a Rust type can be inferred automatically.
    /// See the [`StaticType`] trait and the [`static_type_annotation`] method.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> serde_dhall::Result<()> {
    /// use serde::Deserialize;
    /// use serde_dhall::SimpleType;
    ///
    /// #[derive(Deserialize)]
    /// struct Point {
    ///     x: u64,
    ///     y: Option<u64>,
    /// }
    ///
    /// // Parse a Dhall type
    /// let point_type_str = "{ x: Natural, y: Optional Natural }";
    /// let point_type: SimpleType = serde_dhall::from_str(point_type_str).parse()?;
    ///
    /// // Parse some Dhall data to a Point.
    /// let data = "{ x = 1, y = Some (1 + 1) }";
    /// let point: Point = serde_dhall::from_str(data)
    ///     .type_annotation(&point_type)
    ///     .parse()?;
    /// assert_eq!(point.x, 1);
    /// assert_eq!(point.y, Some(2));
    ///
    /// // Invalid data fails the type validation; deserialization would have succeeded otherwise.
    /// let invalid_data = "{ x = 1 }";
    /// assert!(
    ///     serde_dhall::from_str::<Point>(invalid_data)
    ///         .type_annotation(&point_type)
    ///         .parse()
    ///         .is_err()
    /// );
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [`static_type_annotation`]: struct.Deserializer.html#method.static_type_annotation
    /// [`StaticType`]: trait.StaticType.html
    pub fn type_annotation(&mut self, ty: &SimpleType) -> &mut Self {
        self.annot = Some(ty.clone());
        self
    }

    /// Ensures that the parsed value matches the type of `T`.
    ///
    /// `T` must implement the [`StaticType`] trait. If it doesn't, you can use [`type_annotation`]
    /// to provide a type manually.
    ///
    /// # Examples
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
    /// let point: Point = serde_dhall::from_str(data)
    ///     .static_type_annotation()
    ///     .parse()?;
    /// assert_eq!(point.x, 1);
    /// assert_eq!(point.y, Some(2));
    ///
    /// // Invalid data fails the type validation; deserialization would have succeeded otherwise.
    /// let invalid_data = "{ x = 1 }";
    /// assert!(
    ///     serde_dhall::from_str::<Point>(invalid_data)
    ///         .static_type_annotation()
    ///         .parse()
    ///         .is_err()
    /// );
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [`type_annotation`]: struct.Deserializer.html#method.type_annotation
    /// [`StaticType`]: trait.StaticType.html
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

    /// Parses the chosen dhall value with the options provided.
    ///
    /// # Examples
    ///
    /// Reading from a file:
    ///
    /// ```no_run
    /// # fn main() -> serde_dhall::Result<()> {
    /// let data = serde_dhall::from_file("foo.dhall").parse()?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn parse(&self) -> Result<T>
    where
        T: FromDhall,
    {
        let val = self._parse().map_err(ErrorKind::Dhall).map_err(Error)?;
        T::from_dhall(&val)
    }
}

/// Deserialize an instance of type `T` from a string of Dhall text.
///
/// This returns a [`Deserializer`] object. Call the [`parse`] method to get the deserialized value, or
/// use other [`Deserializer`] methods to e.g. add type annotations beforehand.
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
pub fn from_str<T>(s: &str) -> Deserializer<'_, T> {
    Deserializer::from_str(s)
}

/// Deserialize an instance of type `T` from a Dhall file.
///
/// This returns a [`Deserializer`] object. Call the [`parse`] method to get the deserialized value, or
/// use other [`Deserializer`] methods to e.g. add type annotations beforehand.
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
pub fn from_file<'a, T, P: AsRef<Path>>(path: P) -> Deserializer<'a, T> {
    Deserializer::from_file(path)
}

// pub fn from_url<'a, T>(url: &'a str) -> Deserializer<'a, T> {
//     Deserializer::from_url(url)
// }

// Custom impl to not get a Clone bound on T
impl<'a, T> Clone for Deserializer<'a, T> {
    fn clone(&self) -> Self {
        Deserializer {
            source: self.source.clone(),
            annot: self.annot.clone(),
            allow_imports: self.allow_imports.clone(),
            target_type: std::marker::PhantomData,
        }
    }
}
