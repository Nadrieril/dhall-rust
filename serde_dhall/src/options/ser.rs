use crate::options::{HasAnnot, ManualAnnot, NoAnnot, StaticAnnot, TypeAnnot};
use crate::{Result, SimpleType, ToDhall};

/// Controls how a Dhall value is written.
///
/// This builder exposes the ability to configure how a value is serialized, and to set type
/// annotations.
///
/// When using [`Serializer`], you'll create it with [`serialize()`], then chain calls to methods
/// to set each option, then call [`to_string()`]. This will give you a [`Result`] containing the
/// input serialized to Dhall.
///
/// Note that if you do not provide a type annotation, some values may not be convertible to Dhall,
/// like empty lists or enums.
///
/// [`to_string()`]: Serializer::to_string()
///
/// # Examples
///
/// Serializing without a type annotation:
///
/// ```rust
/// # fn main() -> serde_dhall::Result<()> {
/// use serde_dhall::serialize;
///
/// let string = serialize(&1i64).to_string()?;
/// assert_eq!(string, "+1".to_string());
/// # Ok(())
/// # }
/// ```
///
/// Serializing with an automatic type annotation:
///
/// ```rust
/// # fn main() -> serde_dhall::Result<()> {
/// use serde_dhall::serialize;
///
/// let data: Option<u64> = None;
/// let string = serialize(&data).static_type_annotation().to_string()?;
/// assert_eq!(string, "None Natural".to_string());
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone)]
pub struct Serializer<'a, T, A> {
    data: &'a T,
    annot: A,
}

impl<'a, T> Serializer<'a, T, NoAnnot> {
    /// Provides a type to the serialization process. The provided value will be checked against
    /// that type, and the type will be used when Dhall needs it, like for empty lists or for
    /// unions.
    ///
    /// In many cases the Dhall type that corresponds to a Rust type can be inferred automatically.
    /// See the [`StaticType`] trait and the [`static_type_annotation()`] method for that.
    ///
    /// # Example
    ///
    /// ```
    /// # fn main() -> serde_dhall::Result<()> {
    /// use serde_dhall::{serialize, from_str, SimpleType, SimpleValue};
    ///
    /// let ty = from_str("< A | B: Bool >").parse()?;
    /// let data = SimpleValue::Union("A".to_string(), None);
    /// let string = serialize(&data)
    ///     .type_annotation(&ty)
    ///     .to_string()?;
    /// assert_eq!(string, "< A | B: Bool >.A".to_string());
    ///
    /// // Invalid data fails the type validation; serialization would have succeeded otherwise.
    /// let ty = SimpleType::Integer;
    /// assert!(
    ///     serialize(&Some(0u64))
    ///         .type_annotation(&ty)
    ///         .to_string()
    ///         .is_err()
    /// );
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [`StaticType`]: crate::StaticType
    /// [`static_type_annotation()`]: Serializer::static_type_annotation()
    pub fn type_annotation<'ty>(
        self,
        ty: &'ty SimpleType,
    ) -> Serializer<'a, T, ManualAnnot<'ty>> {
        Serializer {
            annot: ManualAnnot(ty),
            data: self.data,
        }
    }

    /// Uses the type of `T` in the serialization process. This will be used when Dhall needs it,
    /// like for empty lists or for unions.
    ///
    /// `T` must implement the [`StaticType`] trait. If it doesn't, you can use [`type_annotation()`]
    ///
    /// # Example
    ///
    /// ```
    /// # fn main() -> serde_dhall::Result<()> {
    /// use serde::Serialize;
    /// use serde_dhall::{serialize, StaticType};
    ///
    /// #[derive(Serialize, StaticType)]
    /// enum MyOption {
    ///     MyNone,
    ///     MySome(u64),
    /// }
    ///
    /// let data = MyOption::MySome(0);
    /// let string = serialize(&data)
    ///     .static_type_annotation()
    ///     .to_string()?;
    /// // The resulting Dhall string depends on the type annotation; it could not have been
    /// // printed without it.
    /// assert_eq!(string, "< MyNone | MySome: Natural >.MySome 0".to_string());
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [`StaticType`]: crate::StaticType
    /// [`type_annotation()`]: Serializer::type_annotation()
    pub fn static_type_annotation(self) -> Serializer<'a, T, StaticAnnot> {
        Serializer {
            annot: StaticAnnot,
            data: self.data,
        }
    }
}

impl<'a, T, A> Serializer<'a, T, A>
where
    A: TypeAnnot,
{
    /// Prints the chosen value with the options provided.
    ///
    /// If you enabled static annotations, `T` is required to implement [`StaticType`].
    ///
    /// Note that if you do not provide a type annotation, some values may not be convertible to
    /// Dhall, like empty lists or enums.
    ///
    ///
    /// # Example
    ///
    /// ```rust
    /// # fn main() -> serde_dhall::Result<()> {
    /// use serde_dhall::serialize;
    ///
    /// let string = serialize(&1i64).static_type_annotation().to_string()?;
    /// assert_eq!(string, "+1".to_string());
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [`StaticType`]: crate::StaticType
    pub fn to_string(&self) -> Result<String>
    where
        T: ToDhall + HasAnnot<A>,
    {
        let val = self.data.to_dhall(T::get_annot(self.annot).as_ref())?;
        Ok(val.to_string())
    }
}

/// Serialize a value to a string of Dhall text.
///
/// This returns a [`Serializer`] object. Call the [`to_string()`] method to get the serialized
/// value, or use other [`Serializer`] methods to control the serialization process.
///
/// In order to process certain values (like unions or empty lists) correctly, it is necessary to
/// add a type annotation (with [`static_type_annotation()`] or [`type_annotation()`]).
///
/// # Examples
///
/// ```rust
/// # fn main() -> serde_dhall::Result<()> {
/// use serde::Serialize;
/// use serde_dhall::{serialize, StaticType};
///
/// #[derive(Serialize)]
/// struct Point {
///     x: u64,
///     y: u64,
/// }
///
///
/// let data = Point { x: 0, y: 0 };
/// let string = serialize(&data).to_string()?;
/// assert_eq!(string, "{ x = 0, y = 0 }");
/// # Ok(())
/// # }
/// ```
///
/// ```rust
/// # fn main() -> serde_dhall::Result<()> {
/// use serde::Serialize;
/// use serde_dhall::{serialize, StaticType};
///
/// #[derive(Serialize, StaticType)]
/// enum MyOption {
///     MyNone,
///     MySome(u64),
/// }
///
/// let data = MyOption::MySome(0);
/// let string = serialize(&data)
///     .static_type_annotation()
///     .to_string()?;
/// // The resulting Dhall string depends on the type annotation; it could not have been
/// // printed without it.
/// assert_eq!(string, "< MyNone | MySome: Natural >.MySome 0".to_string());
/// # Ok(())
/// # }
/// ```
///
/// [`type_annotation()`]: Serializer::type_annotation()
/// [`static_type_annotation()`]: Serializer::static_type_annotation()
/// [`to_string()`]: Serializer::to_string()
pub fn serialize<T>(data: &T) -> Serializer<'_, T, NoAnnot>
where
    T: ToDhall,
{
    Serializer {
        data,
        annot: NoAnnot,
    }
}
