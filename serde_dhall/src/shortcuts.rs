use crate::{options, Deserialize, Result, SimpleType, StaticType};

/// Deserialize an instance of type `T` from a string of Dhall text.
///
/// This will recursively resolve all imports in the expression, and typecheck it before
/// deserialization. Relative imports will be resolved relative to the current directory.
/// See [`options`] for more control over this process.
///
/// For additional type safety, prefer [`from_str_static_type`] or [`from_str_manual_type`].
///
/// [`options`]: options/index.html
/// [`from_str_manual_type`]: fn.from_str_manual_type.html
/// [`from_str_static_type`]: fn.from_str_static_type.html
///
/// # Example
///
/// ```rust
/// # fn main() -> serde_dhall::Result<()> {
/// use serde::Deserialize;
///
/// // We use serde's derive feature
/// #[derive(Debug, Deserialize)]
/// struct Point {
///     x: u64,
///     y: u64,
/// }
///
/// // Some Dhall data
/// let data = "{ x = 1, y = 1 + 1 } : { x: Natural, y: Natural }";
///
/// // Parse the Dhall string as a Point.
/// let point: Point = serde_dhall::from_str(data)?;
///
/// assert_eq!(point.x, 1);
/// assert_eq!(point.y, 2);
///
/// # Ok(())
/// # }
/// ```
pub fn from_str<T>(s: &str) -> Result<T>
where
    T: Deserialize,
{
    options::from_str(s).parse()
}

/// Deserialize an instance of type `T` from a string of Dhall text,
/// additionally checking that it matches the supplied type.
///
/// This will recursively resolve all imports in the expression, and typecheck it against the
/// supplied type before deserialization. Relative imports will be resolved relative to the current
/// directory. See [`options`] for more control over this process.
///
/// See also [`from_str_static_type`].
///
/// [`options`]: options/index.html
/// [`from_str_static_type`]: fn.from_str_static_type.html
///
/// # Example
///
/// ```rust
/// # fn main() -> serde_dhall::Result<()> {
/// use serde_dhall::SimpleType;
/// use std::collections::HashMap;
///
/// // Parse a Dhall type
/// let point_type_str = "{ x: Natural, y: Natural }";
/// let point_type: SimpleType = serde_dhall::from_str(point_type_str)?;
///
/// // Some Dhall data
/// let point_data = "{ x = 1, y = 1 + 1 }";
///
/// // Deserialize the data to a Rust type. This checks that
/// // the data matches the provided type.
/// let deserialized_map: HashMap<String, usize> =
///         serde_dhall::from_str_manual_type(point_data, &point_type)?;
///
/// let mut expected_map = HashMap::new();
/// expected_map.insert("x".to_string(), 1);
/// expected_map.insert("y".to_string(), 2);
///
/// assert_eq!(deserialized_map, expected_map);
/// # Ok(())
/// # }
/// ```
pub fn from_str_manual_type<T>(s: &str, ty: &SimpleType) -> Result<T>
where
    T: Deserialize,
{
    options::from_str(s).type_annotation(ty).parse()
}

/// Deserialize an instance of type `T` from a string of Dhall text,
/// additionally checking that it matches the type of `T`.
///
/// `T` must implement the [`StaticType`] trait.
///
/// This will recursively resolve all imports in the expression, and typecheck it against the
/// type of `T`. Relative imports will be resolved relative to the current
/// directory. See [`options`] for more control over this process.
///
/// [`options`]: options/index.html
/// [`StaticType`]: trait.StaticType.html
///
/// TODO
pub fn from_str_static_type<T>(s: &str) -> Result<T>
where
    T: Deserialize + StaticType,
{
    options::from_str(s).static_type_annotation().parse()
}
