use crate::error::Result;
use crate::options;
use crate::simple::Type as SimpleType;
use crate::static_type::StaticType;
use crate::Deserialize;

/// Deserialize an instance of type `T` from a string of Dhall text.
///
/// This will recursively resolve all imports in the expression, and typecheck it before
/// deserialization. Relative imports will be resolved relative to the current directory.
/// See [`options`][`options`] for more control over this process.
///
/// For additional type safety, prefer [`from_str_static_type`][`from_str_static_type`] or
/// [`from_str_manual_type`][`from_str_manual_type`].
///
///
/// # Example
///
/// ```rust
/// # fn main() -> serde_dhall::Result<()> {
/// use serde::Deserialize;
///
/// #[derive(Debug, Deserialize)]
/// struct Point {
///     x: u64,
///     y: u64,
/// }
///
/// // Some Dhall data
/// let data = "{ x = 1, y = 1 + 1 } : { x: Natural, y: Natural }";
///
/// // Convert the Dhall string to a Point.
/// let point: Point = serde_dhall::from_str(data)?;
/// assert_eq!(point.x, 1);
/// assert_eq!(point.y, 2);
///
/// # Ok(())
/// # }
/// ```
///
/// [`options`]: options/index.html
/// [`from_str_manual_type`]: fn.from_str_manual_type.html
/// [`from_str_static_type`]: fn.from_str_static_type.html
pub fn from_str<T>(s: &str) -> Result<T>
where
    T: Deserialize,
{
    options::from_str(s).parse()
}

/// Deserialize an instance of type `T` from a string of Dhall text,
/// additionally checking that it matches the supplied type.
///
/// Like [`from_str`], but this additionally checks that
/// the type of the provided expression matches the supplied type.
///
/// ```rust
/// # fn main() -> serde_dhall::Result<()> {
/// use serde_dhall::simple::Type;
/// use std::collections::HashMap;
///
/// // Parse a Dhall type
/// let point_type_str = "{ x: Natural, y: Natural }";
/// let point_type: Type = serde_dhall::from_str(point_type_str)?;
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
///
/// TODO
pub fn from_str_manual_type<T>(s: &str, ty: &SimpleType) -> Result<T>
where
    T: Deserialize,
{
    options::from_str(s).type_annotation(ty).parse()
}

/// Deserialize an instance of type `T` from a string of Dhall text,
/// additionally checking that it matches the type of `T`.
///
/// Like [from_str], but this additionally checks that
/// the type of the provided expression matches the output type `T`. The [StaticType] trait
/// captures Rust types that are valid Dhall types.
///
/// TODO
pub fn from_str_static_type<T>(s: &str) -> Result<T>
where
    T: Deserialize + StaticType,
{
    options::from_str(s).static_type_annotation().parse()
}
