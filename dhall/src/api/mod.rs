mod serde;
pub(crate) mod traits;

/// Deserialization of Dhall expressions into Rust
pub mod de {
    #[doc(hidden)]
    pub use crate::phase::SimpleType;
    pub use crate::traits::{Deserialize, SimpleStaticType, StaticType};
    #[doc(hidden)]
    pub use dhall_proc_macros::SimpleStaticType;

    /// Deserialize an instance of type T from a string of Dhall text.
    ///
    /// This will recursively resolve all imports in the expression, and
    /// typecheck it before deserialization. Relative imports will be resolved relative to the
    /// provided file. More control over this process is not yet available
    /// but will be in a coming version of this crate.
    ///
    /// If a type is provided, this additionally checks that the provided
    /// expression has that type.
    pub fn from_str<'a, T: Deserialize<'a>>(
        s: &'a str,
        ty: Option<&crate::phase::Type>,
    ) -> crate::error::Result<T> {
        T::from_str(s, ty)
    }

    /// Deserialize an instance of type T from a string of Dhall text,
    /// additionally checking that it matches the type of T.
    ///
    /// This will recursively resolve all imports in the expression, and
    /// typecheck it before deserialization. Relative imports will be resolved relative to the
    /// provided file. More control over this process is not yet available
    /// but will be in a coming version of this crate.
    pub fn from_str_auto_type<'a, T: Deserialize<'a> + StaticType>(
        s: &'a str,
    ) -> crate::error::Result<T> {
        from_str(s, Some(&<T as StaticType>::get_static_type()))
    }
}
