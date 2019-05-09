mod serde;
pub(crate) mod static_type;
pub(crate) mod traits;

// pub struct Value(crate::phase::Normalized);

pub use typ::Type;

mod typ {
    use crate::core::thunk::{Thunk, TypeThunk};
    use crate::core::value::Value;
    use crate::phase::{NormalizedSubExpr, Typed};
    use dhall_syntax::Builtin;

    /// A Dhall expression representing a type.
    ///
    /// This captures what is usually simply called a "type", like
    /// `Bool`, `{ x: Integer }` or `Natural -> Text`.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Type(Typed);

    impl Type {
        pub(crate) fn from_value(v: Value) -> Self {
            Type(Typed::from_value_untyped(v))
        }
        pub(crate) fn make_builtin_type(b: Builtin) -> Self {
            Self::from_value(Value::from_builtin(b))
        }
        pub(crate) fn make_optional_type(t: Type) -> Self {
            Self::from_value(Value::AppliedBuiltin(
                Builtin::Optional,
                vec![t.to_thunk()],
            ))
        }
        pub(crate) fn make_list_type(t: Type) -> Self {
            Self::from_value(Value::AppliedBuiltin(
                Builtin::List,
                vec![t.to_thunk()],
            ))
        }
        #[doc(hidden)]
        pub fn from_normalized_expr(e: NormalizedSubExpr) -> Self {
            Type(Typed::from_normalized_expr_untyped(e))
        }
        #[doc(hidden)]
        pub fn make_record_type(
            kts: impl Iterator<Item = (String, Type)>,
        ) -> Self {
            Self::from_value(Value::RecordType(
                kts.map(|(k, t)| {
                    (k.into(), TypeThunk::from_thunk(t.to_thunk()))
                })
                .collect(),
            ))
        }
        #[doc(hidden)]
        pub fn make_union_type(
            kts: impl Iterator<Item = (String, Option<Type>)>,
        ) -> Self {
            Self::from_value(Value::UnionType(
                kts.map(|(k, t)| {
                    (k.into(), t.map(|t| TypeThunk::from_thunk(t.to_thunk())))
                })
                .collect(),
            ))
        }

        pub(crate) fn to_thunk(&self) -> Thunk {
            self.0.to_thunk()
        }
        #[allow(dead_code)]
        pub(crate) fn to_expr(&self) -> NormalizedSubExpr {
            self.0.to_expr()
        }
    }
}

/// Deserialization of Dhall expressions into Rust
pub mod de {
    pub use super::static_type::StaticType;
    pub use super::Type;
    #[doc(hidden)]
    pub use crate::traits::Deserialize;
    #[doc(hidden)]
    pub use dhall_proc_macros::StaticType;

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
        // from_str(s, Some(&<T as StaticType>::static_type()))
        // TODO
        from_str(s, None)
    }
}
