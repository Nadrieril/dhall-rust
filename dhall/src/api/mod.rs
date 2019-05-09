mod serde;
pub(crate) mod static_type;

pub use value::Value;

mod value {
    use super::Type;
    use crate::error::Result;
    use crate::phase::{NormalizedSubExpr, Parsed, Typed};

    // A Dhall value
    pub struct Value(Typed);

    impl Value {
        pub fn from_str(s: &str, ty: Option<&Type>) -> Result<Self> {
            let resolved = Parsed::parse_str(s)?.resolve()?;
            let typed = match ty {
                None => resolved.typecheck()?,
                Some(t) => resolved.typecheck_with(&t.to_type())?,
            };
            Ok(Value(typed))
        }
        pub(crate) fn to_expr(&self) -> NormalizedSubExpr {
            self.0.to_expr()
        }
        pub(crate) fn to_typed(&self) -> Typed {
            self.0.clone()
        }
    }
}

pub use typ::Type;

mod typ {
    use dhall_syntax::Builtin;

    use crate::core::thunk::{Thunk, TypeThunk};
    use crate::core::value::Value;
    use crate::error::Result;
    use crate::phase::{NormalizedSubExpr, Typed};

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
        pub(crate) fn to_type(&self) -> crate::phase::Type {
            self.0.to_type()
        }
    }

    impl crate::de::Deserialize for Type {
        fn from_dhall(v: &crate::api::Value) -> Result<Self> {
            Ok(Type(v.to_typed()))
        }
    }
}

/// Deserialization of Dhall expressions into Rust
pub mod de {
    pub use super::static_type::StaticType;
    pub use super::{Type, Value};
    use crate::error::Result;
    #[doc(hidden)]
    pub use dhall_proc_macros::StaticType;

    /// A data structure that can be deserialized from a Dhall expression
    ///
    /// This is automatically implemented for any type that [serde][serde]
    /// can deserialize.
    ///
    /// This trait cannot be implemented manually.
    // TODO: seal trait
    pub trait Deserialize: Sized {
        /// See [dhall::de::from_str][crate::de::from_str]
        fn from_dhall(v: &Value) -> Result<Self>;
    }

    /// Deserialize an instance of type T from a string of Dhall text.
    ///
    /// This will recursively resolve all imports in the expression, and
    /// typecheck it before deserialization. Relative imports will be resolved relative to the
    /// provided file. More control over this process is not yet available
    /// but will be in a coming version of this crate.
    ///
    /// If a type is provided, this additionally checks that the provided
    /// expression has that type.
    pub fn from_str<T>(s: &str, ty: Option<&Type>) -> Result<T>
    where
        T: Deserialize,
    {
        T::from_dhall(&Value::from_str(s, ty)?)
    }

    /// Deserialize an instance of type T from a string of Dhall text,
    /// additionally checking that it matches the type of T.
    ///
    /// This will recursively resolve all imports in the expression, and
    /// typecheck it before deserialization. Relative imports will be resolved relative to the
    /// provided file. More control over this process is not yet available
    /// but will be in a coming version of this crate.
    pub fn from_str_auto_type<T>(s: &str) -> Result<T>
    where
        T: Deserialize + StaticType,
    {
        from_str(s, Some(&<T as StaticType>::static_type()))
    }
}
