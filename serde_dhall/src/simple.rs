use super::Error;
use dhall::{STyKind, SimpleType, SimpleValue};

/// A Dhall value. This is a wrapper around [`dhall::SimpleValue`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Value(SimpleValue);

impl Value {
    pub fn into_simple_value(self) -> SimpleValue {
        self.0
    }
}

/// A Dhall type. This is a wrapper around [`dhall::SimpleType`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type(SimpleType);

impl Type {
    pub fn into_simple_type(self) -> SimpleType {
        self.0
    }
    pub fn to_dhall_value(&self) -> dhall::Value {
        self.0.to_value()
    }

    pub(crate) fn from_simple_type(ty: SimpleType) -> Self {
        Type(ty)
    }
    pub(crate) fn from_stykind(k: STyKind) -> Self {
        Type(SimpleType::new(k))
    }
    pub(crate) fn make_optional_type(t: Type) -> Self {
        Type::from_stykind(STyKind::Optional(t.0))
    }
    pub(crate) fn make_list_type(t: Type) -> Self {
        Type::from_stykind(STyKind::List(t.0))
    }
    // Made public for the StaticType derive macro
    #[doc(hidden)]
    pub fn make_record_type(kts: impl Iterator<Item = (String, Type)>) -> Self {
        Type::from_stykind(STyKind::Record(
            kts.map(|(k, t)| (k, t.0)).collect(),
        ))
    }
    #[doc(hidden)]
    pub fn make_union_type(
        kts: impl Iterator<Item = (String, Option<Type>)>,
    ) -> Self {
        Type::from_stykind(STyKind::Union(
            kts.map(|(k, t)| (k, t.map(|t| t.0))).collect(),
        ))
    }
}

impl super::sealed::Sealed for Value {}

impl super::Deserialize for Value {
    fn from_dhall(v: &dhall::Value) -> super::Result<Self> {
        let sval = v.to_simple_value().ok_or_else(|| {
            Error::Deserialize(format!(
                "this cannot be deserialized into a simple type: {}",
                v
            ))
        })?;
        Ok(Value(sval))
    }
}

impl super::sealed::Sealed for Type {}

impl super::Deserialize for Type {
    fn from_dhall(v: &dhall::Value) -> super::Result<Self> {
        let sty = v.to_simple_type().ok_or_else(|| {
            Error::Deserialize(format!(
                "this cannot be deserialized into a simple type: {}",
                v
            ))
        })?;
        Ok(Type(sty))
    }
}
