use std::collections::BTreeMap;

use dhall::semantics::{Hir, HirKind, Nir, NirKind};
use dhall::syntax::{Builtin, ExprKind, NumKind, Span};

use crate::Error;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimpleValue {
    kind: Box<SValKind>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SValKind {
    Num(NumKind),
    Text(String),
    Optional(Option<SimpleValue>),
    List(Vec<SimpleValue>),
    Record(BTreeMap<String, SimpleValue>),
    Union(String, Option<SimpleValue>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimpleType {
    kind: Box<STyKind>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum STyKind {
    Bool,
    Natural,
    Integer,
    Double,
    Text,
    Optional(SimpleType),
    List(SimpleType),
    Record(BTreeMap<String, SimpleType>),
    Union(BTreeMap<String, Option<SimpleType>>),
}

/// A Dhall value. This is a wrapper around [`dhall::SimpleValue`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Value(SimpleValue);

/// A Dhall type. This is a wrapper around [`dhall::SimpleType`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type(SimpleType);

impl Value {
    pub fn into_simple_value(self) -> SimpleValue {
        self.0
    }
}

impl Type {
    pub fn into_simple_type(self) -> SimpleType {
        self.0
    }
    pub fn to_value(&self) -> crate::Value {
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

impl SimpleValue {
    pub fn new(kind: SValKind) -> Self {
        SimpleValue {
            kind: Box::new(kind),
        }
    }
    pub fn from_nir(nir: &Nir) -> Option<Self> {
        Some(SimpleValue::new(match nir.kind() {
            NirKind::Num(lit) => SValKind::Num(lit.clone()),
            NirKind::TextLit(x) => SValKind::Text(
                x.as_text()
                    .expect("Normal form should ensure the text is a string"),
            ),
            NirKind::EmptyOptionalLit(_) => SValKind::Optional(None),
            NirKind::NEOptionalLit(x) => {
                SValKind::Optional(Some(Self::from_nir(x)?))
            }
            NirKind::EmptyListLit(_) => SValKind::List(vec![]),
            NirKind::NEListLit(xs) => SValKind::List(
                xs.iter()
                    .map(|v| Self::from_nir(v))
                    .collect::<Option<_>>()?,
            ),
            NirKind::RecordLit(kvs) => SValKind::Record(
                kvs.iter()
                    .map(|(k, v)| Some((k.into(), Self::from_nir(v)?)))
                    .collect::<Option<_>>()?,
            ),
            NirKind::UnionLit(field, x, _) => {
                SValKind::Union(field.into(), Some(Self::from_nir(x)?))
            }
            NirKind::UnionConstructor(field, ty)
                if ty.get(field).map(|f| f.is_some()) == Some(false) =>
            {
                SValKind::Union(field.into(), None)
            }
            _ => return None,
        }))
    }

    pub fn kind(&self) -> &SValKind {
        self.kind.as_ref()
    }
}

impl SimpleType {
    pub fn new(kind: STyKind) -> Self {
        SimpleType {
            kind: Box::new(kind),
        }
    }
    pub fn from_nir(nir: &Nir) -> Option<Self> {
        Some(SimpleType::new(match nir.kind() {
            NirKind::BuiltinType(b) => match b {
                Builtin::Bool => STyKind::Bool,
                Builtin::Natural => STyKind::Natural,
                Builtin::Integer => STyKind::Integer,
                Builtin::Double => STyKind::Double,
                Builtin::Text => STyKind::Text,
                _ => unreachable!(),
            },
            NirKind::OptionalType(t) => STyKind::Optional(Self::from_nir(t)?),
            NirKind::ListType(t) => STyKind::List(Self::from_nir(t)?),
            NirKind::RecordType(kts) => STyKind::Record(
                kts.iter()
                    .map(|(k, v)| Some((k.into(), Self::from_nir(v)?)))
                    .collect::<Option<_>>()?,
            ),
            NirKind::UnionType(kts) => STyKind::Union(
                kts.iter()
                    .map(|(k, v)| {
                        Some((
                            k.into(),
                            v.as_ref()
                                .map(|v| Ok(Self::from_nir(v)?))
                                .transpose()?,
                        ))
                    })
                    .collect::<Option<_>>()?,
            ),
            _ => return None,
        }))
    }

    pub fn kind(&self) -> &STyKind {
        self.kind.as_ref()
    }
    pub fn to_value(&self) -> crate::Value {
        crate::Value {
            hir: self.to_hir(),
            as_simple_val: None,
            as_simple_ty: Some(self.clone()),
        }
    }
    pub fn to_hir(&self) -> Hir {
        let hir = |k| Hir::new(HirKind::Expr(k), Span::Artificial);
        hir(match self.kind() {
            STyKind::Bool => ExprKind::Builtin(Builtin::Bool),
            STyKind::Natural => ExprKind::Builtin(Builtin::Natural),
            STyKind::Integer => ExprKind::Builtin(Builtin::Integer),
            STyKind::Double => ExprKind::Builtin(Builtin::Double),
            STyKind::Text => ExprKind::Builtin(Builtin::Text),
            STyKind::Optional(t) => ExprKind::App(
                hir(ExprKind::Builtin(Builtin::Optional)),
                t.to_hir(),
            ),
            STyKind::List(t) => {
                ExprKind::App(hir(ExprKind::Builtin(Builtin::List)), t.to_hir())
            }
            STyKind::Record(kts) => ExprKind::RecordType(
                kts.into_iter()
                    .map(|(k, t)| (k.as_str().into(), t.to_hir()))
                    .collect(),
            ),
            STyKind::Union(kts) => ExprKind::UnionType(
                kts.into_iter()
                    .map(|(k, t)| {
                        (k.as_str().into(), t.as_ref().map(|t| t.to_hir()))
                    })
                    .collect(),
            ),
        })
    }
}

impl super::sealed::Sealed for Value {}

impl super::Deserialize for Value {
    fn from_dhall(v: &crate::Value) -> super::Result<Self> {
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
    fn from_dhall(v: &crate::Value) -> super::Result<Self> {
        let sty = v.to_simple_type().ok_or_else(|| {
            Error::Deserialize(format!(
                "this cannot be deserialized into a simple type: {}",
                v
            ))
        })?;
        Ok(Type(sty))
    }
}
