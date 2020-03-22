use std::collections::BTreeMap;

use dhall::semantics::{Hir, HirKind, Nir, NirKind};
use dhall::syntax::{Builtin, ExprKind, NumKind, Span};

use crate::{Deserialize, Error, Result, Sealed};

/// A simple value of the kind that can be encoded/decoded with serde
/// TODO
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Value {
    kind: Box<ValKind>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValKind {
    // TODO: redefine NumKind locally
    Num(NumKind),
    Text(String),
    Optional(Option<Value>),
    List(Vec<Value>),
    // TODO: HashMap ?
    Record(BTreeMap<String, Value>),
    Union(String, Option<Value>),
}

/// The type of a `simple::Value`.
/// TODO
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type {
    kind: Box<TyKind>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TyKind {
    Bool,
    Natural,
    Integer,
    Double,
    Text,
    Optional(Type),
    List(Type),
    Record(BTreeMap<String, Type>),
    Union(BTreeMap<String, Option<Type>>),
}

impl Value {
    pub(crate) fn new(kind: ValKind) -> Self {
        Value {
            kind: Box::new(kind),
        }
    }
    pub(crate) fn from_nir(nir: &Nir) -> Option<Self> {
        Some(Value::new(match nir.kind() {
            NirKind::Num(lit) => ValKind::Num(lit.clone()),
            NirKind::TextLit(x) => ValKind::Text(
                x.as_text()
                    .expect("Normal form should ensure the text is a string"),
            ),
            NirKind::EmptyOptionalLit(_) => ValKind::Optional(None),
            NirKind::NEOptionalLit(x) => {
                ValKind::Optional(Some(Self::from_nir(x)?))
            }
            NirKind::EmptyListLit(_) => ValKind::List(vec![]),
            NirKind::NEListLit(xs) => ValKind::List(
                xs.iter()
                    .map(|v| Self::from_nir(v))
                    .collect::<Option<_>>()?,
            ),
            NirKind::RecordLit(kvs) => ValKind::Record(
                kvs.iter()
                    .map(|(k, v)| Some((k.into(), Self::from_nir(v)?)))
                    .collect::<Option<_>>()?,
            ),
            NirKind::UnionLit(field, x, _) => {
                ValKind::Union(field.into(), Some(Self::from_nir(x)?))
            }
            NirKind::UnionConstructor(field, ty)
                if ty.get(field).map(|f| f.is_some()) == Some(false) =>
            {
                ValKind::Union(field.into(), None)
            }
            _ => return None,
        }))
    }

    pub fn kind(&self) -> &ValKind {
        self.kind.as_ref()
    }
}

impl Type {
    pub fn new(kind: TyKind) -> Self {
        Type {
            kind: Box::new(kind),
        }
    }
    pub(crate) fn from_nir(nir: &Nir) -> Option<Self> {
        Some(Type::new(match nir.kind() {
            NirKind::BuiltinType(b) => match b {
                Builtin::Bool => TyKind::Bool,
                Builtin::Natural => TyKind::Natural,
                Builtin::Integer => TyKind::Integer,
                Builtin::Double => TyKind::Double,
                Builtin::Text => TyKind::Text,
                _ => unreachable!(),
            },
            NirKind::OptionalType(t) => TyKind::Optional(Self::from_nir(t)?),
            NirKind::ListType(t) => TyKind::List(Self::from_nir(t)?),
            NirKind::RecordType(kts) => TyKind::Record(
                kts.iter()
                    .map(|(k, v)| Some((k.into(), Self::from_nir(v)?)))
                    .collect::<Option<_>>()?,
            ),
            NirKind::UnionType(kts) => TyKind::Union(
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

    pub fn kind(&self) -> &TyKind {
        self.kind.as_ref()
    }
    pub fn to_value(&self) -> crate::value::Value {
        crate::value::Value {
            hir: self.to_hir(),
            as_simple_val: None,
            as_simple_ty: Some(self.clone()),
        }
    }
    pub(crate) fn to_hir(&self) -> Hir {
        let hir = |k| Hir::new(HirKind::Expr(k), Span::Artificial);
        hir(match self.kind() {
            TyKind::Bool => ExprKind::Builtin(Builtin::Bool),
            TyKind::Natural => ExprKind::Builtin(Builtin::Natural),
            TyKind::Integer => ExprKind::Builtin(Builtin::Integer),
            TyKind::Double => ExprKind::Builtin(Builtin::Double),
            TyKind::Text => ExprKind::Builtin(Builtin::Text),
            TyKind::Optional(t) => ExprKind::App(
                hir(ExprKind::Builtin(Builtin::Optional)),
                t.to_hir(),
            ),
            TyKind::List(t) => {
                ExprKind::App(hir(ExprKind::Builtin(Builtin::List)), t.to_hir())
            }
            TyKind::Record(kts) => ExprKind::RecordType(
                kts.into_iter()
                    .map(|(k, t)| (k.as_str().into(), t.to_hir()))
                    .collect(),
            ),
            TyKind::Union(kts) => ExprKind::UnionType(
                kts.into_iter()
                    .map(|(k, t)| {
                        (k.as_str().into(), t.as_ref().map(|t| t.to_hir()))
                    })
                    .collect(),
            ),
        })
    }
}

impl Sealed for Value {}

impl Deserialize for Value {
    fn from_dhall(v: &crate::value::Value) -> Result<Self> {
        v.to_simple_value().ok_or_else(|| {
            Error::Deserialize(format!(
                "this cannot be deserialized into a simple type: {}",
                v
            ))
        })
    }
}

impl Sealed for Type {}

impl Deserialize for Type {
    fn from_dhall(v: &crate::value::Value) -> Result<Self> {
        v.to_simple_type().ok_or_else(|| {
            Error::Deserialize(format!(
                "this cannot be deserialized into a simple type: {}",
                v
            ))
        })
    }
}

impl From<TyKind> for Type {
    fn from(x: TyKind) -> Type {
        Type::new(x)
    }
}
