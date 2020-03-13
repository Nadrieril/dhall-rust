use std::collections::BTreeMap;

use crate::semantics::{Hir, HirKind, Nir, NirKind};
use crate::syntax::{Builtin, ExprKind, NumKind, Span};
use crate::Value;

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

impl SimpleValue {
    pub(crate) fn new(kind: SValKind) -> Self {
        SimpleValue {
            kind: Box::new(kind),
        }
    }
    pub(crate) fn from_nir(nir: &Nir) -> Option<Self> {
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
    pub(crate) fn from_nir(nir: &Nir) -> Option<Self> {
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
    pub fn to_value(&self) -> Value {
        Value {
            hir: self.to_hir(),
            as_simple_val: None,
            as_simple_ty: Some(self.clone()),
        }
    }
    pub(crate) fn to_hir(&self) -> Hir {
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
