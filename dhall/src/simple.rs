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

pub trait SimpleValueFolder: Sized {
    fn num(x: NumKind) -> Self;
    fn text(x: String) -> Self;
    fn optional(x: Option<Self>) -> Self;
    fn list(x: impl Iterator<Item = Self>) -> Self;
    fn record(values: impl Iterator<Item = (String, Self)>) -> Self;
    fn union(variant: String, content: Option<Self>) -> Self;
}

pub trait SimpleTypeFolder: Sized {
    fn bool() -> Self;
    fn natural() -> Self;
    fn integer() -> Self;
    fn double() -> Self;
    fn text() -> Self;
    fn optional(x: Self) -> Self;
    fn list(x: Self) -> Self;
    fn record(types: impl Iterator<Item = (String, Self)>) -> Self;
    fn union(types: impl Iterator<Item = (String, Option<Self>)>) -> Self;
}

pub(crate) fn fold_simple_value<T>(nir: &Nir) -> Option<T>
where
    T: SimpleValueFolder,
{
    // TODO: check the type first and remove error handling
    Some(match nir.kind() {
        NirKind::Num(lit) => T::num(lit.clone()),
        NirKind::TextLit(x) => T::text(
            x.as_text()
                .expect("Normal form should ensure the text is a string"),
        ),
        NirKind::EmptyOptionalLit(_) => T::optional(None),
        NirKind::NEOptionalLit(x) => T::optional(Some(fold_simple_value(x)?)),
        NirKind::EmptyListLit(_) => T::list(std::iter::empty()),
        NirKind::NEListLit(xs) => T::list(
            xs.iter()
                .map(|v| fold_simple_value(v))
                .collect::<Option<Vec<_>>>()?
                .into_iter(),
        ),
        NirKind::RecordLit(kvs) => T::record(
            kvs.iter()
                .map(|(k, v)| Some((k.into(), fold_simple_value(v)?)))
                .collect::<Option<BTreeMap<_, _>>>()?
                .into_iter(),
        ),
        NirKind::UnionLit(field, x, _) => {
            T::union(field.into(), Some(fold_simple_value(x)?))
        }
        NirKind::UnionConstructor(field, ty)
            if ty.get(field).map(|f| f.is_some()) == Some(false) =>
        {
            T::union(field.into(), None)
        }
        _ => return None,
    })
}

pub(crate) fn fold_simple_type<T>(nir: &Nir) -> Option<T>
where
    T: SimpleTypeFolder,
{
    // TODO: avoid unnecessary allocations
    Some(match nir.kind() {
        NirKind::BuiltinType(b) => match b {
            Builtin::Bool => T::bool(),
            Builtin::Natural => T::natural(),
            Builtin::Integer => T::integer(),
            Builtin::Double => T::double(),
            Builtin::Text => T::text(),
            _ => unreachable!(),
        },
        NirKind::OptionalType(t) => T::optional(fold_simple_type(t)?),
        NirKind::ListType(t) => T::list(fold_simple_type(t)?),
        NirKind::RecordType(kts) => T::record(
            kts.iter()
                .map(|(k, v)| Some((k.into(), fold_simple_type(v)?)))
                .collect::<Option<BTreeMap<_, _>>>()?
                .into_iter(),
        ),
        NirKind::UnionType(kts) => T::union(
            kts.iter()
                .map(|(k, v)| {
                    Some((
                        k.into(),
                        v.as_ref()
                            .map(|v| Ok(fold_simple_type(v)?))
                            .transpose()?,
                    ))
                })
                .collect::<Option<BTreeMap<_, _>>>()?
                .into_iter(),
        ),
        _ => return None,
    })
}

impl SimpleValueFolder for SimpleValue {
    fn num(x: NumKind) -> Self {
        SimpleValue::new(SValKind::Num(x))
    }
    fn text(x: String) -> Self {
        SimpleValue::new(SValKind::Text(x))
    }
    fn optional(x: Option<Self>) -> Self {
        SimpleValue::new(SValKind::Optional(x))
    }
    fn list(xs: impl Iterator<Item = Self>) -> Self {
        SimpleValue::new(SValKind::List(xs.collect()))
    }
    fn record(values: impl Iterator<Item = (String, Self)>) -> Self {
        SimpleValue::new(SValKind::Record(values.collect()))
    }
    fn union(variant: String, content: Option<Self>) -> Self {
        SimpleValue::new(SValKind::Union(variant, content))
    }
}

impl SimpleValue {
    pub(crate) fn new(kind: SValKind) -> Self {
        SimpleValue {
            kind: Box::new(kind),
        }
    }
    pub(crate) fn from_nir(nir: &Nir) -> Option<Self> {
        fold_simple_value::<Self>(nir)
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
