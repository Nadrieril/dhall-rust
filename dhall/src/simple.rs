use std::collections::BTreeMap;

use crate::syntax::{Builtin, LitKind};
use crate::Normalized;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimpleValue {
    kind: Box<SValKind>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SValKind {
    Lit(LitKind),
    Optional(Option<SimpleValue>),
    List(Vec<SimpleValue>),
    Record(BTreeMap<String, SimpleValue>),
    Union(String, Option<SimpleValue>),
    Text(String),
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
    pub fn kind(&self) -> &STyKind {
        self.kind.as_ref()
    }
    pub fn into_normalized(self) -> Normalized {
        match *self.kind {
            STyKind::Bool => Normalized::make_builtin_type(Builtin::Bool),
            STyKind::Natural => Normalized::make_builtin_type(Builtin::Natural),
            STyKind::Integer => Normalized::make_builtin_type(Builtin::Integer),
            STyKind::Double => Normalized::make_builtin_type(Builtin::Double),
            STyKind::Text => Normalized::make_builtin_type(Builtin::Text),
            STyKind::Optional(t) => {
                Normalized::make_optional_type(t.into_normalized())
            }
            STyKind::List(t) => Normalized::make_list_type(t.into_normalized()),
            STyKind::Record(kts) => Normalized::make_record_type(
                kts.into_iter().map(|(k, t)| (k, t.into_normalized())),
            ),
            STyKind::Union(kts) => Normalized::make_union_type(
                kts.into_iter()
                    .map(|(k, t)| (k, t.map(|t| t.into_normalized()))),
            ),
        }
    }
}
