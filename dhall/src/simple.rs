use std::collections::BTreeMap;

use crate::semantics::{Hir, HirKind};
use crate::syntax::{Builtin, ExprKind, NumKind, Span};
use crate::Value;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimpleValue {
    kind: Box<SValKind>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SValKind {
    Num(NumKind),
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
