use std::collections::BTreeMap;

use crate::syntax::LitKind;

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
