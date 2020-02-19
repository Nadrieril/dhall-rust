use crate::syntax::Label;

// Exactly like a Label, but equality returns always true.
// This is so that NirKind equality is exactly alpha-equivalence.
#[derive(Clone, Eq)]
pub struct Binder {
    name: Label,
}

impl Binder {
    pub(crate) fn new(name: Label) -> Self {
        Binder { name }
    }
    pub(crate) fn to_label(&self) -> Label {
        self.clone().into()
    }
}

/// Equality up to alpha-equivalence
impl std::cmp::PartialEq for Binder {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl std::fmt::Debug for Binder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Binder({})", &self.name)
    }
}

impl From<Binder> for Label {
    fn from(x: Binder) -> Label {
        x.name
    }
}
