use crate::syntax::{Label, V};

/// Stores an alpha-normalized variable.
#[derive(Clone, Copy, Eq)]
pub struct AlphaVar {
    alpha: V<()>,
}
// TODO: temporary hopefully
impl std::cmp::PartialEq for AlphaVar {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

// Exactly like a Label, but equality returns always true.
// This is so that ValueKind equality is exactly alpha-equivalence.
#[derive(Clone, Eq)]
pub struct Binder {
    name: Label,
}

impl AlphaVar {
    pub(crate) fn new(alpha: V<()>) -> Self {
        AlphaVar { alpha }
    }
    pub(crate) fn default() -> Self {
        AlphaVar { alpha: V((), 0) }
    }
    pub(crate) fn idx(&self) -> usize {
        self.alpha.idx()
    }

    pub(crate) fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(AlphaVar {
            alpha: self.alpha.shift(delta, &var.alpha)?,
        })
    }
    pub(crate) fn under_binder(&self) -> Self {
        // Can't fail since delta is positive
        self.shift(1, &AlphaVar::default()).unwrap()
    }
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

impl std::fmt::Debug for AlphaVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "AlphaVar({})", self.alpha.1)
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
