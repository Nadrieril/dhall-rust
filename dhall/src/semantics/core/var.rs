use std::collections::HashMap;

use crate::syntax::{Label, V};

/// Stores an alpha-normalized variable.
#[derive(Clone, Eq)]
pub struct AlphaVar {
    alpha: V<()>,
}

// Exactly like a Label, but equality returns always true.
// This is so that ValueKind equality is exactly alpha-equivalence.
#[derive(Clone, Eq)]
pub struct Binder {
    name: Label,
}

impl AlphaVar {
    pub(crate) fn idx(&self) -> usize {
        self.alpha.idx()
    }

    pub(crate) fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(AlphaVar {
            alpha: self.alpha.shift(delta, &var.alpha)?,
        })
    }
    pub(crate) fn under_binder<T>(&self, x: T) -> Self
    where
        T: Into<AlphaVar>,
    {
        // Can't fail since delta is positive
        self.shift(1, &x.into()).unwrap()
    }
    pub(crate) fn over_binder(&self, x: &AlphaVar) -> Option<Self> {
        self.shift(-1, x)
    }
    pub(crate) fn under_multiple_binders(
        &self,
        shift_map: &HashMap<Label, usize>,
    ) -> Self {
        AlphaVar {
            alpha: self.alpha.under_multiple_binders(shift_map),
        }
    }
}

impl Binder {
    pub(crate) fn new(name: Label) -> Self {
        Binder { name }
    }
    pub(crate) fn to_label_maybe_alpha(&self, alpha: bool) -> Label {
        if alpha {
            "_".into()
        } else {
            self.to_label()
        }
    }
    pub(crate) fn to_label(&self) -> Label {
        self.clone().into()
    }
    pub(crate) fn name(&self) -> &Label {
        &self.name
    }
}

/// Equality up to alpha-equivalence
impl std::cmp::PartialEq for AlphaVar {
    fn eq(&self, other: &Self) -> bool {
        self.alpha == other.alpha
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

impl<'a> From<&'a Label> for AlphaVar {
    fn from(x: &'a Label) -> AlphaVar {
        AlphaVar { alpha: V((), 0) }
    }
}
impl From<Binder> for AlphaVar {
    fn from(x: Binder) -> AlphaVar {
        AlphaVar { alpha: V((), 0) }
    }
}
impl<'a> From<&'a Binder> for AlphaVar {
    fn from(x: &'a Binder) -> AlphaVar {
        x.clone().into()
    }
}

impl From<Binder> for Label {
    fn from(x: Binder) -> Label {
        x.name
    }
}
