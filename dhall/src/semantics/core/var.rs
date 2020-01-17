use std::collections::HashMap;

use crate::syntax::{Label, V};

/// Stores a pair of variables: a normal one and one
/// that corresponds to the alpha-normalized version of the first one.
/// Equality is up to alpha-equivalence (compares on the second one only).
#[derive(Clone, Eq)]
pub struct AlphaVar {
    normal: V<Label>,
    alpha: V<()>,
}

// Exactly like a Label, but equality returns always true.
// This is so that ValueKind equality is exactly alpha-equivalence.
#[derive(Clone, Eq)]
pub struct Binder {
    name: Label,
}

pub(crate) trait Shift: Sized {
    // Shift an expression to move it around binders without changing the meaning of its free
    // variables. Shift by 1 to move an expression under a binder. Shift by -1 to extract an
    // expression from under a binder, if the expression does not refer to that bound variable.
    // Returns None if delta was negative and the variable was free in the expression.
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self>;

    fn over_binder<T>(&self, x: T) -> Option<Self>
    where
        T: Into<AlphaVar>,
    {
        self.shift(-1, &x.into())
    }

    fn under_binder<T>(&self, x: T) -> Self
    where
        T: Into<AlphaVar>,
    {
        // Can't fail since delta is positive
        self.shift(1, &x.into()).unwrap()
    }

    fn under_multiple_binders(&self, shift_map: &HashMap<Label, usize>) -> Self
    where
        Self: Clone,
    {
        let mut v = self.clone();
        for (x, n) in shift_map {
            v = v.shift(*n as isize, &x.into()).unwrap();
        }
        v
    }
}

pub(crate) trait Subst<S> {
    fn subst_shift(&self, var: &AlphaVar, val: &S) -> Self;
}

impl AlphaVar {
    pub(crate) fn to_var_maybe_alpha(&self, alpha: bool) -> V<Label> {
        if alpha {
            V("_".into(), self.alpha.idx())
        } else {
            self.normal.clone()
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
}

impl Shift for AlphaVar {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(AlphaVar {
            normal: self.normal.shift(delta, &var.normal)?,
            alpha: self.alpha.shift(delta, &var.alpha)?,
        })
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
        write!(f, "AlphaVar({}, {})", self.normal, self.alpha.1)
    }
}

impl std::fmt::Debug for Binder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Binder({})", &self.name)
    }
}

impl<'a> From<&'a Label> for AlphaVar {
    fn from(x: &'a Label) -> AlphaVar {
        AlphaVar {
            normal: V(x.clone(), 0),
            alpha: V((), 0),
        }
    }
}
impl From<Binder> for AlphaVar {
    fn from(x: Binder) -> AlphaVar {
        AlphaVar {
            normal: V(x.into(), 0),
            alpha: V((), 0),
        }
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
