use std::collections::HashMap;

use dhall_syntax::{Label, V};

/// Stores a pair of variables: a normal one and one
/// that corresponds to the alpha-normalized version of the first one.
/// Equality is up to alpha-equivalence (compares on the second one only).
#[derive(Clone, Eq)]
pub struct AlphaVar {
    normal: V<Label>,
    alpha: V<()>,
}

// Exactly like a Label, but equality returns always true.
// This is so that Value equality is exactly alpha-equivalence.
#[derive(Clone, Eq)]
pub struct AlphaLabel(Label);

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

pub(crate) trait Subst<T> {
    fn subst_shift(&self, var: &AlphaVar, val: &T) -> Self;
}

impl AlphaVar {
    pub(crate) fn to_var(&self, alpha: bool) -> V<Label> {
        if alpha {
            V("_".into(), self.alpha.1)
        } else {
            self.normal.clone()
        }
    }
    pub(crate) fn from_var_and_alpha(normal: V<Label>, alpha: usize) -> Self {
        AlphaVar {
            normal,
            alpha: V((), alpha),
        }
    }
}

impl AlphaLabel {
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

impl Shift for () {
    fn shift(&self, _delta: isize, _var: &AlphaVar) -> Option<Self> {
        Some(())
    }
}

impl<T> Subst<T> for () {
    fn subst_shift(&self, _var: &AlphaVar, _val: &T) -> Self {}
}

/// Equality up to alpha-equivalence
impl std::cmp::PartialEq for AlphaVar {
    fn eq(&self, other: &Self) -> bool {
        self.alpha == other.alpha
    }
}
impl std::cmp::PartialEq for AlphaLabel {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl std::fmt::Debug for AlphaVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "AlphaVar({}, {})", self.normal, self.alpha.1)
    }
}

impl std::fmt::Debug for AlphaLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "AlphaLabel({})", &self.0)
    }
}

impl From<Label> for AlphaVar {
    fn from(x: Label) -> AlphaVar {
        AlphaVar {
            normal: V(x, 0),
            alpha: V((), 0),
        }
    }
}
impl<'a> From<&'a Label> for AlphaVar {
    fn from(x: &'a Label) -> AlphaVar {
        x.clone().into()
    }
}
impl From<AlphaLabel> for AlphaVar {
    fn from(x: AlphaLabel) -> AlphaVar {
        let l: Label = x.into();
        l.into()
    }
}
impl<'a> From<&'a AlphaLabel> for AlphaVar {
    fn from(x: &'a AlphaLabel) -> AlphaVar {
        x.clone().into()
    }
}

impl From<Label> for AlphaLabel {
    fn from(x: Label) -> AlphaLabel {
        AlphaLabel(x)
    }
}
impl From<AlphaLabel> for Label {
    fn from(x: AlphaLabel) -> Label {
        x.0
    }
}
