use dhall_syntax::{Label, V};

/// Stores a pair of variables: a normal one and if relevant one
/// that corresponds to the alpha-normalized version of the first one.
/// Equality is up to alpha-equivalence.
#[derive(Debug, Clone, Eq)]
pub(crate) struct AlphaVar {
    normal: V<Label>,
    alpha: Option<V<()>>,
}

// Exactly like a Label, but equality returns always true.
// This is so that Value equality is exactly alpha-equivalence.
#[derive(Debug, Clone, Eq)]
pub(crate) struct AlphaLabel(Label);

pub(crate) trait Shift {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Self;
}

pub(crate) trait Subst<T>: Shift {
    fn subst_shift(&self, var: &AlphaVar, val: &T) -> Self;
}

impl AlphaVar {
    pub(crate) fn to_var(&self, alpha: bool) -> V<Label> {
        match (alpha, &self.alpha) {
            (true, Some(x)) => V("_".into(), x.1),
            _ => self.normal.clone(),
        }
    }
    pub(crate) fn from_var(normal: V<Label>) -> Self {
        AlphaVar {
            normal,
            alpha: None,
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
    fn shift(&self, delta: isize, var: &AlphaVar) -> Self {
        AlphaVar {
            normal: self.normal.shift(delta, &var.normal),
            alpha: match (&self.alpha, &var.alpha) {
                (Some(x), Some(v)) => Some(x.shift(delta, v)),
                _ => None,
            },
        }
    }
}

impl std::cmp::PartialEq for AlphaVar {
    fn eq(&self, other: &Self) -> bool {
        match (&self.alpha, &other.alpha) {
            (Some(x), Some(y)) => x == y,
            (None, None) => self.normal == other.normal,
            _ => false,
        }
    }
}
impl std::cmp::PartialEq for AlphaLabel {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl From<Label> for AlphaVar {
    fn from(x: Label) -> AlphaVar {
        AlphaVar {
            normal: V(x, 0),
            alpha: Some(V((), 0)),
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
