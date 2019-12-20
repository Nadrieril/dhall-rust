use std::collections::HashMap;

use crate::syntax::{ExprKind, InterpolatedTextContents, Label, V};

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

pub(crate) trait Subst<S> {
    fn subst_shift(&self, var: &AlphaVar, val: &S) -> Self;
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
impl Shift for () {
    fn shift(&self, _delta: isize, _var: &AlphaVar) -> Option<Self> {
        Some(())
    }
}

impl<A: Shift, B: Shift> Shift for (A, B) {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some((self.0.shift(delta, var)?, self.1.shift(delta, var)?))
    }
}

impl<T: Shift> Shift for Option<T> {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(match self {
            None => None,
            Some(x) => Some(x.shift(delta, var)?),
        })
    }
}

impl<T: Shift> Shift for Box<T> {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(Box::new(self.as_ref().shift(delta, var)?))
    }
}

impl<T: Shift> Shift for std::rc::Rc<T> {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(std::rc::Rc::new(self.as_ref().shift(delta, var)?))
    }
}

impl<T: Shift> Shift for std::cell::RefCell<T> {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(std::cell::RefCell::new(self.borrow().shift(delta, var)?))
    }
}

impl<T: Shift, E: Clone> Shift for ExprKind<T, E> {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(self.traverse_ref_with_special_handling_of_binders(
            |v| Ok(v.shift(delta, var)?),
            |x, v| Ok(v.shift(delta, &var.under_binder(x))?),
        )?)
    }
}

impl<T: Shift> Shift for Vec<T> {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(
            self.iter()
                .map(|v| Ok(v.shift(delta, var)?))
                .collect::<Result<_, _>>()?,
        )
    }
}

impl<K, T: Shift> Shift for HashMap<K, T>
where
    K: Clone + std::hash::Hash + Eq,
{
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(
            self.iter()
                .map(|(k, v)| Ok((k.clone(), v.shift(delta, var)?)))
                .collect::<Result<_, _>>()?,
        )
    }
}

impl<T: Shift> Shift for InterpolatedTextContents<T> {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(self.traverse_ref(|x| Ok(x.shift(delta, var)?))?)
    }
}

impl<S> Subst<S> for () {
    fn subst_shift(&self, _var: &AlphaVar, _val: &S) -> Self {}
}

impl<S, A: Subst<S>, B: Subst<S>> Subst<S> for (A, B) {
    fn subst_shift(&self, var: &AlphaVar, val: &S) -> Self {
        (self.0.subst_shift(var, val), self.1.subst_shift(var, val))
    }
}

impl<S, T: Subst<S>> Subst<S> for Option<T> {
    fn subst_shift(&self, var: &AlphaVar, val: &S) -> Self {
        self.as_ref().map(|x| x.subst_shift(var, val))
    }
}

impl<S, T: Subst<S>> Subst<S> for Box<T> {
    fn subst_shift(&self, var: &AlphaVar, val: &S) -> Self {
        Box::new(self.as_ref().subst_shift(var, val))
    }
}

impl<S, T: Subst<S>> Subst<S> for std::rc::Rc<T> {
    fn subst_shift(&self, var: &AlphaVar, val: &S) -> Self {
        std::rc::Rc::new(self.as_ref().subst_shift(var, val))
    }
}

impl<S, T: Subst<S>> Subst<S> for std::cell::RefCell<T> {
    fn subst_shift(&self, var: &AlphaVar, val: &S) -> Self {
        std::cell::RefCell::new(self.borrow().subst_shift(var, val))
    }
}

impl<S: Shift, T: Subst<S>, E: Clone> Subst<S> for ExprKind<T, E> {
    fn subst_shift(&self, var: &AlphaVar, val: &S) -> Self {
        self.map_ref_with_special_handling_of_binders(
            |v| v.subst_shift(var, val),
            |x, v| v.subst_shift(&var.under_binder(x), &val.under_binder(x)),
        )
    }
}

impl<S, T: Subst<S>> Subst<S> for Vec<T> {
    fn subst_shift(&self, var: &AlphaVar, val: &S) -> Self {
        self.iter().map(|v| v.subst_shift(var, val)).collect()
    }
}

impl<S, T: Subst<S>> Subst<S> for InterpolatedTextContents<T> {
    fn subst_shift(&self, var: &AlphaVar, val: &S) -> Self {
        self.map_ref(|x| x.subst_shift(var, val))
    }
}

impl<S, K, T: Subst<S>> Subst<S> for HashMap<K, T>
where
    K: Clone + std::hash::Hash + Eq,
{
    fn subst_shift(&self, var: &AlphaVar, val: &S) -> Self {
        self.iter()
            .map(|(k, v)| (k.clone(), v.subst_shift(var, val)))
            .collect()
    }
}
