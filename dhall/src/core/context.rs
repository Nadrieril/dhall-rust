use std::collections::HashMap;
use std::rc::Rc;

use dhall_syntax::{Label, V};

use crate::core::thunk::Thunk;
use crate::core::value::Value;
use crate::core::var::{AlphaVar, Shift, Subst};
use crate::error::TypeError;
use crate::phase::{Type, Typed};

#[derive(Debug, Clone)]
pub(crate) enum CtxItem<T> {
    Kept(AlphaVar, T),
    Replaced(Thunk, T),
}

#[derive(Debug, Clone)]
pub(crate) struct Context<T>(Rc<Vec<(Label, CtxItem<T>)>>);

#[derive(Debug, Clone)]
pub(crate) struct NormalizationContext(Context<()>);

#[derive(Debug, Clone)]
pub(crate) struct TypecheckContext(Context<Type>);

impl<T> Context<T> {
    pub(crate) fn new() -> Self {
        Context(Rc::new(Vec::new()))
    }
    pub(crate) fn insert_kept(&self, x: &Label, t: T) -> Self
    where
        T: Shift + Clone,
    {
        let mut vec = self.0.as_ref().clone();
        vec.push((x.clone(), CtxItem::Kept(x.into(), t.shift(1, &x.into()))));
        Context(Rc::new(vec))
    }
    pub(crate) fn insert_replaced(&self, x: &Label, th: Thunk, t: T) -> Self
    where
        T: Clone,
    {
        let mut vec = self.0.as_ref().clone();
        vec.push((x.clone(), CtxItem::Replaced(th, t)));
        Context(Rc::new(vec))
    }
    pub(crate) fn lookup(&self, var: &V<Label>) -> Option<CtxItem<T>>
    where
        T: Clone + Shift,
    {
        let mut var = var.clone();
        let mut shift_map: HashMap<Label, _> = HashMap::new();
        for (l, i) in self.0.iter().rev() {
            if var == l.into() {
                return Some(i.shift0_multiple(&shift_map));
            } else {
                var = var.shift(-1, &l.into());
            }
            if let CtxItem::Kept(_, _) = i {
                *shift_map.entry(l.clone()).or_insert(0) += 1;
            }
        }
        None
    }
    /// Given a var that makes sense in the current context, map the given function in such a way
    /// that the passed variable always makes sense in the context of the passed item.
    /// Once we pass the variable definition, the variable doesn't make sense anymore so we just
    /// copy the remaining items.
    fn do_with_var(
        &self,
        var: &AlphaVar,
        mut f: impl FnMut(&AlphaVar, &CtxItem<T>) -> CtxItem<T>,
    ) -> Self
    where
        T: Clone,
    {
        let mut vec = Vec::new();
        vec.reserve(self.0.len());
        let mut var = var.clone();
        let mut iter = self.0.iter().rev();
        for (l, i) in iter.by_ref() {
            vec.push((l.clone(), f(&var, i)));
            if let CtxItem::Kept(_, _) = i {
                if var == l.into() {
                    break;
                } else {
                    var = var.shift(-1, &l.into());
                }
            }
        }
        for (l, i) in iter {
            vec.push((l.clone(), (*i).clone()));
        }
        vec.reverse();
        Context(Rc::new(vec))
    }
    fn shift(&self, delta: isize, var: &AlphaVar) -> Self
    where
        T: Clone + Shift,
    {
        self.do_with_var(var, |var, i| i.shift(delta, &var))
    }
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self
    where
        T: Clone + Subst<Typed>,
    {
        self.do_with_var(var, |var, i| i.subst_shift(&var, val))
    }
}

impl NormalizationContext {
    pub(crate) fn new() -> Self {
        NormalizationContext(Context::new())
    }
    pub(crate) fn skip(&self, x: &Label) -> Self {
        NormalizationContext(self.0.insert_kept(x, ()))
    }
    pub(crate) fn lookup(&self, var: &V<Label>) -> Value {
        match self.0.lookup(var) {
            Some(CtxItem::Replaced(t, ())) => t.to_value(),
            Some(CtxItem::Kept(newvar, ())) => Value::Var(newvar.clone()),
            // Free variable
            None => Value::Var(AlphaVar::from_var(var.clone())),
        }
    }
}

impl TypecheckContext {
    pub(crate) fn new() -> Self {
        TypecheckContext(Context::new())
    }
    pub(crate) fn insert_type(&self, x: &Label, t: Type) -> Self {
        TypecheckContext(self.0.insert_kept(x, t))
    }
    pub(crate) fn insert_value(
        &self,
        x: &Label,
        e: Typed,
    ) -> Result<Self, TypeError> {
        Ok(TypecheckContext(self.0.insert_replaced(
            x,
            e.to_thunk(),
            e.get_type()?.into_owned(),
        )))
    }
    pub(crate) fn lookup(&self, var: &V<Label>) -> Option<Typed> {
        match self.0.lookup(var) {
            Some(CtxItem::Kept(newvar, t)) => Some(Typed::from_thunk_and_type(
                Thunk::from_value(Value::Var(newvar.clone())),
                t.clone(),
            )),
            Some(CtxItem::Replaced(th, t)) => {
                Some(Typed::from_thunk_and_type(th.clone(), t.clone()))
            }
            None => None,
        }
    }
}

impl<T: Shift> Shift for CtxItem<T> {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Self {
        match self {
            CtxItem::Kept(v, t) => {
                CtxItem::Kept(v.shift(delta, var), t.shift(delta, var))
            }
            CtxItem::Replaced(e, t) => {
                CtxItem::Replaced(e.shift(delta, var), t.shift(delta, var))
            }
        }
    }
}

impl<T: Clone + Shift> Shift for Context<T> {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Self {
        self.shift(delta, var)
    }
}

impl Shift for NormalizationContext {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Self {
        NormalizationContext(self.0.shift(delta, var))
    }
}

impl<T: Subst<Typed>> Subst<Typed> for CtxItem<T> {
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        match self {
            CtxItem::Replaced(e, t) => CtxItem::Replaced(
                e.subst_shift(var, val),
                t.subst_shift(var, val),
            ),
            CtxItem::Kept(v, t) if v == var => {
                CtxItem::Replaced(val.to_thunk(), t.subst_shift(var, val))
            }
            CtxItem::Kept(v, t) => {
                CtxItem::Kept(v.shift(-1, var), t.subst_shift(var, val))
            }
        }
    }
}

impl<T: Clone + Subst<Typed>> Subst<Typed> for Context<T> {
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        self.subst_shift(var, val)
    }
}

impl Subst<Typed> for NormalizationContext {
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        NormalizationContext(self.0.subst_shift(var, val))
    }
}

impl PartialEq for TypecheckContext {
    fn eq(&self, _: &Self) -> bool {
        // don't count contexts when comparing stuff
        // this is dirty but needed for now
        true
    }
}
impl Eq for TypecheckContext {}
