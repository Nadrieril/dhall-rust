use std::collections::HashMap;
use std::rc::Rc;

use dhall_syntax::{Label, V};

use crate::core::thunk::Thunk;
use crate::core::value::Value;
use crate::core::var::{AlphaVar, Shift, Subst};
use crate::error::TypeError;
use crate::phase::{Type, Typed};

#[derive(Debug, Clone)]
pub enum CtxItem<T> {
    Kept(AlphaVar, T),
    Replaced(Thunk, T),
}

#[derive(Debug, Clone)]
pub struct Context<T>(Rc<Vec<(Label, CtxItem<T>)>>);

#[derive(Debug, Clone)]
pub struct NormalizationContext(Context<()>);

#[derive(Debug, Clone)]
pub struct TypecheckContext(Context<Type>);

impl<T> Context<T> {
    pub fn new() -> Self {
        Context(Rc::new(Vec::new()))
    }
    pub fn insert_kept(&self, x: &Label, t: T) -> Self
    where
        T: Shift + Clone,
    {
        let mut vec = self.0.as_ref().clone();
        vec.push((x.clone(), CtxItem::Kept(x.into(), t.under_binder(x))));
        Context(Rc::new(vec))
    }
    pub fn insert_replaced(&self, x: &Label, th: Thunk, t: T) -> Self
    where
        T: Clone,
    {
        let mut vec = self.0.as_ref().clone();
        vec.push((x.clone(), CtxItem::Replaced(th, t)));
        Context(Rc::new(vec))
    }
    pub fn lookup(&self, var: &V<Label>) -> Result<CtxItem<T>, V<Label>>
    where
        T: Clone + Shift,
    {
        let mut var = var.clone();
        let mut shift_map: HashMap<Label, _> = HashMap::new();
        for (l, i) in self.0.iter().rev() {
            match var.over_binder(l) {
                None => return Ok(i.under_multiple_binders(&shift_map)),
                Some(newvar) => var = newvar,
            };
            if let CtxItem::Kept(_, _) = i {
                *shift_map.entry(l.clone()).or_insert(0) += 1;
            }
        }
        // Free variable
        Err(var)
    }
    /// Given a var that makes sense in the current context, map the given function in such a way
    /// that the passed variable always makes sense in the context of the passed item.
    /// Once we pass the variable definition, the variable doesn't make sense anymore so we just
    /// copy the remaining items.
    fn do_with_var<E>(
        &self,
        var: &AlphaVar,
        mut f: impl FnMut(&AlphaVar, &CtxItem<T>) -> Result<CtxItem<T>, E>,
    ) -> Result<Self, E>
    where
        T: Clone,
    {
        let mut vec = Vec::new();
        vec.reserve(self.0.len());
        let mut var = var.clone();
        let mut iter = self.0.iter().rev();
        for (l, i) in iter.by_ref() {
            vec.push((l.clone(), f(&var, i)?));
            if let CtxItem::Kept(_, _) = i {
                match var.over_binder(l) {
                    None => break,
                    Some(newvar) => var = newvar,
                };
            }
        }
        for (l, i) in iter {
            vec.push((l.clone(), (*i).clone()));
        }
        vec.reverse();
        Ok(Context(Rc::new(vec)))
    }
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self>
    where
        T: Clone + Shift,
    {
        if delta < 0 {
            Some(self.do_with_var(var, |var, i| Ok(i.shift(delta, &var)?))?)
        } else {
            Some(Context(Rc::new(
                self.0
                    .iter()
                    .map(|(l, i)| Ok((l.clone(), i.shift(delta, &var)?)))
                    .collect::<Result<_, _>>()?,
            )))
        }
    }
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self
    where
        T: Clone + Subst<Typed>,
    {
        self.do_with_var(var, |var, i| Ok::<_, !>(i.subst_shift(&var, val)))
            .unwrap()
    }
}

impl NormalizationContext {
    pub fn new() -> Self {
        NormalizationContext(Context::new())
    }
    pub fn skip(&self, x: &Label) -> Self {
        NormalizationContext(self.0.insert_kept(x, ()))
    }
    pub fn lookup(&self, var: &V<Label>) -> Value {
        match self.0.lookup(var) {
            Ok(CtxItem::Replaced(t, ())) => t.to_value(),
            Ok(CtxItem::Kept(newvar, ())) => Value::Var(newvar.clone()),
            Err(var) => Value::Var(AlphaVar::from_var(var)),
        }
    }
}

impl TypecheckContext {
    pub fn new() -> Self {
        TypecheckContext(Context::new())
    }
    pub fn insert_type(&self, x: &Label, t: Type) -> Self {
        TypecheckContext(self.0.insert_kept(x, t))
    }
    pub fn insert_value(&self, x: &Label, e: Typed) -> Result<Self, TypeError> {
        Ok(TypecheckContext(self.0.insert_replaced(
            x,
            e.to_thunk(),
            e.get_type()?.into_owned(),
        )))
    }
    pub fn lookup(&self, var: &V<Label>) -> Option<Typed> {
        match self.0.lookup(var) {
            Ok(CtxItem::Kept(newvar, t)) => Some(Typed::from_thunk_and_type(
                Thunk::from_value(Value::Var(newvar.clone())),
                t.clone(),
            )),
            Ok(CtxItem::Replaced(th, t)) => {
                Some(Typed::from_thunk_and_type(th.clone(), t.clone()))
            }
            Err(_) => None,
        }
    }
}

impl<T: Shift> Shift for CtxItem<T> {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(match self {
            CtxItem::Kept(v, t) => {
                CtxItem::Kept(v.shift(delta, var)?, t.shift(delta, var)?)
            }
            CtxItem::Replaced(e, t) => {
                CtxItem::Replaced(e.shift(delta, var)?, t.shift(delta, var)?)
            }
        })
    }
}

impl<T: Clone + Shift> Shift for Context<T> {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        self.shift(delta, var)
    }
}

impl Shift for NormalizationContext {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(NormalizationContext(self.0.shift(delta, var)?))
    }
}

impl<T: Subst<Typed>> Subst<Typed> for CtxItem<T> {
    fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        match self {
            CtxItem::Replaced(e, t) => CtxItem::Replaced(
                e.subst_shift(var, val),
                t.subst_shift(var, val),
            ),
            CtxItem::Kept(v, t) => match v.shift(-1, var) {
                None => {
                    CtxItem::Replaced(val.to_thunk(), t.subst_shift(var, val))
                }
                Some(newvar) => CtxItem::Kept(newvar, t.subst_shift(var, val)),
            },
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
