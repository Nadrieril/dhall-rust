use std::borrow::Cow;
use std::rc::Rc;

use dhall_syntax::context::Context;
use dhall_syntax::{Label, V};

use crate::core::thunk::Thunk;
use crate::core::value::Value;
use crate::core::var::AlphaVar;
use crate::phase::{Normalized, Type, Typed};

#[derive(Debug, Clone)]
enum NzEnvItem {
    Thunk(Thunk),
    Skip(AlphaVar),
}

#[derive(Debug, Clone)]
pub(crate) struct NormalizationContext(Rc<Context<Label, NzEnvItem>>);

#[derive(Debug, Clone)]
pub(crate) enum TyEnvItem {
    Type(AlphaVar, Type),
    Value(Normalized),
}

#[derive(Debug, Clone)]
pub(crate) struct TypecheckContext(pub(crate) Context<Label, TyEnvItem>);

impl NzEnvItem {
    pub(crate) fn shift(&self, delta: isize, var: &AlphaVar) -> Self {
        use NzEnvItem::*;
        match self {
            Thunk(e) => Thunk(e.shift(delta, var)),
            Skip(v) => Skip(v.shift(delta, var)),
        }
    }

    pub(crate) fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        match self {
            NzEnvItem::Thunk(e) => NzEnvItem::Thunk(e.subst_shift(var, val)),
            NzEnvItem::Skip(v) if v == var => NzEnvItem::Thunk(val.to_thunk()),
            NzEnvItem::Skip(v) => NzEnvItem::Skip(v.shift(-1, var)),
        }
    }
}

impl NormalizationContext {
    pub(crate) fn new() -> Self {
        NormalizationContext(Rc::new(Context::new()))
    }
    pub(crate) fn skip(&self, x: &Label) -> Self {
        NormalizationContext(Rc::new(
            self.0
                .map(|_, e| e.shift(1, &x.into()))
                .insert(x.clone(), NzEnvItem::Skip(x.into())),
        ))
    }
    pub(crate) fn lookup(&self, var: &V<Label>) -> Value {
        let V(x, n) = var;
        match self.0.lookup(x, *n) {
            Some(NzEnvItem::Thunk(t)) => t.to_value(),
            Some(NzEnvItem::Skip(newvar)) => Value::Var(newvar.clone()),
            // Free variable
            None => Value::Var(AlphaVar::from_var(var.clone())),
        }
    }
    pub(crate) fn from_typecheck_ctx(tc_ctx: &TypecheckContext) -> Self {
        use TyEnvItem::*;
        let mut ctx = Context::new();
        for (k, vs) in tc_ctx.0.iter_keys() {
            for v in vs.iter() {
                let new_item = match v {
                    Type(var, _) => NzEnvItem::Skip(var.clone()),
                    Value(e) => NzEnvItem::Thunk(e.to_thunk()),
                };
                ctx = ctx.insert(k.clone(), new_item);
            }
        }
        NormalizationContext(Rc::new(ctx))
    }

    pub(crate) fn shift(&self, delta: isize, var: &AlphaVar) -> Self {
        NormalizationContext(Rc::new(self.0.map(|_, e| e.shift(delta, var))))
    }

    pub(crate) fn subst_shift(&self, var: &AlphaVar, val: &Typed) -> Self {
        NormalizationContext(Rc::new(
            self.0.map(|_, e| e.subst_shift(var, val)),
        ))
    }
}

impl TyEnvItem {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Self {
        use TyEnvItem::*;
        match self {
            Type(v, e) => Type(v.shift(delta, var), e.shift(delta, var)),
            Value(e) => Value(e.shift(delta, var)),
        }
    }
}

impl TypecheckContext {
    pub(crate) fn new() -> Self {
        TypecheckContext(Context::new())
    }
    pub(crate) fn insert_type(&self, x: &Label, t: Type) -> Self {
        TypecheckContext(self.0.map(|_, e| e.shift(1, &x.into())).insert(
            x.clone(),
            TyEnvItem::Type(x.into(), t.shift(1, &x.into())),
        ))
    }
    pub(crate) fn insert_value(&self, x: &Label, t: Normalized) -> Self {
        TypecheckContext(self.0.insert(x.clone(), TyEnvItem::Value(t)))
    }
    pub(crate) fn lookup(&self, var: &V<Label>) -> Option<Cow<'_, Type>> {
        let V(x, n) = var;
        match self.0.lookup(x, *n) {
            Some(TyEnvItem::Type(_, t)) => Some(Cow::Borrowed(&t)),
            Some(TyEnvItem::Value(t)) => Some(t.get_type()?),
            None => None,
        }
    }
    pub(crate) fn to_normalization_ctx(&self) -> NormalizationContext {
        NormalizationContext::from_typecheck_ctx(self)
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
