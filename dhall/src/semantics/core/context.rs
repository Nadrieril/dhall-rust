use std::collections::HashMap;

use crate::error::TypeError;
use crate::semantics::core::value::Value;
use crate::semantics::core::value::ValueKind;
use crate::semantics::core::var::{AlphaVar, Binder};
use crate::syntax::{Label, V};

#[derive(Debug, Clone)]
enum CtxItem {
    Kept(AlphaVar, Value),
    Replaced(Value),
}

#[derive(Debug, Clone)]
pub(crate) struct TyCtx {
    ctx: Vec<(Binder, CtxItem)>,
}

impl CtxItem {
    fn shift(&self, delta: isize, var: &AlphaVar) -> Option<Self> {
        Some(match self {
            CtxItem::Kept(v, t) => {
                CtxItem::Kept(v.shift(delta, var)?, t.shift(delta, var)?)
            }
            CtxItem::Replaced(e) => CtxItem::Replaced(e.shift(delta, var)?),
        })
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

impl TyCtx {
    pub fn new() -> Self {
        TyCtx { ctx: Vec::new() }
    }
    fn with_vec(&self, vec: Vec<(Binder, CtxItem)>) -> Self {
        TyCtx { ctx: vec }
    }
    pub fn insert_type(&self, x: &Binder, t: Value) -> Self {
        let mut vec = self.ctx.clone();
        vec.push((x.clone(), CtxItem::Kept(x.into(), t.under_binder(x))));
        self.with_vec(vec)
    }
    pub fn insert_value(
        &self,
        x: &Binder,
        e: Value,
    ) -> Result<Self, TypeError> {
        let mut vec = self.ctx.clone();
        vec.push((x.clone(), CtxItem::Replaced(e)));
        Ok(self.with_vec(vec))
    }
    pub fn lookup(&self, var: &V<Label>) -> Option<Value> {
        let mut var = var.clone();
        let mut shift_map: HashMap<Label, _> = HashMap::new();
        for (b, i) in self.ctx.iter().rev() {
            let l = b.to_label();
            match var.over_binder(&l) {
                None => {
                    let i = i.under_multiple_binders(&shift_map);
                    return Some(match i {
                        CtxItem::Kept(newvar, t) => {
                            Value::from_kind_and_type(ValueKind::Var(newvar), t)
                        }
                        CtxItem::Replaced(v) => v,
                    });
                }
                Some(newvar) => var = newvar,
            };
            if let CtxItem::Kept(_, _) = i {
                *shift_map.entry(l).or_insert(0) += 1;
            }
        }
        // Unbound variable
        None
    }
    pub fn new_binder(&self, l: &Label) -> Binder {
        Binder::new(l.clone())
    }
}
