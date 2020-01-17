use crate::error::TypeError;
use crate::semantics::core::value::Value;
use crate::semantics::core::value::ValueKind;
use crate::semantics::core::var::{AlphaVar, Binder};
use crate::syntax::{Label, V};

#[derive(Debug, Clone)]
enum CtxItem {
    // Variable is bound with given type
    Kept(Value),
    // Variable has been replaced by corresponding value
    Replaced(Value),
}

#[derive(Debug, Clone)]
pub(crate) struct TyCtx {
    ctx: Vec<(Binder, CtxItem)>,
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
        vec.push((x.clone(), CtxItem::Kept(t.under_binder())));
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
        let mut shift_delta: isize = 0;
        let mut rev_ctx = self.ctx.iter().rev().map(|(b, i)| (b.to_label(), i));

        let found_item = loop {
            if let Some((label, item)) = rev_ctx.next() {
                var = match var.over_binder(&label) {
                    Some(newvar) => newvar,
                    None => break item,
                };
                if let CtxItem::Kept(_) = item {
                    shift_delta += 1;
                }
            } else {
                // Unbound variable
                return None;
            }
        };

        let v = match found_item {
            CtxItem::Kept(t) => Value::from_kind_and_type(
                ValueKind::Var(AlphaVar::default()),
                t.clone(),
            ),
            CtxItem::Replaced(v) => v.clone(),
        };
        // Can't fail because delta is positive
        let v = v.shift(shift_delta, &AlphaVar::default()).unwrap();
        return Some(v);
    }
    // pub fn lookup_alpha(&self, var: &AlphaVar) -> Option<Value> {
    //     self.lookup(&var.normal)
    // }
    pub fn new_binder(&self, l: &Label) -> Binder {
        Binder::new(l.clone())
    }
}
