use crate::semantics::{AlphaVar, Type, Value, ValueKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NzVar {
    /// Reverse-debruijn index: counts number of binders from the bottom of the stack.
    Bound(usize),
    /// Fake fresh variable generated for expression equality checking.
    Fresh(usize),
}

#[derive(Debug, Clone)]
enum NzEnvItem {
    // Variable is bound with given type
    Kept(Type),
    // Variable has been replaced by corresponding value
    Replaced(Value, Type),
}

#[derive(Debug, Clone)]
pub(crate) struct NzEnv {
    items: Vec<NzEnvItem>,
}

impl NzVar {
    pub fn new(idx: usize) -> Self {
        NzVar::Bound(idx)
    }
    pub fn fresh() -> Self {
        use std::sync::atomic::{AtomicUsize, Ordering};
        // Global counter to ensure uniqueness of the generated id.
        static FRESH_VAR_COUNTER: AtomicUsize = AtomicUsize::new(0);
        let id = FRESH_VAR_COUNTER.fetch_add(1, Ordering::SeqCst);
        NzVar::Fresh(id)
    }
    /// Get index of bound variable.
    /// Panics on a fresh variable.
    pub fn idx(&self) -> usize {
        match self {
            NzVar::Bound(i) => *i,
            NzVar::Fresh(_) => panic!(
                "Trying to use a fresh variable outside of equality checking"
            ),
        }
    }
}

impl NzEnv {
    pub fn new() -> Self {
        NzEnv { items: Vec::new() }
    }

    pub fn insert_type(&self, ty: Type) -> Self {
        let mut env = self.clone();
        env.items.push(NzEnvItem::Kept(ty));
        env
    }
    pub fn insert_value(&self, e: Value, ty: Type) -> Self {
        let mut env = self.clone();
        env.items.push(NzEnvItem::Replaced(e, ty));
        env
    }
    pub fn insert_value_noty(&self, e: Value) -> Self {
        // TODO
        let ty = Value::const_sort();
        self.insert_value(e, ty)
    }
    pub fn lookup_val(&self, var: &AlphaVar) -> ValueKind {
        let idx = self.items.len() - 1 - var.idx();
        match &self.items[idx] {
            NzEnvItem::Kept(_) => ValueKind::Var(NzVar::new(idx)),
            NzEnvItem::Replaced(x, _) => x.kind().clone(),
        }
    }
    pub fn lookup_ty(&self, var: &AlphaVar) -> Value {
        let idx = self.items.len() - 1 - var.idx();
        match &self.items[idx] {
            NzEnvItem::Kept(ty) | NzEnvItem::Replaced(_, ty) => ty.clone(),
        }
    }
}
