use crate::semantics::{AlphaVar, Value, ValueKind};

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
    Kept(Value),
    // Variable has been replaced by corresponding value
    Replaced(Value),
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

    pub fn insert_type(&self, t: Value) -> Self {
        let mut env = self.clone();
        env.items.push(NzEnvItem::Kept(t));
        env
    }
    pub fn insert_value(&self, e: Value) -> Self {
        let mut env = self.clone();
        env.items.push(NzEnvItem::Replaced(e));
        env
    }
    pub fn lookup_val(&self, var: &AlphaVar) -> Value {
        let idx = self.items.len() - 1 - var.idx();
        match &self.items[idx] {
            NzEnvItem::Kept(ty) => Value::from_kind_and_type_whnf(
                ValueKind::Var(NzVar::new(idx)),
                ty.clone(),
            ),
            NzEnvItem::Replaced(x) => x.clone(),
        }
    }
}

/// Ignore NzEnv when comparing; useful because we store them in `AppliedBuiltin`.
impl std::cmp::PartialEq for NzEnv {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}
impl std::cmp::Eq for NzEnv {}
