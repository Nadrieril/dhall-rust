use crate::semantics::{AlphaVar, Nir, NirKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NzVar {
    /// Reverse-debruijn index: counts number of binders from the bottom of the stack.
    Bound(usize),
    /// Fake fresh variable generated for expression equality checking.
    Fresh(usize),
}

#[derive(Debug, Clone)]
enum EnvItem<Type> {
    // Variable is bound with given type
    Kept(Type),
    // Variable has been replaced by corresponding value
    Replaced(Nir, Type),
}

#[derive(Debug, Clone)]
pub(crate) struct ValEnv<Type> {
    items: Vec<EnvItem<Type>>,
}

pub(crate) type NzEnv = ValEnv<()>;

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

impl<Type: Clone> ValEnv<Type> {
    pub fn new() -> Self {
        ValEnv { items: Vec::new() }
    }
    pub fn discard_types(&self) -> ValEnv<()> {
        let items = self
            .items
            .iter()
            .map(|i| match i {
                EnvItem::Kept(_) => EnvItem::Kept(()),
                EnvItem::Replaced(val, _) => EnvItem::Replaced(val.clone(), ()),
            })
            .collect();
        ValEnv { items }
    }

    pub fn insert_type(&self, ty: Type) -> Self {
        let mut env = self.clone();
        env.items.push(EnvItem::Kept(ty));
        env
    }
    pub fn insert_value(&self, e: Nir, ty: Type) -> Self {
        let mut env = self.clone();
        env.items.push(EnvItem::Replaced(e, ty));
        env
    }
    pub fn lookup_val(&self, var: AlphaVar) -> NirKind {
        let idx = self.items.len() - 1 - var.idx();
        match &self.items[idx] {
            EnvItem::Kept(_) => NirKind::Var(NzVar::new(idx)),
            EnvItem::Replaced(x, _) => x.kind().clone(),
        }
    }
    pub fn lookup_ty(&self, var: AlphaVar) -> Type {
        let idx = self.items.len() - 1 - var.idx();
        match &self.items[idx] {
            EnvItem::Kept(ty) | EnvItem::Replaced(_, ty) => ty.clone(),
        }
    }
}

impl<'a> From<&'a NzEnv> for NzEnv {
    fn from(x: &'a NzEnv) -> Self {
        x.clone()
    }
}
