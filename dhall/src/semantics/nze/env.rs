use crate::semantics::{AlphaVar, Nir, NirKind};
use crate::Ctxt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NzVar {
    /// Reverse-debruijn index: counts number of binders from the bottom of the stack.
    Bound(usize),
    /// Fake fresh variable generated for expression equality checking.
    Fresh(usize),
}

#[derive(Debug, Clone)]
enum EnvItem<'cx, T> {
    // Variable is bound with given type
    Kept(T),
    // Variable has been replaced by corresponding value
    Replaced(Nir<'cx>, T),
}

#[derive(Debug, Clone)]
pub struct ValEnv<'cx, T> {
    cx: Ctxt<'cx>,
    items: Vec<EnvItem<'cx, T>>,
}

pub type NzEnv<'cx> = ValEnv<'cx, ()>;

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

impl<'cx, T: Clone> ValEnv<'cx, T> {
    pub fn new(cx: Ctxt<'cx>) -> Self {
        ValEnv {
            cx,
            items: Vec::new(),
        }
    }
    pub fn cx(&self) -> Ctxt<'cx> {
        self.cx
    }
    pub fn discard_types(&self) -> ValEnv<'cx, ()> {
        let items = self
            .items
            .iter()
            .map(|i| match i {
                EnvItem::Kept(_) => EnvItem::Kept(()),
                EnvItem::Replaced(val, _) => EnvItem::Replaced(val.clone(), ()),
            })
            .collect();
        ValEnv { cx: self.cx, items }
    }

    pub fn insert_type(&self, ty: T) -> Self {
        let mut env = self.clone();
        env.items.push(EnvItem::Kept(ty));
        env
    }
    pub fn insert_value(&self, e: Nir<'cx>, ty: T) -> Self {
        let mut env = self.clone();
        env.items.push(EnvItem::Replaced(e, ty));
        env
    }
    pub fn lookup_val(&self, var: AlphaVar) -> NirKind<'cx> {
        let idx = self.items.len() - 1 - var.idx();
        match &self.items[idx] {
            EnvItem::Kept(_) => NirKind::Var(NzVar::new(idx)),
            EnvItem::Replaced(x, _) => x.kind().clone(),
        }
    }
    pub fn lookup_ty(&self, var: AlphaVar) -> T {
        let idx = self.items.len() - 1 - var.idx();
        match &self.items[idx] {
            EnvItem::Kept(ty) | EnvItem::Replaced(_, ty) => ty.clone(),
        }
    }
}

impl<'cx, 'a> From<&'a NzEnv<'cx>> for NzEnv<'cx> {
    fn from(x: &'a NzEnv<'cx>) -> Self {
        x.clone()
    }
}
