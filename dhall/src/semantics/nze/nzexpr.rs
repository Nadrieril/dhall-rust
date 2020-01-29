use crate::semantics::core::var::AlphaVar;
use crate::syntax::{Label, V};

pub(crate) type Binder = Label;

#[derive(Debug, Clone)]
pub(crate) struct NameEnv {
    names: Vec<Binder>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct QuoteEnv {
    size: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NzVar {
    /// Reverse-debruijn index: counts number of binders from the bottom of the stack.
    Bound(usize),
    /// Fake fresh variable generated for expression equality checking.
    Fresh(usize),
}

impl NameEnv {
    pub fn new() -> Self {
        NameEnv { names: Vec::new() }
    }
    pub fn from_binders(names: impl Iterator<Item = Binder>) -> Self {
        NameEnv {
            names: names.collect(),
        }
    }
    pub fn as_quoteenv(&self) -> QuoteEnv {
        QuoteEnv {
            size: self.names.len(),
        }
    }
    pub fn names(&self) -> &[Binder] {
        &self.names
    }

    pub fn insert(&self, x: &Binder) -> Self {
        let mut env = self.clone();
        env.insert_mut(x);
        env
    }
    pub fn insert_mut(&mut self, x: &Binder) {
        self.names.push(x.clone())
    }
    // pub fn remove_mut(&mut self) {
    //     self.names.pop();
    // }

    pub fn unlabel_var(&self, var: &V<Binder>) -> Option<AlphaVar> {
        let V(name, idx) = var;
        let (idx, _) = self
            .names
            .iter()
            .rev()
            .enumerate()
            .filter(|(_, n)| *n == name)
            .nth(*idx)?;
        Some(AlphaVar::new(V((), idx)))
    }
    // pub fn label_var(&self, var: &AlphaVar) -> V<Binder> {
    //     let name = &self.names[self.names.len() - 1 - var.idx()];
    //     let idx = self
    //         .names
    //         .iter()
    //         .rev()
    //         .take(var.idx())
    //         .filter(|n| *n == name)
    //         .count();
    //     V(name.clone(), idx)
    // }
}

// TODO: rename to VarEnv
impl QuoteEnv {
    pub fn new() -> Self {
        QuoteEnv { size: 0 }
    }
    pub fn size(&self) -> usize {
        self.size
    }
    pub fn insert(&self) -> Self {
        QuoteEnv {
            size: self.size + 1,
        }
    }
    pub fn lookup(&self, var: &NzVar) -> AlphaVar {
        self.lookup_fallible(var).unwrap()
    }
    pub fn lookup_fallible(&self, var: &NzVar) -> Option<AlphaVar> {
        let idx = self.size.checked_sub(var.idx() + 1)?;
        Some(AlphaVar::new(V((), idx)))
    }
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
    pub fn shift(&self, delta: isize) -> Self {
        NzVar::new((self.idx() as isize + delta) as usize)
    }
    // Panics on a fresh variable.
    pub fn idx(&self) -> usize {
        match self {
            NzVar::Bound(i) => *i,
            NzVar::Fresh(_) => panic!(
                "Trying to use a fresh variable outside of equality checking"
            ),
        }
    }
}
