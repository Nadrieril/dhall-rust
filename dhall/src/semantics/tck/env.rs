use crate::semantics::{AlphaVar, NzEnv, NzVar, TyExprKind, Type, Value};
use crate::syntax::{Label, V};

/// Environment for indexing variables.
#[derive(Debug, Clone, Copy)]
pub(crate) struct VarEnv {
    size: usize,
}

/// Environment for resolving names.
#[derive(Debug, Clone)]
pub(crate) struct NameEnv {
    names: Vec<Label>,
}

/// Environment for typing expressions.
#[derive(Debug, Clone)]
pub(crate) struct TyEnv {
    names: NameEnv,
    items: NzEnv,
}

impl VarEnv {
    pub fn new() -> Self {
        VarEnv { size: 0 }
    }
    pub fn size(&self) -> usize {
        self.size
    }
    pub fn insert(&self) -> Self {
        VarEnv {
            size: self.size + 1,
        }
    }
    pub fn lookup(&self, var: &NzVar) -> AlphaVar {
        self.lookup_fallible(var).unwrap()
    }
    pub fn lookup_fallible(&self, var: &NzVar) -> Option<AlphaVar> {
        let idx = self.size.checked_sub(var.idx() + 1)?;
        Some(AlphaVar::new(idx))
    }
}

impl NameEnv {
    pub fn new() -> Self {
        NameEnv { names: Vec::new() }
    }
    pub fn as_varenv(&self) -> VarEnv {
        VarEnv {
            size: self.names.len(),
        }
    }

    pub fn insert(&self, x: &Label) -> Self {
        let mut env = self.clone();
        env.insert_mut(x);
        env
    }
    pub fn insert_mut(&mut self, x: &Label) {
        self.names.push(x.clone())
    }
    pub fn remove_mut(&mut self) {
        self.names.pop();
    }

    pub fn unlabel_var(&self, var: &V) -> Option<AlphaVar> {
        let V(name, idx) = var;
        let (idx, _) = self
            .names
            .iter()
            .rev()
            .enumerate()
            .filter(|(_, n)| *n == name)
            .nth(*idx)?;
        Some(AlphaVar::new(idx))
    }
    pub fn label_var(&self, var: &AlphaVar) -> V {
        let name = &self.names[self.names.len() - 1 - var.idx()];
        let idx = self
            .names
            .iter()
            .rev()
            .take(var.idx())
            .filter(|n| *n == name)
            .count();
        V(name.clone(), idx)
    }
}

impl TyEnv {
    pub fn new() -> Self {
        TyEnv {
            names: NameEnv::new(),
            items: NzEnv::new(),
        }
    }
    pub fn as_varenv(&self) -> VarEnv {
        self.names.as_varenv()
    }
    pub fn as_nzenv(&self) -> &NzEnv {
        &self.items
    }
    pub fn as_nameenv(&self) -> &NameEnv {
        &self.names
    }

    pub fn insert_type(&self, x: &Label, t: Type) -> Self {
        TyEnv {
            names: self.names.insert(x),
            items: self.items.insert_type(t),
        }
    }
    pub fn insert_value(&self, x: &Label, e: Value) -> Self {
        TyEnv {
            names: self.names.insert(x),
            items: self.items.insert_value(e),
        }
    }
    pub fn lookup(&self, var: &V) -> Option<(TyExprKind, Type)> {
        let var = self.names.unlabel_var(var)?;
        let ty = self.items.lookup_ty(&var);
        Some((TyExprKind::Var(var), ty))
    }
}
