use std::collections::HashMap;

use crate::error::{Error, ImportError};
use crate::semantics::{AlphaVar, ImportLocation, TypedHir, VarEnv};
use crate::syntax::{Label, V};

/// Environment for resolving names.
#[derive(Debug, Clone, Default)]
pub struct NameEnv {
    names: Vec<Label>,
}

pub type ImportCache = HashMap<ImportLocation, TypedHir>;
pub type ImportStack = Vec<ImportLocation>;

/// Environment for resolving imports
#[derive(Debug, Clone, Default)]
pub struct ImportEnv {
    cache: ImportCache,
    stack: ImportStack,
}

impl NameEnv {
    pub fn new() -> Self {
        NameEnv::default()
    }
    pub fn as_varenv(&self) -> VarEnv {
        VarEnv::from_size(self.names.len())
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
    pub fn label_var(&self, var: AlphaVar) -> V {
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

impl ImportEnv {
    pub fn new() -> Self {
        ImportEnv::default()
    }

    pub fn get_from_cache<'a>(
        &'a self,
        location: &ImportLocation,
    ) -> Option<&'a TypedHir> {
        self.cache.get(location)
    }

    pub fn set_cache(&mut self, location: ImportLocation, expr: TypedHir) {
        self.cache.insert(location, expr);
    }

    pub fn with_cycle_detection(
        &mut self,
        location: ImportLocation,
        do_resolve: impl FnOnce(&mut Self) -> Result<TypedHir, Error>,
    ) -> Result<TypedHir, Error> {
        if self.stack.contains(&location) {
            return Err(
                ImportError::ImportCycle(self.stack.clone(), location).into()
            );
        }
        // Push the current location on the stack
        self.stack.push(location);
        // Resolve the import recursively
        // WARNING: do not propagate errors here or the stack will get messed up.
        let result = do_resolve(self);
        // Remove location from the stack.
        self.stack.pop().unwrap();
        result
    }
}
