use std::collections::HashMap;

use crate::error::{Error, ImportError};
use crate::semantics::{AlphaVar, ImportLocation, TypedHir, VarEnv};
use crate::syntax::{Label, V};

/// Environment for resolving names.
#[derive(Debug, Clone)]
pub(crate) struct NameEnv {
    names: Vec<Label>,
}

pub(crate) type ImportCache = HashMap<ImportLocation, TypedHir>;
pub(crate) type ImportStack = Vec<ImportLocation>;

/// Environment for resolving imports
#[derive(Debug, Clone)]
pub(crate) struct ImportEnv {
    cache: ImportCache,
    stack: ImportStack,
}

impl NameEnv {
    pub fn new() -> Self {
        NameEnv { names: Vec::new() }
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

impl ImportEnv {
    pub fn new() -> Self {
        ImportEnv {
            cache: HashMap::new(),
            stack: Vec::new(),
        }
    }

    pub fn handle_import(
        &mut self,
        location: ImportLocation,
        do_resolve: impl FnOnce(&mut Self) -> Result<TypedHir, Error>,
    ) -> Result<TypedHir, Error> {
        if self.stack.contains(&location) {
            return Err(
                ImportError::ImportCycle(self.stack.clone(), location).into()
            );
        }
        Ok(match self.cache.get(&location) {
            Some(expr) => expr.clone(),
            None => {
                // Push the current location on the stack
                self.stack.push(location);

                // Resolve the import recursively
                let expr = do_resolve(self)?;

                // Remove location from the stack.
                let location = self.stack.pop().unwrap();

                // Add the resolved import to the cache
                self.cache.insert(location, expr.clone());

                expr
            }
        })
    }
}
