use std::collections::HashMap;

use crate::error::{Error, ImportError};
use crate::semantics::{AlphaVar, Import, TypedHir, VarEnv};
use crate::syntax::{Label, V};

/// Environment for resolving names.
#[derive(Debug, Clone)]
pub(crate) struct NameEnv {
    names: Vec<Label>,
}

pub(crate) type ImportCache = HashMap<Import, TypedHir>;
pub(crate) type ImportStack = Vec<Import>;

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
        import: Import,
        mut do_resolve: impl FnMut(&mut Self, &Import) -> Result<TypedHir, Error>,
    ) -> Result<TypedHir, Error> {
        if self.stack.contains(&import) {
            return Err(
                ImportError::ImportCycle(self.stack.clone(), import).into()
            );
        }
        Ok(match self.cache.get(&import) {
            Some(expr) => expr.clone(),
            None => {
                // Push the current import on the stack
                self.stack.push(import.clone());

                // Resolve the import recursively
                let expr = do_resolve(self, &import)?;

                // Remove import from the stack.
                self.stack.pop();

                // Add the import to the cache
                self.cache.insert(import, expr.clone());

                expr
            }
        })
    }
}
