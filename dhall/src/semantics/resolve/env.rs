use std::collections::HashMap;

use crate::error::{Error, ImportError};
use crate::semantics::{AlphaVar, Cache, ImportLocation, VarEnv};
use crate::syntax::{Hash, Label, V};
use crate::{Ctxt, ImportResultId, Typed};

/// Environment for resolving names.
#[derive(Debug, Clone, Default)]
pub struct NameEnv {
    names: Vec<Label>,
}

pub type CyclesStack = Vec<ImportLocation>;

/// Environment for resolving imports
pub struct ImportEnv<'cx> {
    cx: Ctxt<'cx>,
    disk_cache: Option<Cache>, // `None` if it failed to initialize
    mem_cache: HashMap<ImportLocation, ImportResultId>,
    stack: CyclesStack,
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

impl<'cx> ImportEnv<'cx> {
    pub fn new(cx: Ctxt<'cx>) -> Self {
        ImportEnv {
            cx,
            disk_cache: Cache::new().ok(),
            mem_cache: Default::default(),
            stack: Default::default(),
        }
    }

    pub fn cx(&self) -> Ctxt<'cx> {
        self.cx
    }

    pub fn get_from_mem_cache(
        &self,
        location: &ImportLocation,
    ) -> Option<ImportResultId> {
        Some(*self.mem_cache.get(location)?)
    }

    pub fn get_from_disk_cache(&self, hash: &Option<Hash>) -> Option<Typed> {
        let hash = hash.as_ref()?;
        let expr = self.disk_cache.as_ref()?.get(hash).ok()?;
        Some(expr)
    }

    pub fn write_to_mem_cache(
        &mut self,
        location: ImportLocation,
        result: ImportResultId,
    ) {
        self.mem_cache.insert(location, result);
    }

    pub fn write_to_disk_cache(&self, hash: &Option<Hash>, expr: &Typed) {
        if let Some(disk_cache) = self.disk_cache.as_ref() {
            if let Some(hash) = hash {
                let _ = disk_cache.insert(hash, &expr);
            }
        }
    }

    pub fn with_cycle_detection(
        &mut self,
        location: ImportLocation,
        do_resolve: impl FnOnce(&mut Self) -> Result<Typed, Error>,
    ) -> Result<Typed, Error> {
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
