use elsa::vec::FrozenVec;
use once_cell::sync::OnceCell;

use crate::semantics::{Import, ImportLocation};
use crate::syntax::Span;
use crate::Typed;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ImportId(usize);
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ImportResultId(usize);

/// What's stored for each `ImportId`. Allows getting and setting a result for this import.
pub struct StoredImport<'cx> {
    cx: Ctxt<'cx>,
    pub base_location: ImportLocation,
    pub import: Import,
    pub span: Span,
    result: OnceCell<ImportResultId>,
}

/// Implementation detail. Made public for the `Index` instances.
#[derive(Default)]
pub struct CtxtS<'cx> {
    imports: FrozenVec<Box<StoredImport<'cx>>>,
    import_results: FrozenVec<Box<Typed>>,
}

/// Context for the dhall compiler. Stores various global maps.
/// Access the relevant value using `cx[id]`.
#[derive(Copy, Clone)]
pub struct Ctxt<'cx>(&'cx CtxtS<'cx>);

impl Ctxt<'_> {
    pub fn with_new<T>(f: impl for<'cx> FnOnce(Ctxt<'cx>) -> T) -> T {
        let cx = CtxtS::default();
        let cx = Ctxt(&cx);
        f(cx)
    }
}
impl<'cx> Ctxt<'cx> {
    /// Store an import and the location relative to which it must be resolved.
    pub fn push_import(
        self,
        base_location: ImportLocation,
        import: Import,
        span: Span,
    ) -> ImportId {
        let stored = StoredImport {
            cx: self,
            base_location,
            import,
            span,
            result: OnceCell::new(),
        };
        let id = self.0.imports.len();
        self.0.imports.push(Box::new(stored));
        ImportId(id)
    }
    /// Store the result of fetching an import.
    pub fn push_import_result(self, res: Typed) -> ImportResultId {
        let id = self.0.import_results.len();
        self.0.import_results.push(Box::new(res));
        ImportResultId(id)
    }
}

impl<'cx> StoredImport<'cx> {
    /// Get the id of the result of fetching this import. Returns `None` if the result has not yet
    /// been fetched.
    pub fn get_resultid(&self) -> Option<ImportResultId> {
        self.result.get().copied()
    }
    /// Store the result of fetching this import.
    pub fn set_resultid(&self, res: ImportResultId) {
        let _ = self.result.set(res);
    }
    /// Get the result of fetching this import. Returns `None` if the result has not yet been
    /// fetched.
    pub fn get_result(&self) -> Option<&'cx Typed> {
        let res = self.get_resultid()?;
        Some(&self.cx[res])
    }
    /// Store the result of fetching this import.
    pub fn set_result(&self, res: Typed) -> ImportResultId {
        let res = self.cx.push_import_result(res);
        self.set_resultid(res);
        res
    }
}

impl<'cx> std::ops::Deref for Ctxt<'cx> {
    type Target = &'cx CtxtS<'cx>;
    fn deref(&self) -> &&'cx CtxtS<'cx> {
        &self.0
    }
}

impl<'cx> std::ops::Index<ImportId> for CtxtS<'cx> {
    type Output = StoredImport<'cx>;
    fn index(&self, id: ImportId) -> &StoredImport<'cx> {
        &self.imports[id.0]
    }
}
impl<'cx> std::ops::Index<ImportResultId> for CtxtS<'cx> {
    type Output = Typed;
    fn index(&self, id: ImportResultId) -> &Typed {
        &self.import_results[id.0]
    }
}

/// Empty impl, because `FrozenVec` does not implement `Debug` and I can't be bothered to do it
/// myself.
impl<'cx> std::fmt::Debug for Ctxt<'cx> {
    fn fmt(&self, _: &mut std::fmt::Formatter) -> std::fmt::Result {
        Ok(())
    }
}
