use elsa::vec::FrozenVec;
use once_cell::sync::OnceCell;

use crate::semantics::{Import, ImportLocation};
use crate::syntax::Span;
use crate::Typed;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ImportId(usize);
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ImportResultId(usize);

struct StoredImport {
    base_location: ImportLocation,
    import: Import,
    span: Span,
    result: OnceCell<ImportResultId>,
}

#[derive(Default)]
struct CtxtS {
    imports: FrozenVec<Box<StoredImport>>,
    import_results: FrozenVec<Box<Typed>>,
}

/// Context for the dhall compiler. Stores various global maps.
#[derive(Copy, Clone)]
pub struct Ctxt<'cx>(&'cx CtxtS);

impl Ctxt<'_> {
    pub fn with_new<T>(f: impl for<'cx> FnOnce(Ctxt<'cx>) -> T) -> T {
        let cx = CtxtS::default();
        let cx = Ctxt(&cx);
        f(cx)
    }
}
impl<'cx> Ctxt<'cx> {
    fn get_stored_import(self, import: ImportId) -> &'cx StoredImport {
        self.0.imports.get(import.0).unwrap()
    }
    pub fn get_import_result(self, id: ImportResultId) -> &'cx Typed {
        &self.0.import_results.get(id.0).unwrap()
    }

    /// Store an import and the location relative to which it must be resolved.
    pub fn push_import(
        self,
        base_location: ImportLocation,
        import: Import,
        span: Span,
    ) -> ImportId {
        let stored = StoredImport {
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

    pub fn get_import(self, import: ImportId) -> &'cx Import {
        &self.get_stored_import(import).import
    }
    pub fn get_import_base_location(
        self,
        import: ImportId,
    ) -> &'cx ImportLocation {
        &self.get_stored_import(import).base_location
    }
    pub fn get_import_span(self, import: ImportId) -> Span {
        self.get_stored_import(import).span.clone()
    }
    /// Get the result of fetching this import. Returns `None` if the result has not yet been
    /// fetched.
    pub fn get_result_of_import(self, import: ImportId) -> Option<&'cx Typed> {
        let res = self.get_resultid_of_import(import)?;
        Some(self.get_import_result(res))
    }
    /// Get the id of the result of fetching this import. Returns `None` if the result has not yet
    /// been fetched.
    pub fn get_resultid_of_import(
        self,
        import: ImportId,
    ) -> Option<ImportResultId> {
        self.get_stored_import(import).result.get().copied()
    }
    /// Store the result of fetching this import.
    pub fn set_result_of_import(
        self,
        import: ImportId,
        res: Typed,
    ) -> ImportResultId {
        let res = self.push_import_result(res);
        self.set_resultid_of_import(import, res);
        res
    }
    /// Store the result of fetching this import.
    pub fn set_resultid_of_import(self, import: ImportId, res: ImportResultId) {
        let _ = self.get_stored_import(import).result.set(res);
    }
}
