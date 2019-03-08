// use dhall_core::{Expr, FilePrefix, Import, ImportLocation, ImportMode, X};
use dhall_core::{Expr, StringLike, Import, X};
// use std::path::Path;
// use std::path::PathBuf;

pub fn resolve_imports<Label: StringLike, S: Clone>(
    expr: &Expr<Label, S, Import>,
) -> Expr<Label, S, X> {
    let no_import = |_: &Import| -> X { panic!("ahhh import") };
    expr.map_embed(&no_import)
}
