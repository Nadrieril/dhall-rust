use dhall_core::{Expr, Import, ImportLocation, ImportMode, FilePrefix, X};


// fn resolve_import(import: Import) -> Expr<X, Import> {

// }

pub fn resolve_imports<'i, S: Clone>(expr: &Expr<'i, S, Import>) -> Expr<'i, S, X> {
    let no_import = |_: &Import| -> X { panic!("ahhh import") };
    expr.map_embed(&no_import)
}
