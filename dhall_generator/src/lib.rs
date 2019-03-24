extern crate proc_macro;

mod dhall_expr;

#[proc_macro]
pub fn dhall_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    dhall_expr::dhall_expr(input)
}

