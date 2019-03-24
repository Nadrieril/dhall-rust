extern crate proc_macro;

mod dhall_expr;
mod dhall_type;

use proc_macro::TokenStream;

#[proc_macro]
pub fn dhall_expr(input: TokenStream) -> TokenStream {
    dhall_expr::dhall_expr(input)
}

#[proc_macro_derive(DhallType)]
pub fn derive_dhall_type(input: TokenStream) -> TokenStream {
    dhall_type::derive_dhall_type(input)
}
