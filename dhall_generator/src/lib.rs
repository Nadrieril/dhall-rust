extern crate proc_macro;

mod dhall_expr;
mod dhall_type;

use proc_macro::TokenStream;

// Deprecated
#[proc_macro]
pub fn dhall_expr(input: TokenStream) -> TokenStream {
    subexpr(input)
}

#[proc_macro]
pub fn expr(input: TokenStream) -> TokenStream {
    dhall_expr::expr(input)
}

#[proc_macro]
pub fn subexpr(input: TokenStream) -> TokenStream {
    dhall_expr::subexpr(input)
}

#[proc_macro_derive(StaticType)]
pub fn derive_type(input: TokenStream) -> TokenStream {
    dhall_type::derive_type(input)
}
