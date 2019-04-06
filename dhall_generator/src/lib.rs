extern crate proc_macro;

mod derive;
mod quote;

use proc_macro::TokenStream;

// Deprecated
#[proc_macro]
pub fn dhall_expr(input: TokenStream) -> TokenStream {
    subexpr(input)
}

#[proc_macro]
pub fn expr(input: TokenStream) -> TokenStream {
    quote::expr(input)
}

#[proc_macro]
pub fn subexpr(input: TokenStream) -> TokenStream {
    quote::subexpr(input)
}

#[proc_macro_derive(StaticType)]
pub fn derive_type(input: TokenStream) -> TokenStream {
    derive::derive_type(input)
}
