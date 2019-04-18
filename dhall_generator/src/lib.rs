//! This crate contains the code-generation primitives for the [dhall-rust][dhall-rust] crate.
//! This is highly unstable and breaks regularly; use at your own risk.
//!
//! [dhall-rust]: https://github.com/Nadrieril/dhall-rust

extern crate proc_macro;

mod derive;
mod quote;

use proc_macro::TokenStream;

#[proc_macro]
pub fn expr(input: TokenStream) -> TokenStream {
    quote::expr(input)
}

#[proc_macro]
pub fn subexpr(input: TokenStream) -> TokenStream {
    quote::subexpr(input)
}

#[proc_macro_derive(SimpleStaticType)]
pub fn derive_simple_static_type(input: TokenStream) -> TokenStream {
    derive::derive_simple_static_type(input)
}
