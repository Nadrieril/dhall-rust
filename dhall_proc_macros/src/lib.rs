//! This crate contains the code-generation primitives for the [dhall-rust][dhall-rust] crate.
//! This is highly unstable and breaks regularly; use at your own risk.
//!
//! [dhall-rust]: https://github.com/Nadrieril/dhall-rust

extern crate proc_macro;

mod derive;
mod parser;

use proc_macro::TokenStream;

#[proc_macro_derive(StaticType)]
pub fn derive_static_type(input: TokenStream) -> TokenStream {
    derive::derive_static_type(input)
}

#[proc_macro]
pub fn make_parser(input: TokenStream) -> TokenStream {
    TokenStream::from(match parser::make_parser(input) {
        Ok(tokens) => tokens,
        Err(err) => err.to_compile_error(),
    })
}
