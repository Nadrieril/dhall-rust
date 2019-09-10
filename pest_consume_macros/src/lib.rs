//! This crate contains the code-generation primitives for the [dhall-rust][dhall-rust] crate.
//! This is highly unstable and breaks regularly; use at your own risk.
//!
//! [dhall-rust]: https://github.com/Nadrieril/dhall-rust

extern crate proc_macro;

mod make_parser;
mod match_inputs;

use proc_macro::TokenStream;

#[proc_macro_attribute]
pub fn make_parser(attrs: TokenStream, input: TokenStream) -> TokenStream {
    TokenStream::from(match make_parser::make_parser(attrs, input) {
        Ok(tokens) => tokens,
        Err(err) => err.to_compile_error(),
    })
}

#[proc_macro_hack::proc_macro_hack]
pub fn match_inputs(input: TokenStream) -> TokenStream {
    TokenStream::from(match match_inputs::match_inputs(input) {
        Ok(tokens) => tokens,
        Err(err) => err.to_compile_error(),
    })
}
