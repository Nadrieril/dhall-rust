extern crate proc_macro;
// use dhall_core::*;
// use proc_macro2::TokenStream;
use quote::quote;

pub fn derive_dhall_type(_input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    (quote!{
        impl DhallType for A {
            fn dhall_type() -> dhall_core::DhallExpr {
                dhall_core::rc(dhall_core::Expr::BoolLit(false))
            }
        }
    }).into()
}

