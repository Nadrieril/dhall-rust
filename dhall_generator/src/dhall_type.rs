extern crate proc_macro;
// use dhall_core::*;
use proc_macro::TokenStream;
use quote::{quote, quote_spanned};
use syn::spanned::Spanned;
use syn::{parse_macro_input, parse_quote, DeriveInput};

pub fn derive_dhall_type(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    // List of types that must impl DhallType
    let mut constraints = vec![];

    let dhall_type = match &input.data {
        syn::Data::Struct(data) => match &data.fields {
            syn::Fields::Named(fields) => {
                let fields = fields.named.iter()
                    .map(|f| {
                        let name = f.ident.as_ref().unwrap().to_string();
                        let ty = &f.ty;
                        constraints.push(ty.clone());
                        quote!( m.insert(dhall_core::Label::from(#name), <#ty as dhall::DhallType>::dhall_type()); )
                    });
                quote! { dhall_core::rc(dhall_core::Expr::RecordType({
                    use std::collections::BTreeMap;
                    let mut m = BTreeMap::new();
                    #(#fields)*
                    m
                })) }
            }
            _ => quote!(dhall_generator::dhall_expr!(Bool)),
        },
        _ => quote!(dhall_generator::dhall_expr!(Bool)),
    };

    let mut generics = input.generics.clone();
    generics.make_where_clause();
    let (impl_generics, ty_generics, orig_where_clause) =
        generics.split_for_impl();
    let orig_where_clause = orig_where_clause.unwrap();

    // Hygienic errors
    let assertions = constraints.iter().enumerate().map(|(i, ty)| {
        // Ensure that ty: DhallType, with an appropriate span
        let assert_name =
            syn::Ident::new(&format!("_AssertDhallType{}", i), ty.span());
        let mut local_where_clause = orig_where_clause.clone();
        local_where_clause
            .predicates
            .push(parse_quote!(#ty: dhall::DhallType));
        let phantoms = generics.params.iter().map(|param| match param {
            syn::GenericParam::Type(syn::TypeParam { ident, .. }) => {
                quote!(#ident)
            }
            syn::GenericParam::Lifetime(syn::LifetimeDef {
                lifetime, ..
            }) => quote!(&#lifetime ()),
            _ => unimplemented!(),
        });
        quote_spanned! {ty.span()=>
            struct #assert_name #impl_generics #local_where_clause {
                _phantom: std::marker::PhantomData<(#(#phantoms),*)>
            };
        }
    });

    // Ensure that all the fields have a DhallType impl
    let mut where_clause = orig_where_clause.clone();
    for ty in constraints.iter() {
        where_clause
            .predicates
            .push(parse_quote!(#ty: dhall::DhallType));
    }

    let ident = &input.ident;
    let tokens = quote! {
        impl #impl_generics dhall::DhallType for #ident #ty_generics #where_clause {
            fn dhall_type() -> dhall_core::DhallExpr {
                #(#assertions)*
                #dhall_type
            }
        }
    };
    TokenStream::from(tokens)
}
