extern crate proc_macro;
// use dhall_core::*;
use proc_macro::TokenStream;
use quote::{quote, quote_spanned};
use syn::spanned::Spanned;
use syn::Error;
use syn::{parse_quote, DeriveInput};

pub fn derive_dhall_type(input: TokenStream) -> TokenStream {
    TokenStream::from(match derive_dhall_type_inner(input) {
        Ok(tokens) => tokens,
        Err(err) => err.to_compile_error(),
    })
}

pub fn derive_for_struct(
    data: &syn::DataStruct,
    constraints: &mut Vec<syn::Type>,
) -> Result<proc_macro2::TokenStream, Error> {
    let fields = match &data.fields {
        syn::Fields::Named(fields) => fields
            .named
            .iter()
            .map(|f| {
                let name = f.ident.as_ref().unwrap().to_string();
                let ty = &f.ty;
                (name, ty)
            })
            .collect(),
        syn::Fields::Unnamed(fields) => fields
            .unnamed
            .iter()
            .enumerate()
            .map(|(i, f)| {
                let name = format!("_{}", i + 1);
                let ty = &f.ty;
                (name, ty)
            })
            .collect(),
        syn::Fields::Unit => vec![],
    };
    let fields = fields.into_iter().map(|(name, ty)| {
        constraints.push(ty.clone());
        quote! {
            m.insert(
                dhall_core::Label::from(#name),
                <#ty as dhall::DhallType>::dhall_type()
            );
        }
    });
    Ok(quote! { dhall_core::rc(dhall_core::Expr::RecordType({
        use std::collections::BTreeMap;
        let mut m = BTreeMap::new();
        #(#fields)*
        m
    })) })
}

pub fn derive_for_enum(
    data: &syn::DataEnum,
    constraints: &mut Vec<syn::Type>,
) -> Result<proc_macro2::TokenStream, Error> {
    let variants = data
        .variants
        .iter()
        .map(|v| {
            let name = v.ident.to_string();
            let ty = match &v.fields {
                syn::Fields::Unnamed(fields) if fields.unnamed.is_empty() => {
                    Err(Error::new(
                        v.span(),
                        "Nullary variants are not supported",
                    ))
                }
                syn::Fields::Unnamed(fields) if fields.unnamed.len() > 1 => {
                    Err(Error::new(
                        v.span(),
                        "Variants with more than one field are not supported",
                    ))
                }
                syn::Fields::Unnamed(fields) => {
                    Ok(&fields.unnamed.iter().next().unwrap().ty)
                }
                syn::Fields::Named(_) => Err(Error::new(
                    v.span(),
                    "Named variants are not supported",
                )),
                syn::Fields::Unit => Err(Error::new(
                    v.span(),
                    "Nullary variants are not supported",
                )),
            };
            let ty = ty?;
            constraints.push(ty.clone());
            Ok(quote! {
                m.insert(
                    dhall_core::Label::from(#name),
                    <#ty as dhall::DhallType>::dhall_type()
                );
            })
        })
        .collect::<Result<Vec<_>, Error>>()?;

    Ok(quote! { dhall_core::rc(dhall_core::Expr::UnionType({
        use std::collections::BTreeMap;
        let mut m = BTreeMap::new();
        #(#variants)*
        m
    })) })
}

pub fn derive_dhall_type_inner(
    input: TokenStream,
) -> Result<proc_macro2::TokenStream, Error> {
    let input: DeriveInput = syn::parse_macro_input::parse(input)?;

    // List of types that must impl DhallType
    let mut constraints = vec![];

    let dhall_type = match &input.data {
        syn::Data::Struct(data) => derive_for_struct(data, &mut constraints)?,
        syn::Data::Enum(data) if data.variants.is_empty() => {
            return Err(Error::new(
                input.span(),
                "Empty enums are not supported",
            ))
        }
        syn::Data::Enum(data) => derive_for_enum(data, &mut constraints)?,
        syn::Data::Union(x) => {
            return Err(Error::new(
                x.union_token.span(),
                "Unions are not supported",
            ))
        }
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
        impl #impl_generics dhall::DhallType for #ident #ty_generics
                #where_clause {
            fn dhall_type() -> dhall_core::DhallExpr {
                #(#assertions)*
                #dhall_type
            }
        }
    };
    Ok(tokens)
}
