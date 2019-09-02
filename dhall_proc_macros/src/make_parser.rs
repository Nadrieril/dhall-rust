use quote::quote;
use syn::parse::{ParseStream, Result};
use syn::spanned::Spanned;
use syn::{
    parse_quote, Error, Expr, Ident, ImplItem, ImplItemMethod, ItemImpl,
    ReturnType, Token,
};

fn apply_special_attrs(
    rule_enum: &Ident,
    function: &mut ImplItemMethod,
) -> Result<()> {
    let recognized_attrs: Vec<_> = function
        .attrs
        .drain_filter(|attr| attr.path.is_ident("prec_climb"))
        .collect();

    let name = function.sig.ident.clone();
    let output_type = match &function.sig.output {
        ReturnType::Default => parse_quote!(()),
        ReturnType::Type(_, t) => (**t).clone(),
    };

    if recognized_attrs.is_empty() {
    } else if recognized_attrs.len() > 1 {
        return Err(Error::new(
            recognized_attrs[1].span(),
            "expected a single prec_climb attribute",
        ));
    } else {
        let attr = recognized_attrs.into_iter().next().unwrap();
        let (child_rule, climber) =
            attr.parse_args_with(|input: ParseStream| {
                let child_rule: Ident = input.parse()?;
                let _: Token![,] = input.parse()?;
                let climber: Expr = input.parse()?;
                Ok((child_rule, climber))
            })?;

        *function = parse_quote!(
            fn #name<'a>(
                input: ParseInput<'a, #rule_enum>,
            ) -> #output_type {
                #[allow(non_snake_case, dead_code)]
                #function

                #climber.climb(
                    input.pair.clone().into_inner(),
                    |p| Self::#child_rule(input.with_pair(p)),
                    |l, op, r| {
                        #name(input.clone(), l?, op, r?)
                    },
                )
            }
        );
    }

    *function = parse_quote!(
        #[allow(non_snake_case, dead_code)]
        #function
    );

    Ok(())
}

pub fn make_parser(
    attrs: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> Result<proc_macro2::TokenStream> {
    let rule_enum: Ident = syn::parse(attrs)?;

    let mut imp: ItemImpl = syn::parse(input)?;
    imp.items
        .iter_mut()
        .map(|item| match item {
            ImplItem::Method(m) => apply_special_attrs(&rule_enum, m),
            _ => Ok(()),
        })
        .collect::<Result<()>>()?;

    let ty = &imp.self_ty;
    let (impl_generics, _, where_clause) = imp.generics.split_for_impl();
    Ok(quote!(
        impl #impl_generics PestConsumer for #ty #where_clause {
            type RuleEnum = #rule_enum;
        }

        #imp
    ))
}
