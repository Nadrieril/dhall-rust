use quote::quote;
use syn::parse::{ParseStream, Result};
use syn::spanned::Spanned;
use syn::{
    parse_quote, Error, Expr, FnArg, Ident, ImplItem, ImplItemMethod, ItemImpl,
    Pat, Token,
};

fn apply_special_attrs(function: &mut ImplItemMethod) -> Result<()> {
    *function = parse_quote!(
        #[allow(non_snake_case, dead_code)]
        #function
    );

    let recognized_attrs: Vec<_> = function
        .attrs
        .drain_filter(|attr| attr.path.is_ident("prec_climb"))
        .collect();

    let name = function.sig.ident.clone();

    if recognized_attrs.is_empty() {
        // do nothing
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

        // Get the name of the first (`input`) function argument
        let first_arg = function.sig.inputs.first().ok_or_else(|| {
            Error::new(
                function.sig.inputs.span(),
                "a prec_climb function needs 4 arguments",
            )
        })?;
        let first_arg = match &first_arg {
            FnArg::Receiver(_) => return Err(Error::new(
                first_arg.span(),
                "a prec_climb function should not have a `self` argument",
            )),
            FnArg::Typed(first_arg) =>   match &*first_arg.pat{
                Pat::Ident(ident) => &ident.ident,
                _ => return Err(Error::new(
                    first_arg.span(),
                    "this argument should be a plain identifier instead of a pattern",
                )),
            }
        };

        function.block = parse_quote!({
            #function

            #climber.climb(
                #first_arg.pair.clone().into_inner(),
                |p| Self::#child_rule(#first_arg.with_pair(p)),
                |l, op, r| {
                    #name(#first_arg.clone(), l?, op, r?)
                },
            )
        });
        // Remove the 3 last arguments to keep only the `input` one
        function.sig.inputs.pop();
        function.sig.inputs.pop();
        function.sig.inputs.pop();
        // Check that an argument remains
        function.sig.inputs.first().ok_or_else(|| {
            Error::new(
                function.sig.inputs.span(),
                "a prec_climb function needs 4 arguments",
            )
        })?;
    }

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
            ImplItem::Method(m) => apply_special_attrs(m),
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
