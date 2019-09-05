use std::collections::HashMap;
use std::iter;

use quote::quote;
use syn::parse::{ParseStream, Result};
use syn::spanned::Spanned;
use syn::{
    parse_quote, Error, Expr, FnArg, Ident, ImplItem, ImplItemMethod, ItemImpl,
    Pat, Signature, Token,
};

fn collect_aliases(
    imp: &mut ItemImpl,
) -> Result<HashMap<Ident, (Signature, Vec<Ident>)>> {
    let mut alias_map = HashMap::new();

    for item in &mut imp.items {
        if let ImplItem::Method(function) = item {
            let fn_name = function.sig.ident.clone();
            let mut alias_attrs = function
                .attrs
                .drain_filter(|attr| attr.path.is_ident("alias"))
                .collect::<Vec<_>>()
                .into_iter();

            if let Some(attr) = alias_attrs.next() {
                let tgt: Ident = attr.parse_args()?;
                alias_map
                    .entry(tgt)
                    .or_insert_with(|| (function.sig.clone(), Vec::new()))
                    .1
                    .push(fn_name);
            }
            if let Some(attr) = alias_attrs.next() {
                return Err(Error::new(
                    attr.span(),
                    "expected at most one alias attribute",
                ));
            }
        }
    }

    Ok(alias_map)
}

fn parse_rulefn_sig(sig: &Signature) -> Result<(Ident, Ident)> {
    let fn_name = sig.ident.clone();
    // Get the name of the first (`input`) function argument
    let input_arg = sig.inputs.first().ok_or_else(|| {
        Error::new(
            sig.inputs.span(),
            "a rule function needs an `input` argument",
        )
    })?;
    let input_arg = match &input_arg {
        FnArg::Receiver(_) => return Err(Error::new(
            input_arg.span(),
            "a rule function should not have a `self` argument",
        )),
        FnArg::Typed(input_arg) => match &*input_arg.pat{
            Pat::Ident(ident) => ident.ident.clone(),
            _ => return Err(Error::new(
                input_arg.span(),
                "this argument should be a plain identifier instead of a pattern",
            )),
        }
    };

    Ok((fn_name, input_arg))
}

fn apply_special_attrs(
    function: &mut ImplItemMethod,
    alias_map: &mut HashMap<Ident, (Signature, Vec<Ident>)>,
    rule_enum: &Ident,
) -> Result<()> {
    *function = parse_quote!(
        #[allow(non_snake_case, dead_code)]
        #function
    );

    let (fn_name, input_arg) = parse_rulefn_sig(&function.sig)?;

    // `prec_climb` attr
    let prec_climb_attrs: Vec<_> = function
        .attrs
        .drain_filter(|attr| attr.path.is_ident("prec_climb"))
        .collect();

    if prec_climb_attrs.len() > 1 {
        return Err(Error::new(
            prec_climb_attrs[1].span(),
            "expected at most one prec_climb attribute",
        ));
    } else if prec_climb_attrs.is_empty() {
        // do nothing
    } else {
        let attr = prec_climb_attrs.into_iter().next().unwrap();
        let (child_rule, climber) =
            attr.parse_args_with(|input: ParseStream| {
                let child_rule: Ident = input.parse()?;
                let _: Token![,] = input.parse()?;
                let climber: Expr = input.parse()?;
                Ok((child_rule, climber))
            })?;

        function.block = parse_quote!({
            #function

            #climber.climb(
                #input_arg.pair.clone().into_inner(),
                |p| Self::#child_rule(#input_arg.with_pair(p)),
                |l, op, r| {
                    #fn_name(#input_arg.clone(), l?, op, r?)
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

    // `alias` attr
    if let Some((_, aliases)) = alias_map.remove(&fn_name) {
        let block = &function.block;
        function.block = parse_quote!({
            match #input_arg.as_rule() {
                #(#rule_enum::#aliases => Self::#aliases(#input_arg),)*
                #rule_enum::#fn_name => #block,
                r => unreachable!(
                    "make_parser: called {} on {:?}",
                    stringify!(#fn_name),
                    r
                )
            }
        });
    }

    Ok(())
}

pub fn make_parser(
    attrs: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> Result<proc_macro2::TokenStream> {
    let rule_enum: Ident = syn::parse(attrs)?;
    let mut imp: ItemImpl = syn::parse(input)?;

    let mut alias_map = collect_aliases(&mut imp)?;
    let rule_alias_branches: Vec<_> = alias_map
        .iter()
        .flat_map(|(tgt, (_, srcs))| iter::repeat(tgt).zip(srcs))
        .map(|(tgt, src)| {
            quote!(
                #rule_enum::#src => stringify!(#tgt).to_string(),
            )
        })
        .collect();

    imp.items
        .iter_mut()
        .map(|item| match item {
            ImplItem::Method(m) => {
                apply_special_attrs(m, &mut alias_map, &rule_enum)
            }
            _ => Ok(()),
        })
        .collect::<Result<()>>()?;

    // Entries that remain in the alias map don't have a matching method, so we create one.
    let extra_fns: Vec<_> = alias_map
        .iter()
        .map(|(tgt, (sig, srcs))| {
            let mut sig = sig.clone();
            sig.ident = tgt.clone();

            let (_, input_arg) = parse_rulefn_sig(&sig)?;
            Ok(ImplItem::Method(parse_quote!(
                #sig {
                    match #input_arg.as_rule() {
                        #(#rule_enum::#srcs => Self::#srcs(#input_arg),)*
                        r if &format!("{:?}", r) == stringify!(#tgt) =>
                            return Err(#input_arg.error(format!(
                                "make_parser: missing method for rule {}",
                                stringify!(#tgt),
                            ))),
                        r => unreachable!(
                            "make_parser: called {} on {:?}",
                            stringify!(#tgt),
                            r
                        )
                    }
                }
            )))
        })
        .collect::<Result<_>>()?;
    imp.items.extend(extra_fns);

    let ty = &imp.self_ty;
    let (impl_generics, _, where_clause) = imp.generics.split_for_impl();
    Ok(quote!(
        impl #impl_generics PestConsumer for #ty #where_clause {
            type Rule = #rule_enum;
            fn rule_alias(rule: Self::Rule) -> String {
                match rule {
                    #(#rule_alias_branches)*
                    r => format!("{:?}", r),
                }
            }
        }

        #imp
    ))
}
