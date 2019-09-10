use std::collections::HashMap;
use std::iter;

use quote::quote;
use syn::parse::{Parse, ParseStream, Result};
use syn::spanned::Spanned;
use syn::{
    parse_quote, Error, Expr, FnArg, Ident, ImplItem, ImplItemMethod, ItemImpl,
    LitBool, Pat, Path, Token,
};

/// Ext. trait adding `partition_filter` to `Vec`. Would like to use `Vec::drain_filter`
/// but it's unstable for now.
pub trait VecPartitionFilterExt<Item> {
    fn partition_filter<F>(&mut self, predicate: F) -> Vec<Item>
    where
        F: FnMut(&mut Item) -> bool;
}

impl<Item> VecPartitionFilterExt<Item> for Vec<Item> {
    fn partition_filter<F>(&mut self, mut predicate: F) -> Vec<Item>
    where
        F: FnMut(&mut Item) -> bool,
    {
        let mut ret = Vec::new();
        let mut i = 0;
        while i != self.len() {
            if predicate(&mut self[i]) {
                ret.push(self.remove(i))
            } else {
                i += 1;
            }
        }
        ret
    }
}

mod kw {
    syn::custom_keyword!(shortcut);
}

struct MakeParserAttrs {
    parser: Path,
    rule_enum: Path,
}

struct AliasArgs {
    target: Ident,
    is_shortcut: bool,
}

struct PrecClimbArgs {
    child_rule: Ident,
    climber: Expr,
}

struct AliasSrc {
    ident: Ident,
    is_shortcut: bool,
}

struct ParsedFn<'a> {
    // Body of the function
    function: &'a mut ImplItemMethod,
    // Name of the function.
    fn_name: Ident,
    // Name of the first argument of the function, which should be of type `ParseInput`.
    input_arg: Ident,
    // List of aliases pointing to this function
    alias_srcs: Vec<AliasSrc>,
}

impl Parse for MakeParserAttrs {
    fn parse(input: ParseStream) -> Result<Self> {
        let parser = input.parse()?;
        let _: Token![,] = input.parse()?;
        let rule_enum = input.parse()?;
        Ok(MakeParserAttrs { parser, rule_enum })
    }
}

impl Parse for AliasArgs {
    fn parse(input: ParseStream) -> Result<Self> {
        let target = input.parse()?;
        let is_shortcut = if input.peek(Token![,]) {
            // #[alias(rule, shortcut = true)]
            let _: Token![,] = input.parse()?;
            let _: kw::shortcut = input.parse()?;
            let _: Token![=] = input.parse()?;
            let b: LitBool = input.parse()?;
            b.value
        } else {
            // #[alias(rule)]
            false
        };
        Ok(AliasArgs {
            target,
            is_shortcut,
        })
    }
}

impl Parse for PrecClimbArgs {
    fn parse(input: ParseStream) -> Result<Self> {
        let child_rule = input.parse()?;
        let _: Token![,] = input.parse()?;
        let climber = input.parse()?;
        Ok(PrecClimbArgs {
            child_rule,
            climber,
        })
    }
}

fn collect_aliases(
    imp: &mut ItemImpl,
) -> Result<HashMap<Ident, Vec<AliasSrc>>> {
    let functions = imp.items.iter_mut().flat_map(|item| match item {
        ImplItem::Method(m) => Some(m),
        _ => None,
    });

    let mut alias_map = HashMap::new();
    for function in functions {
        let fn_name = function.sig.ident.clone();
        let mut alias_attrs = function
            .attrs
            .partition_filter(|attr| attr.path.is_ident("alias"))
            .into_iter();

        if let Some(attr) = alias_attrs.next() {
            let args: AliasArgs = attr.parse_args()?;
            alias_map.entry(args.target).or_insert_with(Vec::new).push(
                AliasSrc {
                    ident: fn_name,
                    is_shortcut: args.is_shortcut,
                },
            );
        }
        if let Some(attr) = alias_attrs.next() {
            return Err(Error::new(
                attr.span(),
                "expected at most one alias attribute",
            ));
        }
    }

    Ok(alias_map)
}

fn parse_fn<'a>(
    function: &'a mut ImplItemMethod,
    alias_map: &mut HashMap<Ident, Vec<AliasSrc>>,
) -> Result<ParsedFn<'a>> {
    let fn_name = function.sig.ident.clone();
    // Get the name of the first (`input`) function argument
    let input_arg = function.sig.inputs.first().ok_or_else(|| {
        Error::new(
            function.sig.inputs.span(),
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

    let alias_srcs = alias_map.remove(&fn_name).unwrap_or_else(Vec::new);

    Ok(ParsedFn {
        function,
        fn_name,
        input_arg,
        alias_srcs,
    })
}

fn apply_special_attrs(f: &mut ParsedFn, rule_enum: &Path) -> Result<()> {
    let function = &mut *f.function;
    let fn_name = &f.fn_name;
    let input_arg = &f.input_arg;

    *function = parse_quote!(
        #[allow(non_snake_case)]
        #function
    );

    // `prec_climb` attr
    let prec_climb_attrs: Vec<_> = function
        .attrs
        .partition_filter(|attr| attr.path.is_ident("prec_climb"));

    if prec_climb_attrs.len() > 1 {
        return Err(Error::new(
            prec_climb_attrs[1].span(),
            "expected at most one prec_climb attribute",
        ));
    } else if prec_climb_attrs.is_empty() {
        // do nothing
    } else {
        let attr = prec_climb_attrs.into_iter().next().unwrap();
        let PrecClimbArgs {
            child_rule,
            climber,
        } = attr.parse_args()?;

        function.block = parse_quote!({
            #function

            #climber.climb(
                #input_arg.as_pair().clone().into_inner(),
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
    if !f.alias_srcs.is_empty() {
        let aliases = f.alias_srcs.iter().map(|src| &src.ident);
        let block = &function.block;
        function.block = parse_quote!({
            let mut #input_arg = #input_arg;
            // While the current rule allows shortcutting, and there is a single child, and the
            // child can still be parsed by the current function, then skip to that child.
            while <Self as pest_consume::PestConsumer>::allows_shortcut(#input_arg.as_rule()) {
                if let Some(child) = #input_arg.single_child() {
                    if &<Self as pest_consume::PestConsumer>::rule_alias(child.as_rule())
                            == stringify!(#fn_name) {
                        #input_arg = child;
                        continue;
                    }
                }
                break
            }

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
    let attrs: MakeParserAttrs = syn::parse(attrs)?;
    let parser = &attrs.parser;
    let rule_enum = &attrs.rule_enum;
    let mut imp: ItemImpl = syn::parse(input)?;

    let mut alias_map = collect_aliases(&mut imp)?;
    let rule_alias_branches: Vec<_> = alias_map
        .iter()
        .flat_map(|(tgt, srcs)| iter::repeat(tgt).zip(srcs))
        .map(|(tgt, src)| {
            let ident = &src.ident;
            quote!(
                #rule_enum::#ident => stringify!(#tgt).to_string(),
            )
        })
        .collect();
    let shortcut_branches: Vec<_> = alias_map
        .iter()
        .flat_map(|(_tgt, srcs)| srcs)
        .map(|AliasSrc { ident, is_shortcut }| {
            quote!(
                #rule_enum::#ident => #is_shortcut,
            )
        })
        .collect();

    let fn_map: HashMap<Ident, ParsedFn> = imp
        .items
        .iter_mut()
        .flat_map(|item| match item {
            ImplItem::Method(m) => Some(m),
            _ => None,
        })
        .map(|method| {
            let mut f = parse_fn(method, &mut alias_map)?;
            apply_special_attrs(&mut f, &rule_enum)?;
            Ok((f.fn_name.clone(), f))
        })
        .collect::<Result<_>>()?;

    // Entries that remain in the alias map don't have a matching method, so we create one.
    let extra_fns: Vec<_> = alias_map
        .iter()
        .map(|(tgt, srcs)| {
            // Get the signature of one of the functions that has this alias. They should all have
            // essentially the same signature anyways.
            let f = fn_map.get(&srcs.first().unwrap().ident).unwrap();
            let input_arg = f.input_arg.clone();
            let mut sig = f.function.sig.clone();
            sig.ident = tgt.clone();
            let srcs = srcs.iter().map(|src| &src.ident);

            Ok(parse_quote!(
                #sig {
                    match #input_arg.as_rule() {
                        #(#rule_enum::#srcs => Self::#srcs(#input_arg),)*
                        // We can't match on #rule_enum::#tgt since `tgt` might be an arbitrary
                        // identifier.
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
            ))
        })
        .collect::<Result<_>>()?;
    imp.items.extend(extra_fns);

    let ty = &imp.self_ty;
    let (impl_generics, _, where_clause) = imp.generics.split_for_impl();
    Ok(quote!(
        impl #impl_generics pest_consume::PestConsumer for #ty #where_clause {
            type Rule = #rule_enum;
            type Parser = #parser;
            fn rule_alias(rule: Self::Rule) -> String {
                match rule {
                    #(#rule_alias_branches)*
                    r => format!("{:?}", r),
                }
            }
            fn allows_shortcut(rule: Self::Rule) -> bool {
                match rule {
                    #(#shortcut_branches)*
                    _ => false,
                }
            }
        }

        #imp
    ))
}
