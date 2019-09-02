use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::parse::{Parse, ParseStream, Result};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{
    bracketed, parenthesized, parse_quote, token, Error, Expr, Ident, ImplItem,
    ImplItemMethod, ItemImpl, Pat, ReturnType, Token,
};

#[derive(Debug, Clone)]
struct ChildrenBranch {
    pattern_span: Span,
    pattern: Punctuated<ChildrenBranchPatternItem, Token![,]>,
    body: Expr,
}

#[derive(Debug, Clone)]
enum ChildrenBranchPatternItem {
    Single { rule_name: Ident, binder: Pat },
    Multiple { rule_name: Ident, binder: Ident },
}

#[derive(Debug, Clone)]
struct ParseChildrenInput {
    input_expr: Expr,
    branches: Punctuated<ChildrenBranch, Token![,]>,
}

impl Parse for ChildrenBranch {
    fn parse(input: ParseStream) -> Result<Self> {
        let contents;
        let _: token::Bracket = bracketed!(contents in input);
        let pattern_unparsed: TokenStream = contents.fork().parse()?;
        let pattern_span = pattern_unparsed.span();
        let pattern = Punctuated::parse_terminated(&contents)?;
        let _: Token![=>] = input.parse()?;
        let body = input.parse()?;

        Ok(ChildrenBranch {
            pattern_span,
            pattern,
            body,
        })
    }
}

impl Parse for ChildrenBranchPatternItem {
    fn parse(input: ParseStream) -> Result<Self> {
        let contents;
        let rule_name = input.parse()?;
        parenthesized!(contents in input);
        if input.peek(Token![..]) {
            let binder = contents.parse()?;
            let _: Token![..] = input.parse()?;
            Ok(ChildrenBranchPatternItem::Multiple { rule_name, binder })
        } else if input.is_empty() || input.peek(Token![,]) {
            let binder = contents.parse()?;
            Ok(ChildrenBranchPatternItem::Single { rule_name, binder })
        } else {
            Err(input.error("expected `..` or nothing"))
        }
    }
}

impl Parse for ParseChildrenInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let input_expr = input.parse()?;
        let _: Token![;] = input.parse()?;
        let branches = Punctuated::parse_terminated(input)?;

        Ok(ParseChildrenInput {
            input_expr,
            branches,
        })
    }
}

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

fn make_parser_branch(branch: &ChildrenBranch) -> Result<TokenStream> {
    use ChildrenBranchPatternItem::{Multiple, Single};

    let body = &branch.body;

    // Convert the input pattern into a pattern-match on the Rules of the children. This uses
    // slice_patterns.
    // A single pattern just checks that the rule matches; a variable-length pattern binds the
    // subslice and checks, in the if-guard, that its elements all match the chosen Rule.
    let variable_pattern_ident =
        Ident::new("variable_pattern", Span::call_site());
    let match_pat = branch.pattern.iter().map(|item| match item {
        Single { rule_name, .. } => {
            quote!(<<Self as PestConsumer>::RuleEnum>::#rule_name)
        }
        Multiple { .. } => quote!(#variable_pattern_ident..),
    });
    let match_filter = branch.pattern.iter().map(|item| match item {
        Single { .. } => quote!(),
        Multiple { rule_name, .. } => quote!(
            {
                // We can't use .all() directly in the pattern guard; see
                // https://github.com/rust-lang/rust/issues/59803.
                let all_match = |slice: &[_]| {
                    slice.iter().all(|r|
                        r == &<<Self as PestConsumer>::RuleEnum>::#rule_name
                    )
                };
                all_match(#variable_pattern_ident)
            } &&
        ),
    });

    // Once we have found a branch that matches, we need to parse the children.
    let mut singles_before_multiple = Vec::new();
    let mut multiple = None;
    let mut singles_after_multiple = Vec::new();
    for item in &branch.pattern {
        match item {
            Single {
                rule_name, binder, ..
            } => {
                if multiple.is_none() {
                    singles_before_multiple.push((rule_name, binder))
                } else {
                    singles_after_multiple.push((rule_name, binder))
                }
            }
            Multiple {
                rule_name, binder, ..
            } => {
                if multiple.is_none() {
                    multiple = Some((rule_name, binder))
                } else {
                    return Err(Error::new(
                        branch.pattern_span.clone(),
                        "multiple variable-length patterns are not allowed",
                    ));
                }
            }
        }
    }
    let mut parses = Vec::new();
    for (rule_name, binder) in singles_before_multiple.into_iter() {
        parses.push(quote!(
            let #binder = Self::#rule_name(
                inputs.next().unwrap()
            )?;
        ))
    }
    // Note the `rev()`: we are taking inputs from the end of the iterator in reverse order, so that
    // only the unmatched inputs are left for the variable-length pattern, if any.
    for (rule_name, binder) in singles_after_multiple.into_iter().rev() {
        parses.push(quote!(
            let #binder = Self::#rule_name(
                inputs.next_back().unwrap()
            )?;
        ))
    }
    if let Some((rule_name, binder)) = multiple {
        parses.push(quote!(
            let #binder = inputs
                .map(|i| Self::#rule_name(i))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter();
        ))
    }

    Ok(quote!(
        [#(#match_pat),*] if #(#match_filter)* true => {
            #(#parses)*
            #body
        }
    ))
}

pub fn parse_children(
    input: proc_macro::TokenStream,
) -> Result<proc_macro2::TokenStream> {
    let input: ParseChildrenInput = syn::parse(input)?;

    let input_expr = &input.input_expr;
    let branches = input
        .branches
        .iter()
        .map(make_parser_branch)
        .collect::<Result<Vec<_>>>()?;
    Ok(quote!({
        let children_rules: Vec<_> = #input_expr.pair
            .clone()
            .into_inner()
            .map(|p| p.as_rule())
            .collect();

        #[allow(unused_mut)]
        let mut inputs = #input_expr
            .pair
            .clone()
            .into_inner()
            .map(|p| #input_expr.with_pair(p));

        #[allow(unreachable_code)]
        match children_rules.as_slice() {
            #(#branches,)*
            [..] => return Err(#input_expr.error(
                format!("Unexpected children: {:?}", children_rules)
            )),
        }
    }))
}
