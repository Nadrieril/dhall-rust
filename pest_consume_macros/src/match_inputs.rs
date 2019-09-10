use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::parse::{Parse, ParseStream, Result};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{
    bracketed, parenthesized, parse_quote, token, Error, Expr, Ident, Pat,
    Token, Type,
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
    consumer: Type,
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
        let consumer = if input.peek(token::Lt) {
            let _: token::Lt = input.parse()?;
            let consumer = input.parse()?;
            let _: token::Gt = input.parse()?;
            let _: Token![;] = input.parse()?;
            consumer
        } else {
            parse_quote!(Self)
        };
        let input_expr = input.parse()?;
        let _: Token![;] = input.parse()?;
        let branches = Punctuated::parse_terminated(input)?;

        Ok(ParseChildrenInput {
            consumer,
            input_expr,
            branches,
        })
    }
}

fn make_parser_branch(
    branch: &ChildrenBranch,
    i_inputs: &Ident,
    consumer: &Type,
) -> Result<TokenStream> {
    use ChildrenBranchPatternItem::{Multiple, Single};

    let body = &branch.body;

    // Convert the input pattern into a pattern-match on the Rules of the children. This uses
    // slice_patterns.
    // A single pattern just checks that the rule matches; a variable-length pattern binds the
    // subslice and checks, in the if-guard, that its elements all match the chosen Rule.
    let i_variable_pattern =
        Ident::new("___variable_pattern", Span::call_site());
    let match_pat = branch.pattern.iter().map(|item| match item {
        Single { rule_name, .. } => quote!(stringify!(#rule_name)),
        Multiple { .. } => quote!(#i_variable_pattern @ ..),
    });
    let match_filter = branch.pattern.iter().map(|item| match item {
        Single { .. } => quote!(),
        Multiple { rule_name, .. } => quote!(
            {
                // We can't use .all() directly in the pattern guard; see
                // https://github.com/rust-lang/rust/issues/59803.
                let all_match = |slice: &[_]| {
                    slice.iter().all(|r|
                        *r == stringify!(#rule_name)
                    )
                };
                all_match(#i_variable_pattern)
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
            let #binder = #consumer::#rule_name(
                #i_inputs.next().unwrap()
            )?;
        ))
    }
    // Note the `rev()`: we are taking inputs from the end of the iterator in reverse order, so that
    // only the unmatched inputs are left for the variable-length pattern, if any.
    for (rule_name, binder) in singles_after_multiple.into_iter().rev() {
        parses.push(quote!(
            let #binder = #consumer::#rule_name(
                #i_inputs.next_back().unwrap()
            )?;
        ))
    }
    if let Some((rule_name, binder)) = multiple {
        parses.push(quote!(
            let #binder = #i_inputs
                .map(|i| #consumer::#rule_name(i))
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

pub fn match_inputs(
    input: proc_macro::TokenStream,
) -> Result<proc_macro2::TokenStream> {
    let input: ParseChildrenInput = syn::parse(input)?;

    let i_input_rules = Ident::new("___input_rules", Span::call_site());
    let i_inputs = Ident::new("___inputs", Span::call_site());

    let input_expr = &input.input_expr;
    let consumer = &input.consumer;
    let branches = input
        .branches
        .iter()
        .map(|br| make_parser_branch(br, &i_inputs, consumer))
        .collect::<Result<Vec<_>>>()?;

    Ok(quote!({
        #[allow(unused_mut)]
        let mut #i_inputs = #input_expr;

        let #i_input_rules = #i_inputs.aliased_rules::<#consumer>();
        let #i_input_rules: Vec<&str> = #i_input_rules
            .iter()
            .map(String::as_str)
            .collect();

        #[allow(unreachable_code)]
        match #i_input_rules.as_slice() {
            #(#branches,)*
            [..] => return Err(#i_inputs.error(
                format!("Unexpected children: {:?}", #i_input_rules)
            )),
        }
    }))
}
