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
    parser: Type,
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
        let parser = if input.peek(token::Lt) {
            let _: token::Lt = input.parse()?;
            let parser = input.parse()?;
            let _: token::Gt = input.parse()?;
            let _: Token![;] = input.parse()?;
            parser
        } else {
            parse_quote!(Self)
        };
        let input_expr = input.parse()?;
        let _: Token![;] = input.parse()?;
        let branches = Punctuated::parse_terminated(input)?;

        Ok(ParseChildrenInput {
            parser,
            input_expr,
            branches,
        })
    }
}

fn make_parser_branch(
    branch: &ChildrenBranch,
    i_inputs: &Ident,
    i_input_rules: &Ident,
    parser: &Type,
) -> Result<TokenStream> {
    use ChildrenBranchPatternItem::{Multiple, Single};

    let body = &branch.body;
    let aliased_rule = quote!(<#parser as ::pest_consume::Parser>::AliasedRule);

    // Patterns all have the form [a, b, c.., d], with a bunch of simple patterns,
    // optionally a multiple pattern, and then some more simple patterns.
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

    // Find which branch to take
    let mut conditions = Vec::new();
    let start = singles_before_multiple.len();
    let end = singles_after_multiple.len();
    conditions.push(quote!(
        #start + #end <= #i_input_rules.len()
    ));
    for (i, (rule_name, _)) in singles_before_multiple.iter().enumerate() {
        conditions.push(quote!(
            #i_input_rules[#i] == #aliased_rule::#rule_name
        ))
    }
    for (i, (rule_name, _)) in singles_after_multiple.iter().enumerate() {
        conditions.push(quote!(
            #i_input_rules[#i_input_rules.len()-1 - #i] == #aliased_rule::#rule_name
        ))
    }
    if let Some((rule_name, _)) = multiple {
        conditions.push(quote!(
            {
                // We can't use .all() directly in the pattern guard; see
                // https://github.com/rust-lang/rust/issues/59803.
                let all_match = |slice: &[_]| {
                    slice.iter().all(|r|
                        *r == #aliased_rule::#rule_name
                    )
                };
                all_match(&#i_input_rules[#start..#i_input_rules.len() - #end])
            }
        ))
    } else {
        // No variable-length pattern, so the size must be exactly the number of patterns
        conditions.push(quote!(
            #start + #end == #i_input_rules.len()
        ))
    }

    // Once we have found a branch that matches, we need to parse the children.
    let mut parses = Vec::new();
    for (rule_name, binder) in singles_before_multiple.into_iter() {
        parses.push(quote!(
            let #binder = #parser::#rule_name(
                #i_inputs.next().unwrap()
            )?;
        ))
    }
    // Note the `rev()`: we are taking inputs from the end of the iterator in reverse order, so that
    // only the unmatched inputs are left in the iterator for the variable-length pattern, if any.
    for (rule_name, binder) in singles_after_multiple.into_iter().rev() {
        parses.push(quote!(
            let #binder = #parser::#rule_name(
                #i_inputs.next_back().unwrap()
            )?;
        ))
    }
    if let Some((rule_name, binder)) = multiple {
        parses.push(quote!(
            let #binder = #i_inputs
                .map(|i| #parser::#rule_name(i))
                .collect::<::std::result::Result<::std::vec::Vec<_>, _>>()?
                .into_iter();
        ))
    }

    Ok(quote!(
        _ if #(#conditions &&)* true => {
            #(#parses)*
            #body
        }
    ))
}

pub fn match_nodes(
    input: proc_macro::TokenStream,
) -> Result<proc_macro2::TokenStream> {
    let input: ParseChildrenInput = syn::parse(input)?;

    let i_input_rules = Ident::new("___input_rules", Span::call_site());
    let i_inputs = Ident::new("___inputs", Span::call_site());

    let input_expr = &input.input_expr;
    let parser = &input.parser;
    let branches = input
        .branches
        .iter()
        .map(|br| make_parser_branch(br, &i_inputs, &i_input_rules, parser))
        .collect::<Result<Vec<_>>>()?;

    Ok(quote!({
        #[allow(unused_mut)]
        let mut #i_inputs = #input_expr;
        let #i_input_rules = #i_inputs.aliased_rules::<#parser>();

        #[allow(unreachable_code)]
        match () {
            #(#branches,)*
            _ => return ::std::result::Result::Err(#i_inputs.error(
                std::format!("Unexpected children: {:?}", #i_input_rules)
            )),
        }
    }))
}
