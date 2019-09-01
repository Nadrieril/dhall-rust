use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::parse::{Parse, ParseStream, Result};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{
    bracketed, parenthesized, parse_quote, token, Error, Expr, Ident, ItemFn,
    Pat, ReturnType, Token, Type,
};

mod rule_kw {
    syn::custom_keyword!(rule);
    syn::custom_keyword!(captured_str);
    syn::custom_keyword!(children);
    syn::custom_keyword!(prec_climb);
}

#[derive(Debug, Clone)]
struct Rules(Vec<Rule>);

#[derive(Debug, Clone)]
struct Rule {
    name: Ident,
    output_type: Type,
    contents: RuleContents,
}

#[derive(Debug, Clone)]
enum RuleContents {
    PrecClimb {
        child_rule: Ident,
        climber: Expr,
        function: ItemFn,
    },
    Function {
        function: ItemFn,
    },
}

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

impl Parse for Rules {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut rules = Vec::new();
        while !input.is_empty() {
            rules.push(input.parse()?)
        }
        Ok(Rules(rules))
    }
}

impl Parse for Rule {
    fn parse(input: ParseStream) -> Result<Self> {
        let function: ItemFn = input.parse()?;
        let (recognized_attrs, remaining_attrs) = function
            .attrs
            .iter()
            .cloned()
            .partition::<Vec<_>, _>(|attr| attr.path.is_ident("prec_climb"));
        let function = ItemFn {
            attrs: remaining_attrs,
            ..(function.clone())
        };

        let name = function.sig.ident.clone();
        let output_type = match &function.sig.output {
            ReturnType::Default => parse_quote!(()),
            ReturnType::Type(_, t) => (**t).clone(),
        };

        if recognized_attrs.is_empty() {
            Ok(Rule {
                name,
                output_type,
                contents: RuleContents::Function { function },
            })
        } else if recognized_attrs.len() != 1 {
            Err(input.error("expected a prec_climb attribute"))
        } else {
            let attr = recognized_attrs.into_iter().next().unwrap();
            let (child_rule, climber) =
                attr.parse_args_with(|input: ParseStream| {
                    let child_rule: Ident = input.parse()?;
                    let _: Token![,] = input.parse()?;
                    let climber: Expr = input.parse()?;
                    Ok((child_rule, climber))
                })?;

            Ok(Rule {
                name,
                output_type,
                contents: RuleContents::PrecClimb {
                    child_rule,
                    climber,
                    function,
                },
            })
        }
    }
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

fn make_construct_precclimbers(rules: &Rules) -> Result<TokenStream> {
    let mut entries: Vec<TokenStream> = Vec::new();
    for rule in &rules.0 {
        if let RuleContents::PrecClimb { climber, .. } = &rule.contents {
            let name = &rule.name;
            entries.push(quote!(
                map.insert(Rule::#name, #climber);
            ))
        }
    }

    Ok(quote!(
        fn construct_precclimbers() -> HashMap<Rule, PrecClimber<Rule>> {
            let mut map = HashMap::new();
            #(#entries)*
            map
        }
    ))
}

fn make_entrypoints(rules: &Rules) -> Result<TokenStream> {
    let mut entries: Vec<TokenStream> = Vec::new();
    for rule in &rules.0 {
        let name = &rule.name;
        let output_type = &rule.output_type;
        entries.push(quote!(
            #[allow(non_snake_case, dead_code)]
            fn #name<'a>(
                input_str: &str,
                pair: Pair<'a, Rule>,
            ) -> #output_type {
                let climbers = construct_precclimbers();
                let input = ParseInput {
                    climbers: &climbers,
                    original_input_str: input_str.to_string().into(),
                    pair
                };
                Parsers::#name(input)
            }
        ))
    }

    Ok(quote!(
        struct EntryPoint;
        impl EntryPoint {
            #(#entries)*
        }
    ))
}

fn make_parsers(rules: &Rules) -> Result<TokenStream> {
    let entries = rules.0.iter().map(|rule| {
        let name = &rule.name;
        let output_type = &rule.output_type;
        match &rule.contents {
            RuleContents::PrecClimb {
                child_rule,
                function,
                ..
            } => quote!(
                #[allow(non_snake_case, dead_code)]
                fn #name<'a, 'climbers>(
                    input: ParseInput<'a, 'climbers, Rule>,
                ) -> #output_type {
                    #function
                    let climber = input.climbers.get(&Rule::#name).unwrap();
                    climber.climb(
                        input.pair.clone().into_inner(),
                        |p| Parsers::#child_rule(input.with_pair(p)),
                        |l, op, r| {
                            #name(input.clone(), l?, op, r?)
                        },
                    )
                }
            ),
            RuleContents::Function { function } => quote!(
                #[allow(non_snake_case, dead_code)]
                #function
            ),
        }
    });

    Ok(quote!(
        struct Parsers;
        impl Parsers {
            #(#entries)*
        }
    ))
}

pub fn make_parser(
    input: proc_macro::TokenStream,
) -> Result<proc_macro2::TokenStream> {
    let rules: Rules = syn::parse(input.clone())?;

    let construct_precclimbers = make_construct_precclimbers(&rules)?;
    let entrypoints = make_entrypoints(&rules)?;
    let parsers = make_parsers(&rules)?;

    Ok(quote!(
        #construct_precclimbers
        #entrypoints
        #parsers
    ))
}

fn make_parser_branch(branch: &ChildrenBranch) -> Result<TokenStream> {
    use ChildrenBranchPatternItem::{Multiple, Single};

    let body = &branch.body;

    // Convert the input pattern into a pattern-match on the Rules of the children. This uses
    // slice_patterns.
    // A single pattern just checks that the rule matches; a variable-length pattern binds the
    // subslice and checks that they all match the chosen Rule in the `if`-condition.
    let variable_pattern_ident =
        Ident::new("variable_pattern", Span::call_site());
    let match_pat = branch.pattern.iter().map(|item| match item {
        Single { rule_name, .. } => quote!(Rule::#rule_name),
        Multiple { .. } => quote!(#variable_pattern_ident..),
    });
    let match_filter = branch.pattern.iter().map(|item| match item {
        Single { .. } => quote!(),
        Multiple { rule_name, .. } => quote!(
            #variable_pattern_ident.iter().all(|r| r == &Rule::#rule_name) &&
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
            let #binder = Parsers::#rule_name(
                inputs.next().unwrap()
            )?;
        ))
    }
    // Note the `rev()`: we are taking inputs from the end of the iterator in reverse order, so that
    // only the unmatched inputs are left for the variable-length pattern, if any.
    for (rule_name, binder) in singles_after_multiple.into_iter().rev() {
        parses.push(quote!(
            let #binder = Parsers::#rule_name(
                inputs.next_back().unwrap()
            )?;
        ))
    }
    if let Some((rule_name, binder)) = multiple {
        parses.push(quote!(
            let #binder = inputs
                .map(|i| Parsers::#rule_name(i))
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
        let children_rules: Vec<Rule> = #input_expr.pair
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
