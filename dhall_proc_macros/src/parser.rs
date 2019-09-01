use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::parse::{Parse, ParseStream, Result};
use syn::punctuated::Punctuated;
use syn::{bracketed, parenthesized, token, Expr, Ident, Pat, Token, Type};

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
    rule_token: rule_kw::rule,
    bang_token: Token![!],
    paren_token: token::Paren,
    name: Ident,
    lt_token: token::Lt,
    output_type: Type,
    gt_token: token::Gt,
    contents: RuleContents,
    semi_token: Token![;],
}

#[derive(Debug, Clone)]
enum RuleContents {
    Empty,
    CapturedString {
        span: Option<Ident>,
        captured_str_token: rule_kw::captured_str,
        bang_token: Token![!],
        paren_token: token::Paren,
        pattern: Pat,
        fat_arrow_token: Token![=>],
        body: Expr,
    },
    Children {
        span: Option<Ident>,
        children_token: rule_kw::children,
        bang_token: Token![!],
        paren_token: token::Paren,
        branches: Punctuated<ChildrenBranch, Token![,]>,
    },
    PrecClimb {
        span: Option<Ident>,
        prec_climb_token: rule_kw::prec_climb,
        bang_token: Token![!],
        paren_token: token::Paren,
        child_rule: Ident,
        comma_token: Token![,],
        climber: Expr,
        comma_token2: Token![,],
        pattern: Pat,
        fat_arrow_token: Token![=>],
        body: Expr,
    },
}

#[derive(Debug, Clone)]
struct ChildrenBranch {
    bracket_token: token::Bracket,
    pattern_unparsed: TokenStream,
    pattern: Punctuated<ChildrenBranchPatternItem, Token![,]>,
    fat_arrow_token: Token![=>],
    body: Expr,
}

#[derive(Debug, Clone)]
enum ChildrenBranchPatternItem {
    Single {
        rule_name: Ident,
        paren_token: token::Paren,
        binder: Pat,
    },
    Multiple {
        rule_name: Ident,
        paren_token: token::Paren,
        binder: Ident,
        slice_token: Token![..],
    },
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
        let contents;
        Ok(Rule {
            rule_token: input.parse()?,
            bang_token: input.parse()?,
            paren_token: parenthesized!(contents in input),
            name: contents.parse()?,
            lt_token: contents.parse()?,
            output_type: contents.parse()?,
            gt_token: contents.parse()?,
            contents: contents.parse()?,
            semi_token: input.parse()?,
        })
    }
}

impl Parse for RuleContents {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.is_empty() {
            return Ok(RuleContents::Empty);
        }
        let _: Token![;] = input.parse()?;
        let span = if input.peek(Ident) && input.peek2(Token![;]) {
            let span: Ident = input.parse()?;
            let _: Token![;] = input.parse()?;
            Some(span)
        } else {
            None
        };

        let lookahead = input.lookahead1();
        if lookahead.peek(rule_kw::captured_str) {
            let contents;
            Ok(RuleContents::CapturedString {
                span,
                captured_str_token: input.parse()?,
                bang_token: input.parse()?,
                paren_token: parenthesized!(contents in input),
                pattern: contents.parse()?,
                fat_arrow_token: input.parse()?,
                body: input.parse()?,
            })
        } else if lookahead.peek(rule_kw::children) {
            let contents;
            Ok(RuleContents::Children {
                span,
                children_token: input.parse()?,
                bang_token: input.parse()?,
                paren_token: parenthesized!(contents in input),
                branches: Punctuated::parse_terminated(&contents)?,
            })
        } else if lookahead.peek(rule_kw::prec_climb) {
            let contents;
            Ok(RuleContents::PrecClimb {
                span,
                prec_climb_token: input.parse()?,
                bang_token: input.parse()?,
                paren_token: parenthesized!(contents in input),
                child_rule: contents.parse()?,
                comma_token: contents.parse()?,
                climber: contents.parse()?,
                comma_token2: contents.parse()?,
                pattern: contents.parse()?,
                fat_arrow_token: contents.parse()?,
                body: contents.parse()?,
            })
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for ChildrenBranch {
    fn parse(input: ParseStream) -> Result<Self> {
        let contents;
        Ok(ChildrenBranch {
            bracket_token: bracketed!(contents in input),
            pattern_unparsed: contents.fork().parse()?,
            pattern: Punctuated::parse_terminated(&contents)?,
            fat_arrow_token: input.parse()?,
            body: input.parse()?,
        })
    }
}

impl Parse for ChildrenBranchPatternItem {
    fn parse(input: ParseStream) -> Result<Self> {
        let rule_name = input.parse()?;
        let contents;
        let paren_token = parenthesized!(contents in input);
        if input.peek(Token![..]) {
            Ok(ChildrenBranchPatternItem::Multiple {
                rule_name,
                paren_token,
                binder: contents.parse()?,
                slice_token: input.parse()?,
            })
        } else if input.is_empty() || input.peek(Token![,]) {
            Ok(ChildrenBranchPatternItem::Single {
                rule_name,
                paren_token,
                binder: contents.parse()?,
            })
        } else {
            Err(input.error("expected `..` or nothing"))
        }
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
                input: Rc<str>,
                pair: Pair<'a, Rule>,
            ) -> ParseResult<#output_type> {
                let climbers = construct_precclimbers();
                Parsers::#name((&climbers, input), pair)
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

fn make_parser_branch(branch: &ChildrenBranch) -> TokenStream {
    let ChildrenBranch {
        pattern,
        body,
        pattern_unparsed,
        ..
    } = branch;
    let variable_pattern = Ident::new("variable_pattern", Span::call_site());
    let match_pat = pattern.iter().map(|item| match item {
        ChildrenBranchPatternItem::Single { rule_name, .. } => {
            quote!(Rule::#rule_name)
        }
        ChildrenBranchPatternItem::Multiple { .. } => {
            quote!(#variable_pattern..)
        }
    });
    let match_filter = pattern.iter().map(|item| match item {
        ChildrenBranchPatternItem::Single { .. } => quote!(true &&),
        ChildrenBranchPatternItem::Multiple { rule_name, .. } => {
            quote!(#variable_pattern.iter().all(|r| r == &Rule::#rule_name) &&)
        }
    });
    quote!(
        [#(#match_pat),*] if #(#match_filter)* true => {
            parse_children!((climbers, input.clone()), iter;
                [#pattern_unparsed] => {
                    #[allow(unused_variables)]
                    let res: Result<_, String> = try { #body };
                    res.map_err(|msg|
                        custom_parse_error(&pair, msg)
                    )
                }
            )
        }
    )
}

fn make_parser_expr(rule: &Rule) -> Result<TokenStream> {
    let name = &rule.name;
    let expr = match &rule.contents {
        RuleContents::Empty => quote!(Ok(())),
        RuleContents::CapturedString { pattern, body, .. } => quote!(
            let #pattern = pair.as_str();
            let res: Result<_, String> = try { #body };
            res.map_err(|msg| custom_parse_error(&pair, msg))
        ),
        RuleContents::PrecClimb {
            child_rule,
            pattern,
            body,
            ..
        } => quote!(
            let climber = climbers.get(&Rule::#name).unwrap();
            climber.climb(
                pair.clone().into_inner(),
                |p| Parsers::#child_rule((climbers, input.clone()), p),
                |l, op, r| {
                    let #pattern = (l?, op, r?);
                    let res: Result<_, String> = try { #body };
                    res.map_err(|msg| custom_parse_error(&pair, msg))
                },
            )
        ),
        RuleContents::Children { branches, .. } => {
            let branches = branches.iter().map(make_parser_branch);
            quote!(
                let children_rules: Vec<Rule> = pair
                    .clone()
                    .into_inner()
                    .map(|p| p.as_rule())
                    .collect();

                #[allow(unused_mut)]
                let mut iter = pair.clone().into_inner();

                #[allow(unreachable_code)]
                match children_rules.as_slice() {
                    #(#branches,)*
                    [..] => Err(custom_parse_error(
                        &pair,
                        format!("Unexpected children: {:?}", children_rules)
                    )),
                }
            )
        }
    };
    Ok(expr)
}

fn make_parsers(rules: &Rules) -> Result<TokenStream> {
    let mut entries: Vec<TokenStream> = Vec::new();
    for rule in &rules.0 {
        let span_def = match &rule.contents {
            RuleContents::CapturedString {
                span: Some(span), ..
            }
            | RuleContents::Children {
                span: Some(span), ..
            }
            | RuleContents::PrecClimb {
                span: Some(span), ..
            } => Some(quote!(
                let #span = Span::make(input.clone(), pair.as_span());
            )),
            _ => None,
        };

        let name = &rule.name;
        let output_type = &rule.output_type;
        let expr = make_parser_expr(rule)?;

        entries.push(quote!(
            #[allow(non_snake_case, dead_code)]
            fn #name<'a>(
                (climbers, input): (&HashMap<Rule, PrecClimber<Rule>>, Rc<str>),
                pair: Pair<'a, Rule>,
            ) -> ParseResult<#output_type> {
                #span_def
                #expr
            }
        ))
    }

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
    let rules: Rules = syn::parse_macro_input::parse(input.clone())?;

    let construct_precclimbers = make_construct_precclimbers(&rules)?;
    let entrypoints = make_entrypoints(&rules)?;
    let parsers = make_parsers(&rules)?;

    Ok(quote!(
        #construct_precclimbers
        #entrypoints
        #parsers
    ))
}
