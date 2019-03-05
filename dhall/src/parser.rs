use std::collections::BTreeMap;
// use itertools::*;
use lalrpop_util;
use pest::iterators::Pair;
use pest::Parser;

use dhall_parser::{DhallParser, Rule};

use crate::core::{bx, Builtin, Const, Expr, V};
use crate::grammar;
use crate::grammar_util::{BoxExpr, ParsedExpr};
use crate::lexer::{Lexer, LexicalError, Tok};

pub fn parse_expr_lalrpop(
    s: &str,
) -> Result<BoxExpr, lalrpop_util::ParseError<usize, Tok, LexicalError>> {
    grammar::ExprParser::new().parse(Lexer::new(s))
    // Ok(bx(Expr::BoolLit(false)))
}

pub type ParseError = pest::error::Error<Rule>;

pub type ParseResult<T> = Result<T, ParseError>;

pub fn custom_parse_error(pair: &Pair<Rule>, msg: String) -> ParseError {
    let e = pest::error::ErrorVariant::CustomError { message: msg };
    pest::error::Error::new_from_span(e, pair.as_span())
}

fn debug_pair(pair: Pair<Rule>) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    fn aux(s: &mut String, indent: usize, prefix: String, pair: Pair<Rule>) {
        let indent_str = "| ".repeat(indent);
        let rule = pair.as_rule();
        let contents = pair.as_str().clone();
        let mut inner = pair.into_inner();
        let mut first = true;
        while let Some(p) = inner.next() {
            if first {
                first = false;
                let last = inner.peek().is_none();
                if last && p.as_str() == contents {
                    let prefix = format!("{}{:?} > ", prefix, rule);
                    aux(s, indent, prefix, p);
                    continue;
                } else {
                    writeln!(
                        s,
                        r#"{}{}{:?}: "{}""#,
                        indent_str, prefix, rule, contents
                    )
                    .unwrap();
                }
            }
            aux(s, indent + 1, "".into(), p);
        }
        if first {
            writeln!(
                s,
                r#"{}{}{:?}: "{}""#,
                indent_str, prefix, rule, contents
            )
            .unwrap();
        }
    }
    aux(&mut s, 0, "".into(), pair);
    s
}

/* Macro to pattern-match iterators.
 * Panics if the sequence doesn't match;
 *
 * Example:
 * ```
 * let vec = vec![1, 2, 3];
 *
 * match_iter!(vec.into_iter(); (x, y?, z) => {
 *  // x: T
 *  // y: Option<T>
 *  // z: T
 * })
 *
 * // or
 * match_iter!(vec.into_iter(); (x, y, z*) => {
 *  // x, y: T
 *  // z: impl Iterator<T>
 * })
 * ```
 *
*/
#[derive(Debug)]
enum IterMatchError<T> {
    NotEnoughItems,
    TooManyItems,
    Other(T), // Allow other macros to inkect their own errors
}
macro_rules! match_iter {
    // Everything else pattern
    (@match 0, $iter:expr, $x:ident* $($rest:tt)*) => {
        match_iter!(@match 2, $iter $($rest)*);
        #[allow(unused_mut)]
        let mut $x = $iter;
    };
    // Alias to use in macros
    (@match 0, $iter:expr, $x:ident?? $($rest:tt)*) => {
        match_iter!(@match 2, $iter $($rest)*);
        #[allow(unused_mut)]
        let mut $x = $iter;
    };
    // Optional pattern
    (@match 0, $iter:expr, $x:ident? $($rest:tt)*) => {
        match_iter!(@match 1, $iter $($rest)*);
        let $x = $iter.next();
        match $iter.next() {
            Some(_) => break Err(IterMatchError::TooManyItems),
            None => {},
        };
    };
    // Normal pattern
    (@match 0, $iter:expr, $x:ident $($rest:tt)*) => {
        let $x = match $iter.next() {
            Some(x) => x,
            None => break Err(IterMatchError::NotEnoughItems),
        };
        match_iter!(@match 0, $iter $($rest)*);
    };
    // Normal pattern after a variable length one: declare reversed and take from the end
    (@match $w:expr, $iter:expr, $x:ident $($rest:tt)*) => {
        match_iter!(@match $w, $iter $($rest)*);
        let $x = match $iter.next_back() {
            Some(x) => x,
            None => break Err(IterMatchError::NotEnoughItems),
        };
    };

    // Check no elements remain
    (@match 0, $iter:expr $(,)*) => {
        match $iter.next() {
            Some(_) => break Err(IterMatchError::TooManyItems),
            None => {},
        };
    };
    (@match $_:expr, $iter:expr) => {};

    // Entrypoints
    (@get_err, $iter:expr; ($($args:tt)*) => $body:expr) => {
        {
            #[allow(unused_mut)]
            let mut iter = $iter;
            let ret: Result<_, IterMatchError<_>> = loop {
                match_iter!(@match 0, iter, $($args)*);
                break Ok($body);
            };
            ret
        }
    };
    ($($args:tt)*) => {
        {
            let ret: Result<_, IterMatchError<()>> = match_iter!(@get_err, $($args)*);
            ret.unwrap()
        }
    };
}

macro_rules! named {
    ($name:ident<$o:ty>; $submac:ident!( $($args:tt)* )) => (
        #[allow(unused_variables)]
        fn $name<'a>(pair: Pair<'a, Rule>) -> ParseResult<$o> {
            $submac!(pair; $($args)*)
        }
    );
}

macro_rules! named_rule {
    ($name:ident<$o:ty>; $submac:ident!( $($args:tt)* )) => (
        named!($name<$o>; match_rule!(
            Rule::$name => $submac!( $($args)* ),
        ));
    );
}

macro_rules! match_children {
    (@collect, $pairs:expr, ($($args:tt)*), $body:expr, ($($acc:tt)*), ($x:ident : $ty:ident, $($rest:tt)*)) => {
        match_children!(@collect, $pairs, ($($args)*), $body, ($($acc)*, $x), ($($rest)*))
    };
    (@collect, $pairs:expr, ($($args:tt)*), $body:expr, ($($acc:tt)*), ($x:ident? : $ty:ident, $($rest:tt)*)) => {
        match_children!(@collect, $pairs, ($($args)*), $body, ($($acc)*, $x?), ($($rest)*))
    };
    (@collect, $pairs:expr, ($($args:tt)*), $body:expr, ($($acc:tt)*), ($x:ident* : $ty:ident, $($rest:tt)*)) => {
        match_children!(@collect, $pairs, ($($args)*), $body, ($($acc)*, $x??), ($($rest)*))
    };
    // Catch extra comma if exists
    (@collect, $pairs:expr, ($($args:tt)*), $body:expr, (,$($acc:tt)*), ($(,)*)) => {
        match_children!(@collect, $pairs, ($($args)*), $body, ($($acc)*), ())
    };
    (@collect, $pairs:expr, ($($args:tt)*), $body:expr, ($($acc:tt)*), ($(,)*)) => {
        let matched: Result<_, IterMatchError<ParseError>> =
            match_iter!(@get_err, $pairs; ($($acc)*) => {
                match_children!(@parse, $pairs, $($args)*);
                Ok($body)
        });
        match matched {
            Ok(v) => break v,
            Err(_) => {},
        };
    };

    (@parse, $pairs:expr, $x:ident : $ty:ident $($rest:tt)*) => {
        let $x = $ty($x);
        let $x = match $x {
            Ok(x) => x,
            Err(e) => break Err(IterMatchError::Other(e)),
        };
        match_children!(@parse, $pairs $($rest)*);
    };
    (@parse, $pairs:expr, $x:ident? : $ty:ident $($rest:tt)*) => {
        let $x = $x.map($ty);
        let $x = match $x {
            Some(Ok(x)) => Some(x),
            Some(Err(e)) => break Err(IterMatchError::Other(e)),
            None => None,
        };
        match_children!(@parse, $pairs $($rest)*);
    };
    (@parse, $pairs:expr, $x:ident* : $ty:ident $($rest:tt)*) => {
        let $x = $x.map($ty).collect::<ParseResult<Vec<_>>>();
        #[allow(unused_mut)]
        let mut $x = match $x {
            Ok(x) => x.into_iter(),
            Err(e) => break Err(IterMatchError::Other(e)),
        };
        match_children!(@parse, $pairs $($rest)*);
    };
    (@parse, $pairs:expr $(,)*) => {};

    // Entrypoint
    ($pair:expr; $( ($($args:tt)*) => $body:expr ),* $(,)*) => {
        {
            let pair = $pair;
            #[allow(unused_mut)]
            let mut pairs = pair.clone().into_inner();
            // Would use loop labels but they create warnings
            #[allow(unreachable_code)]
            loop {
                $(
                    match_children!(@collect, pairs.clone(), ($($args)*), $body, (), ($($args)*,));
                )*
                // break Err(TODO);
                panic!("No match found while matching on:\n{}", debug_pair(pair));
            }
        }
    };
}

macro_rules! with_captured_str {
    ($pair:expr; $x:ident; $body:expr) => {{
        #[allow(unused_mut)]
        let mut $x = $pair.as_str();
        Ok($body)
    }};
}

macro_rules! with_raw_pair {
    ($pair:expr; $x:ident; $body:expr) => {{
        #[allow(unused_mut)]
        let mut $x = $pair;
        Ok($body)
    }};
}

macro_rules! map {
    ($pair:expr; $ty:ident; $f:expr) => {{
        let x = $ty($pair)?;
        Ok($f(x))
    }};
}

macro_rules! plain_value {
    ($_pair:expr; $body:expr) => {
        Ok($body)
    };
}

macro_rules! binop {
    ($pair:expr; $f:expr) => {
        {
            let f = $f;
            match_children!($pair; (first: expression, rest*: expression) => {
                rest.fold(first, |acc, e| bx(f(acc, e)))
            })
        }
    };
}

macro_rules! with_rule {
    ($pair:expr; $x:ident; $submac:ident!( $($args:tt)* )) => {
        {
            #[allow(unused_mut)]
            let mut $x = $pair.as_rule();
            $submac!($pair; $($args)*)
        }
    };
}

macro_rules! match_rule {
    ($pair:expr; $($pat:pat => $submac:ident!( $($args:tt)* ),)*) => {
        {
            #[allow(unreachable_patterns)]
            match $pair.as_rule() {
                $(
                    $pat => $submac!($pair; $($args)*),
                )*
                r => Err(custom_parse_error(&$pair, format!("Unexpected {:?}", r))),
            }
        }
    };
}

named!(eoi<()>; plain_value!(()));

named!(str<&'a str>; with_captured_str!(s; { s.trim() }));

named!(raw_str<&'a str>; with_captured_str!(s; s));

named!(natural<usize>; with_raw_pair!(pair; {
    pair.as_str().trim()
        .parse()
        .map_err(|e: std::num::ParseIntError| custom_parse_error(&pair, format!("{}", e)))?
}));

named!(integer<isize>; with_raw_pair!(pair; {
    pair.as_str().trim()
        .parse()
        .map_err(|e: std::num::ParseIntError| custom_parse_error(&pair, format!("{}", e)))?
}));

named!(letbinding<(&'a str, Option<BoxExpr<'a>>, BoxExpr<'a>)>;
    match_children!((name: str, annot?: expression, expr: expression) => (name, annot, expr))
);

named!(record_entry<(&'a str, BoxExpr<'a>)>;
    match_children!((name: str, expr: expression) => (name, expr))
);

named!(partial_record_entries<(Rule, BoxExpr<'a>, BTreeMap<&'a str, ParsedExpr<'a>>)>;
    with_rule!(rule;
        match_children!((expr: expression, entries*: record_entry) => {
            let mut map: BTreeMap<&str, ParsedExpr> = BTreeMap::new();
            for (n, e) in entries {
                map.insert(n, *e);
            }
            (rule, expr, map)
        })
    )
);

named_rule!(union_type_entry<(&'a str, BoxExpr<'a>)>;
    match_children!((name: str, expr: expression) => (name, expr))
);

named_rule!(union_type_entries<BTreeMap<&'a str, ParsedExpr<'a>>>;
    match_children!((entries*: union_type_entry) => {
        let mut map: BTreeMap<&str, ParsedExpr> = BTreeMap::new();
        for (n, e) in entries {
            map.insert(n, *e);
        }
        map
    })
);

named_rule!(non_empty_union_type_or_literal<(Option<(&'a str, BoxExpr<'a>)>, BTreeMap<&'a str, ParsedExpr<'a>>)>;
    match_children!(
        (label: str, e: expression, entries: union_type_entries) => {
            (Some((label, e)), entries)
        },
        (l: str, e: expression, rest: non_empty_union_type_or_literal) => {
            let (x, mut entries) = rest;
            entries.insert(l, *e);
            (x, entries)
        },
        (l: str, e: expression) => {
            let mut entries = BTreeMap::new();
            entries.insert(l, *e);
            (None, entries)
        },
    )
);

named_rule!(empty_union_type<()>; plain_value!(()));

named!(expression<BoxExpr<'a>>; match_rule!(
    Rule::double_quote_literal =>
        match_children!((strs*: raw_str) => {
            bx(Expr::TextLit(strs.collect()))
        }),

    Rule::natural_literal_raw => map!(natural; |n| bx(Expr::NaturalLit(n))),
    Rule::integer_literal_raw => map!(integer; |n| bx(Expr::IntegerLit(n))),

    Rule::identifier_raw =>
        match_children!((name: str, idx?: natural) => {
            match Builtin::parse(name) {
                Some(b) => bx(Expr::Builtin(b)),
                None => match name {
                    "True" => bx(Expr::BoolLit(true)),
                    "False" => bx(Expr::BoolLit(false)),
                    "Type" => bx(Expr::Const(Const::Type)),
                    "Kind" => bx(Expr::Const(Const::Kind)),
                    name => bx(Expr::Var(V(name, idx.unwrap_or(0)))),
                }
            }
        }),

    Rule::lambda_expression =>
        match_children!((label: str, typ: expression, body: expression) => {
            bx(Expr::Lam(label, typ, body))
        }),

    Rule::ifthenelse_expression =>
        match_children!((cond: expression, left: expression, right: expression) => {
            bx(Expr::BoolIf(cond, left, right))
        }),

    Rule::let_expression =>
        match_children!((bindings*: letbinding, final_expr: expression) => {
            bindings.fold(final_expr, |acc, x| bx(Expr::Let(x.0, x.1, x.2, acc)))
        }),

    Rule::forall_expression =>
        match_children!((label: str, typ: expression, body: expression) => {
            bx(Expr::Pi(label, typ, body))
        }),

    Rule::arrow_expression =>
        match_children!((typ: expression, body: expression) => {
            bx(Expr::Pi("_", typ, body))
        }),

    Rule::merge_expression =>
        match_children!((x: expression, y: expression, z?: expression) => {
            bx(Expr::Merge(x, y, z))
        }),

    Rule::empty_collection =>
        match_children!((x: str, y: expression) => {
           match x {
              "Optional" => bx(Expr::OptionalLit(Some(y), vec![])),
              "List" => bx(Expr::ListLit(Some(y), vec![])),
              _ => unreachable!(),
           }
        }),

    Rule::non_empty_optional =>
        match_children!((x: expression, _y: str, z: expression) => {
            bx(Expr::OptionalLit(Some(z), vec![*x]))
        }),

    Rule::annotated_expression => binop!(Expr::Annot),
    Rule::import_alt_expression => binop!(Expr::ImportAlt),
    Rule::or_expression => binop!(Expr::BoolOr),
    Rule::plus_expression => binop!(Expr::NaturalPlus),
    Rule::text_append_expression => binop!(Expr::TextAppend),
    Rule::list_append_expression => binop!(Expr::ListAppend),
    Rule::and_expression => binop!(Expr::BoolAnd),
    Rule::combine_expression => binop!(Expr::Combine),
    Rule::prefer_expression => binop!(Expr::Prefer),
    Rule::combine_types_expression => binop!(Expr::CombineTypes),
    Rule::times_expression => binop!(Expr::NaturalTimes),
    Rule::equal_expression => binop!(Expr::BoolEQ),
    Rule::not_equal_expression => binop!(Expr::BoolNE),
    Rule::application_expression => binop!(Expr::App),

    Rule::selector_expression_raw =>
        match_children!((first: expression, rest*: str) => {
            rest.fold(first, |acc, e| bx(Expr::Field(acc, e)))
        }),

    Rule::empty_record_type => plain_value!(bx(Expr::Record(BTreeMap::new()))),
    Rule::empty_record_literal => plain_value!(bx(Expr::RecordLit(BTreeMap::new()))),
    Rule::non_empty_record_type_or_literal =>
        match_children!((first_label: str, rest: partial_record_entries) => {
            let (rule, first_expr, mut map) = rest;
            map.insert(first_label, *first_expr);
            match rule {
                Rule::non_empty_record_type => bx(Expr::Record(map)),
                Rule::non_empty_record_literal => bx(Expr::RecordLit(map)),
                _ => unreachable!()
            }
        }),

    Rule::union_type_or_literal =>
        match_children!(
            (_e: empty_union_type) => {
                bx(Expr::Union(BTreeMap::new()))
            },
            (x: non_empty_union_type_or_literal) => {
                match x {
                    (Some((l, e)), entries) => bx(Expr::UnionLit(l, e, entries)),
                    (None, entries) => bx(Expr::Union(entries)),
                }
            },
        ),
    Rule::non_empty_list_literal_raw =>
        match_children!((items*: expression) => {
            bx(Expr::ListLit(None, items.map(|x| *x).collect()))
        }),


    _ => with_rule!(rule;
        match_children!((exprs*: expression) => {
            let rulename = format!("{:?}", rule);
            // panic!(rulename);
            bx(Expr::FailedParse(rulename, exprs.map(|x| *x).collect()))
        })
    ),
));

named!(final_expression<BoxExpr<'a>>;
    match_children!((e: expression, _eoi: eoi) => e)
);

pub fn parse_expr_pest(s: &str) -> ParseResult<BoxExpr> {
    let pairs = DhallParser::parse(Rule::final_expression, s)?;
    match_iter!(pairs; (e) => final_expression(e))
}

#[test]
fn test_parse() {
    use crate::core::Expr::*;
    // let expr = r#"{ x = "foo", y = 4 }.x"#;
    // let expr = r#"(1 + 2) * 3"#;
    let expr = r#"if True then 1 + 3 * 5 else 2"#;
    println!("{:?}", parse_expr_lalrpop(expr));
    match parse_expr_pest(expr) {
        Err(e) => {
            println!("{:?}", e);
            println!("{}", e);
        }
        ok => println!("{:?}", ok),
    }
    // assert_eq!(parse_expr_pest(expr).unwrap(), parse_expr_lalrpop(expr).unwrap());
    // assert!(false);

    println!("test {:?}", parse_expr_lalrpop("3 + 5 * 10"));
    assert!(parse_expr_lalrpop("22").is_ok());
    assert!(parse_expr_lalrpop("(22)").is_ok());
    assert_eq!(
        parse_expr_lalrpop("3 + 5 * 10").ok(),
        Some(Box::new(NaturalPlus(
            Box::new(NaturalLit(3)),
            Box::new(NaturalTimes(
                Box::new(NaturalLit(5)),
                Box::new(NaturalLit(10))
            ))
        )))
    );
    // The original parser is apparently right-associative
    assert_eq!(
        parse_expr_lalrpop("2 * 3 * 4").ok(),
        Some(Box::new(NaturalTimes(
            Box::new(NaturalLit(2)),
            Box::new(NaturalTimes(
                Box::new(NaturalLit(3)),
                Box::new(NaturalLit(4))
            ))
        )))
    );
    assert!(parse_expr_lalrpop("((((22))))").is_ok());
    assert!(parse_expr_lalrpop("((22)").is_err());
    println!("{:?}", parse_expr_lalrpop("\\(b : Bool) -> b == False"));
    assert!(parse_expr_lalrpop("\\(b : Bool) -> b == False").is_ok());
    println!("{:?}", parse_expr_lalrpop("foo.bar"));
    assert!(parse_expr_lalrpop("foo.bar").is_ok());
    assert!(parse_expr_lalrpop("[] : List Bool").is_ok());

    // println!("{:?}", parse_expr_lalrpop("< Left = True | Right : Natural >"));
    // println!("{:?}", parse_expr_lalrpop(r#""bl${42}ah""#));
    // assert!(parse_expr_lalrpop("< Left = True | Right : Natural >").is_ok());
}
