use std::collections::BTreeMap;
use itertools::*;
use lalrpop_util;
use pest::Parser;
use pest::iterators::Pair;

use dhall_parser::{DhallParser, Rule};

use crate::grammar;
use crate::grammar_util::{BoxExpr, ParsedExpr};
use crate::lexer::{Lexer, LexicalError, Tok};
use crate::core::{bx, Expr, Builtin, Const, V};

pub fn parse_expr_lalrpop(s: &str) -> Result<BoxExpr, lalrpop_util::ParseError<usize, Tok, LexicalError>>  {
    grammar::ExprParser::new().parse(Lexer::new(s))
}

pub type ParseError = pest::error::Error<Rule>;

pub type ParseResult<T> = Result<T, ParseError>;

pub fn custom_parse_error(pair: &Pair<Rule>, msg: String) -> ParseError {
    let e = pest::error::ErrorVariant::CustomError{ message: msg };
    pest::error::Error::new_from_span(e, pair.as_span())
}



macro_rules! make_parser {
    ($( named!( $name:ident<$o:ty>; $($args:tt)* ); )*) => (
        #[allow(non_camel_case_types)]
        enum ParsedType {
            $( $name, )*
        }

        impl ParsedType {
            fn parse(self, pair: Pair<Rule>) -> ParseResult<ParsedValue> {
                match self {
                    $( ParsedType::$name => $name(pair), )*
                }
            }
        }

        #[allow(non_camel_case_types)]
        enum ParsedValue<'a> {
            $( $name($o), )*
        }

        impl<'a> ParsedValue<'a> {
            $(
                fn $name(self) -> ParseResult<$o> {
                    match self {
                        ParsedValue::$name(x) => Ok(x),
                        _ => unreachable!(),
                    }
                }
            )*
        }

        $(
            named!($name<$o>; $($args)*);
        )*
    );
}

macro_rules! named {
    ($name:ident<$o:ty>; $submac:ident!( $($args:tt)* )) => (
        #[allow(unused_variables)]
        fn $name(pair: Pair<Rule>) -> ParseResult<ParsedValue> {
            let res = $submac!(pair; $($args)*);
            Ok(ParsedValue::$name(res?))
        }
    );
}

macro_rules! match_children {
    // Normal pattern
    (@match 0, $pairs:expr, $x:ident : $ty:ident $($rest:tt)*) => {
        let $x = $ty($pairs.next().unwrap())?.$ty()?;
        match_children!(@match 0, $pairs $($rest)*);
    };
    // Normal pattern after a variable length one: declare reversed and take from the end
    (@match $w:expr, $pairs:expr, $x:ident : $ty:ident $($rest:tt)*) => {
        match_children!(@match $w, $pairs $($rest)*);
        let $x = $ty($pairs.next_back().unwrap())?.$ty()?;
    };
    // Optional pattern
    (@match 0, $pairs:expr, $x:ident? : $ty:ident $($rest:tt)*) => {
        match_children!(@match 1, $pairs $($rest)*);
        let $x = $pairs.next().map($ty).map(|x| x?.$ty()).transpose()?;
        $pairs.next().ok_or(()).expect_err("Some parsed values remain unused");
    };
    // Everything else pattern
    (@match 0, $pairs:expr, $x:ident* : $ty:ident $($rest:tt)*) => {
        match_children!(@match 2, $pairs $($rest)*);
        #[allow(unused_mut)]
        let mut $x = $pairs.map($ty).map(|x| x?.$ty());
    };

    // Check no elements remain
    (@match 0, $pairs:expr) => {
        $pairs.next().ok_or(()).expect_err("Some parsed values remain unused");
    };
    (@match $_:expr, $pairs:expr) => {};

    // Entrypoints
    (@pairs; $pairs:expr; ($($args:tt)*) => $body:expr) => {
        {
            match_children!(@match 0, $pairs, $($args)*);
            Ok($body)
        }
    };
    ($pair:expr; $($rest:tt)*) => {
        {
            #[allow(unused_mut)]
            let mut pairs = $pair.into_inner();
            match_children!(@pairs; pairs; $($rest)*)
        }
    };
}

macro_rules! with_captured_str {
    ($pair:expr; $x:ident; $body:expr) => {
        {
            #[allow(unused_mut)]
            let mut $x = $pair.as_str();
            Ok($body)
        }
    };
}

macro_rules! with_raw_pair {
    ($pair:expr; $x:ident; $body:expr) => {
        {
            #[allow(unused_mut)]
            let mut $x = $pair;
            Ok($body)
        }
    };
}

macro_rules! map {
    ($pair:expr; $ty:ident; $f:expr) => {
        {
            let x = $ty($pair)?.$ty()?;
            Ok($f(x))
        }
    };
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
                rest.fold_results(first, |acc, e| bx(f(acc, e)))?
            })
        }
    };
}

macro_rules! single {
    ($pair:expr; $ty:ident) => {
        match_children!($pair; (expr: $ty) => expr)
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


make_parser!{
    named!(eoi<()>; plain_value!(()));

    named!(str<&'a str>; with_captured_str!(s; { s.trim() }));

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
                for entry in entries {
                    let (n, e) = entry?;
                    map.insert(n, *e);
                }
                (rule, expr, map)
            })
        )
    );

    named!(expression<BoxExpr<'a>>; match_rule!(
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
                bindings.fold_results(final_expr, |acc, x| bx(Expr::Let(x.0, x.1, x.2, acc)))?
            }),

        Rule::forall_expression =>
            match_children!((label: str, typ: expression, body: expression) => {
                bx(Expr::Pi(label, typ, body))
            }),

        Rule::annotated_expression => binop!(Expr::Annot),
        Rule::import_alt_expression => single!(expression),
        Rule::or_expression => binop!(Expr::BoolOr),
        Rule::plus_expression => binop!(Expr::NaturalPlus),
        Rule::text_append_expression => binop!(Expr::TextAppend),
        Rule::list_append_expression => single!(expression),
        Rule::and_expression => binop!(Expr::BoolAnd),
        Rule::combine_expression => single!(expression),
        Rule::prefer_expression => single!(expression),
        Rule::combine_types_expression => single!(expression),
        Rule::times_expression => binop!(Expr::NaturalTimes),
        Rule::equal_expression => binop!(Expr::BoolEQ),
        Rule::not_equal_expression => binop!(Expr::BoolNE),
        Rule::application_expression => binop!(Expr::App),

        Rule::selector_expression_raw =>
            match_children!((first: expression, rest*: str) => {
                rest.fold_results(first, |acc, e| bx(Expr::Field(acc, e)))?
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

        _ => with_rule!(rule;
            match_children!((exprs*: expression) => {
                // panic!();
                let rulename = format!("{:?}", rule);
                bx(Expr::FailedParse(rulename, exprs.map_results(|x| *x).collect::<ParseResult<_>>()?))
            })
        ),
    ));
}


pub fn parse_expr_pest(s: &str) -> ParseResult<BoxExpr>  {
    let mut pairs = DhallParser::parse(Rule::final_expression, s)?;
    match_children!(@pairs; pairs; (e: expression, _eoi: eoi) => e)
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
        },
        ok => println!("{:?}", ok),
    }
    // assert_eq!(parse_expr_pest(expr).unwrap(), parse_expr_lalrpop(expr).unwrap());
    // assert!(false);

    println!("test {:?}", parse_expr_lalrpop("3 + 5 * 10"));
    assert!(parse_expr_lalrpop("22").is_ok());
    assert!(parse_expr_lalrpop("(22)").is_ok());
    assert_eq!(parse_expr_lalrpop("3 + 5 * 10").ok(),
               Some(Box::new(NaturalPlus(Box::new(NaturalLit(3)),
                                Box::new(NaturalTimes(Box::new(NaturalLit(5)),
                                                      Box::new(NaturalLit(10))))))));
    // The original parser is apparently right-associative
    assert_eq!(parse_expr_lalrpop("2 * 3 * 4").ok(),
               Some(Box::new(NaturalTimes(Box::new(NaturalLit(2)),
                                 Box::new(NaturalTimes(Box::new(NaturalLit(3)),
                                                       Box::new(NaturalLit(4))))))));
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
