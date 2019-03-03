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


macro_rules! parse_aux {
    // Normal pattern
    (0, $inner:expr, $x:ident : $ty:ident $($rest:tt)*) => {
        let $x = concat_idents!(parse_, $ty)($inner.next().unwrap())?;
        parse_aux!(0, $inner $($rest)*);
    };
    // Normal pattern after a variable length one: declare reversed and take from the end
    ($w:expr, $inner:expr, $x:ident : $ty:ident $($rest:tt)*) => {
        parse_aux!($w, $inner $($rest)*);
        let $x = concat_idents!(parse_, $ty)($inner.next_back().unwrap())?;
    };
    // Optional pattern
    (0, $inner:expr, $x:ident? : $ty:ident $($rest:tt)*) => {
        parse_aux!(1, $inner $($rest)*);
        let $x = $inner.next().map(concat_idents!(parse_, $ty)).transpose()?;
        $inner.next().ok_or(()).expect_err("Some parsed values remain unused");
    };
    // Everything else pattern
    (0, $inner:expr, $x:ident* : $ty:ident $($rest:tt)*) => {
        parse_aux!(2, $inner $($rest)*);
        #[allow(unused_mut)]
        let mut $x = $inner.map(concat_idents!(parse_, $ty));
    };

    // Check no elements remain
    (0, $inner:expr) => {
        $inner.next().ok_or(()).expect_err("Some parsed values remain unused");
    };
    ($_:expr, $inner:expr) => {};
}

macro_rules! parse {
    ($pair:expr; ($($args:tt)*) => $body:expr) => {
        {
            #[allow(unused_mut)]
            let mut inner = $pair.into_inner();
            parse_aux!(0, inner, $($args)*);
            Ok($body)
        }
    };
}


fn parse_binop<'a, F>(pair: Pair<'a, Rule>, mut f: F) -> ParseResult<BoxExpr<'a>>
where F: FnMut(BoxExpr<'a>, BoxExpr<'a>) -> ParsedExpr<'a> {
    parse!(pair; (first: expression, rest*: expression) => {
        rest.fold_results(first, |acc, e| bx(f(acc, e)))?
    })
}

fn skip_expr(pair: Pair<Rule>) -> ParseResult<BoxExpr> {
    parse!(pair; (expr: expression) => {
        expr
    })
}

fn parse_str(pair: Pair<Rule>) -> ParseResult<&str> {
    Ok(pair.as_str().trim())
}

fn parse_natural(pair: Pair<Rule>) -> ParseResult<usize> {
    parse_str(pair.clone())?
        .parse()
        .map_err(|e: std::num::ParseIntError| custom_parse_error(&pair, format!("{}", e)))
}

fn parse_integer(pair: Pair<Rule>) -> ParseResult<isize> {
    parse_str(pair.clone())?
        .parse()
        .map_err(|e: std::num::ParseIntError| custom_parse_error(&pair, format!("{}", e)))
}

fn parse_letbinding(pair: Pair<Rule>) -> ParseResult<(&str, Option<BoxExpr>, BoxExpr)> {
    parse!(pair; (name: str, annot?: expression, expr: expression) => {
        (name, annot, expr)
    })
}

fn parse_record_entry(pair: Pair<Rule>) -> ParseResult<(&str, BoxExpr)> {
    parse!(pair; (name: str, expr: expression) => { (name, expr) })
}

fn parse_partial_record_entries(pair: Pair<Rule>) -> ParseResult<(Rule, BoxExpr, BTreeMap<&str, ParsedExpr>)> {
    let rule = pair.as_rule();
    parse!(pair; (expr: expression, entries*: record_entry) => {
        let mut map: BTreeMap<&str, ParsedExpr> = BTreeMap::new();
        for entry in entries {
            let (n, e) = entry?;
            map.insert(n, *e);
        }
        (rule, expr, map)
    })
}

// TODO: handle stack manually
fn parse_expression(pair: Pair<Rule>) -> ParseResult<BoxExpr> {
    match pair.as_rule() {
        Rule::natural_literal_raw => Ok(bx(Expr::NaturalLit(parse_natural(pair)?))),
        Rule::integer_literal_raw => Ok(bx(Expr::IntegerLit(parse_integer(pair)?))),

        Rule::identifier_raw =>
            parse!(pair; (name: str, idx?: natural) => {
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
            parse!(pair; (label: str, typ: expression, body: expression) => {
                bx(Expr::Lam(label, typ, body))
            }),

        Rule::ifthenelse_expression =>
            parse!(pair; (cond: expression, left: expression, right: expression) => {
                bx(Expr::BoolIf(cond, left, right))
            }),

        Rule::let_expression =>
            parse!(pair; (bindings*: letbinding, final_expr: expression) => {
                bindings.fold_results(final_expr, |acc, x| bx(Expr::Let(x.0, x.1, x.2, acc)))?
            }),

        Rule::forall_expression =>
            parse!(pair; (label: str, typ: expression, body: expression) => {
                bx(Expr::Pi(label, typ, body))
            }),

        Rule::annotated_expression => { parse_binop(pair, Expr::Annot) }
        Rule::import_alt_expression => { skip_expr(pair) }
        Rule::or_expression => { parse_binop(pair, Expr::BoolOr) }
        Rule::plus_expression => { parse_binop(pair, Expr::NaturalPlus) }
        Rule::text_append_expression => { parse_binop(pair, Expr::TextAppend) }
        Rule::list_append_expression => { skip_expr(pair) }
        Rule::and_expression => { parse_binop(pair, Expr::BoolAnd) }
        Rule::combine_expression => { skip_expr(pair) }
        Rule::prefer_expression => { skip_expr(pair) }
        Rule::combine_types_expression => { skip_expr(pair) }
        Rule::times_expression => { parse_binop(pair, Expr::NaturalTimes) }
        Rule::equal_expression => { parse_binop(pair, Expr::BoolEQ) }
        Rule::not_equal_expression => { parse_binop(pair, Expr::BoolNE) }
        Rule::application_expression => { parse_binop(pair, Expr::App) }

        Rule::selector_expression_raw =>
            parse!(pair; (first: expression, rest*: str) => {
                rest.fold_results(first, |acc, e| bx(Expr::Field(acc, e)))?
            }),

        Rule::empty_record_type => Ok(bx(Expr::Record(BTreeMap::new()))),
        Rule::empty_record_literal => Ok(bx(Expr::RecordLit(BTreeMap::new()))),
        Rule::non_empty_record_type_or_literal =>
            parse!(pair; (first_label: str, rest: partial_record_entries) => {
                let (rule, first_expr, mut map) = rest;
                map.insert(first_label, *first_expr);
                match rule {
                    Rule::non_empty_record_type => bx(Expr::Record(map)),
                    Rule::non_empty_record_literal => bx(Expr::RecordLit(map)),
                    _ => unreachable!()
                }
            }),


        _ => {
            // panic!();
            let rulename = format!("{:?}", pair.as_rule());
            parse!(pair; (exprs*: expression) => {
                bx(Expr::FailedParse(rulename, exprs.map_results(|x| *x).collect::<ParseResult<_>>()?))
            })
        }
    }
}

pub fn parse_expr_pest(s: &str) -> ParseResult<BoxExpr>  {
    let parsed_expr = DhallParser::parse(Rule::final_expression, s)?.next().unwrap();

    parse_expression(parsed_expr)
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
    assert_eq!(parse_expr_pest(expr).unwrap(), parse_expr_lalrpop(expr).unwrap());
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
