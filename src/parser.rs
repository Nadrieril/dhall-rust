use lalrpop_util;

use crate::grammar;
use crate::grammar_util::BoxExpr;
use crate::lexer::{Lexer, LexicalError, Tok};
use crate::core::{bx, Expr};

pub type ParseError<'i> = lalrpop_util::ParseError<usize, Tok<'i>, LexicalError>;

pub fn parse_expr(s: &str) -> Result<BoxExpr, ParseError>  {
    grammar::ExprParser::new().parse(Lexer::new(s))
}

use pest::Parser;
use pest::error::Error;
use pest_derive::*;

#[derive(Parser)]
#[grammar = "dhall.pest"]
struct DhallParser;

use pest::iterators::Pair;
fn debug_pair(pair: Pair<Rule>) {
    fn aux(indent: usize, pair: Pair<Rule>) {
        let indent_str = "| ".repeat(indent);
        println!(r#"{}{:?}: "{}""#, indent_str, pair.as_rule(), pair.as_str());
        for p in pair.into_inner() {
            aux(indent+1, p);
        }
    }
    aux(0, pair)
}

pub fn parse_expr_pest(s: &str) -> Result<BoxExpr, Error<Rule>>  {
    let parsed_expr = DhallParser::parse(Rule::complete_expression, s)?.next().unwrap();
    debug_pair(parsed_expr.clone());
    // println!("{}", parsed_expr.clone());

    fn parse_pair(pair: Pair<Rule>) -> BoxExpr {
        match pair.as_rule() {
            Rule::natural_literal => bx(Expr::NaturalLit(str::parse(pair.as_str().trim()).unwrap())),
            Rule::plus_expression => {
                let mut inner = pair.into_inner().map(parse_pair);
                let first_expr = inner.next().unwrap();
                inner.fold(first_expr, |acc, e| bx(Expr::NaturalPlus(acc, e)))
            }
            Rule::times_expression => {
                let mut inner = pair.into_inner().map(parse_pair);
                let first_expr = inner.next().unwrap();
                inner.fold(first_expr, |acc, e| bx(Expr::NaturalTimes(acc, e)))
            }
            r => panic!("{:?}", r),
        }
    }

    Ok(parse_pair(parsed_expr))
}


#[test]
fn test_parse() {
    use crate::core::Expr::*;
    let expr = "((22 + 3) * 10)";
    match parse_expr_pest(expr) {
        Err(e) => println!("{}", e),
        ok => println!("{:?}", ok),
    }
    println!("{:?}", parse_expr(expr));
    assert_eq!(parse_expr_pest(expr).unwrap(), parse_expr(expr).unwrap());
    assert!(false);

    println!("test {:?}", parse_expr("3 + 5 * 10"));
    assert!(parse_expr("22").is_ok());
    assert!(parse_expr("(22)").is_ok());
    assert_eq!(parse_expr("3 + 5 * 10").ok(),
               Some(Box::new(NaturalPlus(Box::new(NaturalLit(3)),
                                Box::new(NaturalTimes(Box::new(NaturalLit(5)),
                                                      Box::new(NaturalLit(10))))))));
    // The original parser is apparently right-associative
    assert_eq!(parse_expr("2 * 3 * 4").ok(),
               Some(Box::new(NaturalTimes(Box::new(NaturalLit(2)),
                                 Box::new(NaturalTimes(Box::new(NaturalLit(3)),
                                                       Box::new(NaturalLit(4))))))));
    assert!(parse_expr("((((22))))").is_ok());
    assert!(parse_expr("((22)").is_err());
    println!("{:?}", parse_expr("\\(b : Bool) -> b == False"));
    assert!(parse_expr("\\(b : Bool) -> b == False").is_ok());
    println!("{:?}", parse_expr("foo.bar"));
    assert!(parse_expr("foo.bar").is_ok());
    assert!(parse_expr("[] : List Bool").is_ok());

    // println!("{:?}", parse_expr("< Left = True | Right : Natural >"));
    // println!("{:?}", parse_expr(r#""bl${42}ah""#));
    // assert!(parse_expr("< Left = True | Right : Natural >").is_ok());
}
