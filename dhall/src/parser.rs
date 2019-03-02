use lalrpop_util;

use crate::grammar;
use crate::grammar_util::{BoxExpr, ParsedExpr};
use crate::lexer::{Lexer, LexicalError, Tok};
use crate::core::{bx, Expr, V};

pub type ParseError<'i> = lalrpop_util::ParseError<usize, Tok<'i>, LexicalError>;

pub fn parse_expr(s: &str) -> Result<BoxExpr, ParseError>  {
    grammar::ExprParser::new().parse(Lexer::new(s))
}

use pest::Parser;
use pest::error::Error;
use pest::iterators::Pair;
use dhall_parser::{DhallParser, Rule};

fn debug_pair(pair: Pair<Rule>) {
    fn aux(indent: usize, prefix: String, pair: Pair<Rule>) {
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
                    aux(indent, prefix, p);
                    continue;
                } else {
                    println!(r#"{}{}{:?}: "{}""#, indent_str, prefix, rule, contents);
                }
            }
            aux(indent+1, "".into(), p);
        }
        if first {
            println!(r#"{}{}{:?}: "{}""#, indent_str, prefix, rule, contents);
        }
        // println!(r#"{}{}{:?}: "{}""#, indent_str, prefix, rule, contents);
        // for p in inner {
        //     aux(indent+1, "".into(), p);
        // }
    }
    aux(0, "".into(), pair)
}

pub fn parse_expr_pest(s: &str) -> Result<BoxExpr, Error<Rule>>  {
    let parsed_expr = DhallParser::parse(Rule::final_expression, s)?.next().unwrap();
    debug_pair(parsed_expr.clone());
    // println!("{}", parsed_expr.clone());

    fn parse_binop<'a, F>(pair: Pair<'a, Rule>, mut f: F) -> BoxExpr<'a>
    where F: FnMut(BoxExpr<'a>, BoxExpr<'a>) -> ParsedExpr<'a> {
        let mut inner = pair.into_inner().map(parse_expression);
        let first_expr = inner.next().unwrap();
        inner.fold(first_expr, |acc, e| bx(f(acc, e)))
    }

    fn skip_expr(pair: Pair<Rule>) -> BoxExpr {
        let mut inner = pair.into_inner().map(parse_expression);
        inner.next().unwrap()
    }

    fn parse_str(pair: Pair<Rule>) -> &str {
        pair.as_str().trim()
    }

    fn parse_natural(pair: Pair<Rule>) -> Result<usize, std::num::ParseIntError> {
        parse_str(pair).parse()
    }

    fn parse_expression(pair: Pair<Rule>) -> BoxExpr {
        match pair.as_rule() {
            Rule::natural_literal_raw => bx(Expr::NaturalLit(parse_natural(pair).unwrap())),

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

            Rule::selector_expression_raw => {
                let mut inner = pair.into_inner();
                let first_expr = parse_expression(inner.next().unwrap());
                inner.fold(first_expr, |acc, e| bx(Expr::Field(acc, e.as_str())))
            }

            Rule::identifier_raw => {
                let mut inner = pair.into_inner();
                let name = parse_str(inner.next().unwrap());
                let idx = inner.next().map(parse_natural).unwrap_or(Ok(0)).unwrap();
                bx(Expr::Var(V(name, idx)))
            }


            // Rule::record_type_or_literal => {
            //     let mut inner = pair.into_inner();
            //     let first_expr = parse_expression(inner.next().unwrap());
            //     inner.fold(first_expr, |acc, e| bx(Expr::Field(acc, e.as_str())))
            // }

            // r => panic!("{:?}", r),
            // _ => bx(Expr::BoolLit(false)),

            _ => {
                let rulename = format!("{:?}", pair.as_rule());
                let mut inner = pair.into_inner().map(parse_expression).map(|x| *x);
                bx(Expr::FailedParse(rulename, inner.collect()))
            }
        }
    }

    Ok(parse_expression(parsed_expr))
}


#[test]
fn test_parse() {
    use crate::core::Expr::*;
    // let expr = r#"{ x = "foo", y = 4 }.x"#;
    // let expr = r#"(1 + 2) * 3"#;
    let expr = r#"if True then 1 + 3 * 5 else 2"#;
    println!("{:?}", parse_expr(expr));
    match parse_expr_pest(expr) {
        Err(e) => {
            println!("{:?}", e);
            println!("{}", e);
        },
        ok => println!("{:?}", ok),
    }
    // assert_eq!(parse_expr_pest(expr).unwrap(), parse_expr(expr).unwrap());
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
