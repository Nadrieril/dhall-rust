use lalrpop_util;

use crate::grammar;
use crate::grammar_util::BoxExpr;
use crate::lexer::{Lexer, LexicalError, Tok};

pub type ParseError<'i> = lalrpop_util::ParseError<usize, Tok<'i>, LexicalError>;

pub fn parse_expr(s: &str) -> Result<BoxExpr, ParseError>  {
    grammar::ExprParser::new().parse(Lexer::new(s))
}

#[test]
fn test_parse() {
    use crate::core::Expr::*;
    println!("test {:?}", parse_expr("+3 + +5 * +10"));
    assert!(parse_expr("22").is_ok());
    assert!(parse_expr("(22)").is_ok());
    assert_eq!(parse_expr("+3 + +5 * +10").ok(),
               Some(Box::new(NaturalPlus(Box::new(NaturalLit(3)),
                                Box::new(NaturalTimes(Box::new(NaturalLit(5)),
                                                      Box::new(NaturalLit(10))))))));
    // The original parser is apparently right-associative
    assert_eq!(parse_expr("+2 * +3 * +4").ok(),
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
}
