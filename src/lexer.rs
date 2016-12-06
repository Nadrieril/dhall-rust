use nom;

use std::str::FromStr;

#[derive(Debug, PartialEq, Eq)]
pub enum Keyword {
    Natural,
    NaturalFold,
    NaturalBuild,
    NaturalIsZero,
    NaturalEven,
    NaturalOdd,
    Integer,
    Double,
    Text,
    List,
    ListBuild,
    ListFold,
    ListLength,
    ListHead,
    ListLast,
    ListIndexed,
    ListReverse,
    Optional,
    OptionalFold,
    Bool,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Tok {
    Identifier(String),
    Reserved(Keyword),
    Bool(bool),
    Integer(isize),
    Natural(usize),

    // Symbols
    ParenL,
    ParenR,
    Arrow,
    Lambda,
    Pi,
    Combine,
    BoolAnd,
    BoolOr,
    CompareEQ,
    CompareNE,
    Append,
    Times,
    Plus,
    Dot,
    Ascription,
    Equals,
}

#[derive(Debug)]
pub enum LexicalError {
    Error(nom::simple_errors::Err<u32>),
    Incomplete(nom::Needed),
}

pub type Spanned<Tok, Loc, Error> = Result<(Loc, Tok, Loc), Error>;

/*
macro_rules! one_of_chars {
    ($c:expr, [$($cs:pat),*]) => {
        match $c {
            $($cs => true),*,
            _ => false,
        }
    }
}

fn is_symbol(c: char) -> bool {
    one_of_chars!(c, [
        '!',
        '&',
        '(',
        ')',
        '*',
        '+',
        '-',
        '/',
        ':',
        '=',
        '>',
        '\\',
        '|',
        '∧',
        'λ'
    ])
}
named!(symbol<&str, &str>, take_while1_s!(is_symbol));
*/

fn is_decimal(c: char) -> bool {
    c.is_digit(10)
}

named!(identifier<&str, &str>, take_while1_s!(char::is_alphabetic)); // FIXME [A-Za-z_][A-Za-z0-9_/]*
named!(natural<&str, &str>, preceded!(tag!("+"), take_while1_s!(is_decimal)));
named!(integral<&str, isize>, map_res!(take_while1_s!(is_decimal), |s| isize::from_str(s)));
named!(integer<&str, isize>, alt!(
    preceded!(tag!("-"), map!(integral, |i: isize| -i)) |
    integral
));
named!(boolean<&str, bool>, alt!(
    value!(true, tag!("True")) |
    value!(false, tag!("False"))
));

named!(keyword<&str, Keyword>, alt!(
    value!(Keyword::Natural, tag!("Natural")) |
    value!(Keyword::NaturalFold, tag!("Natural/fold")) |
    value!(Keyword::NaturalBuild, tag!("Natural/build")) |
    value!(Keyword::NaturalIsZero, tag!("Natural/isZero")) |
    value!(Keyword::NaturalEven, tag!("Natural/even")) |
    value!(Keyword::NaturalOdd, tag!("Natural/odd")) |
    value!(Keyword::Integer, tag!("Integer")) |
    value!(Keyword::Double, tag!("Double")) |
    value!(Keyword::Text, tag!("Text")) |
    value!(Keyword::List, tag!("List")) |
    value!(Keyword::ListBuild, tag!("List/build")) |
    value!(Keyword::ListFold, tag!("List/fold")) |
    value!(Keyword::ListLength, tag!("List/length")) |
    value!(Keyword::ListHead, tag!("List/head")) |
    value!(Keyword::ListLast, tag!("List/last")) |
    value!(Keyword::ListIndexed, tag!("List/indexed")) |
    value!(Keyword::ListReverse, tag!("List/reverse")) |
    value!(Keyword::Optional, tag!("Optional")) |
    value!(Keyword::OptionalFold, tag!("Optional/fold")) |
    value!(Keyword::Bool, tag!("Bool"))
));

named!(token<&str, Tok>, alt!(
    value!(Tok::Pi, tag!("forall")) |
    value!(Tok::Pi, tag!("∀")) |
    value!(Tok::Lambda, tag!("\\")) |
    value!(Tok::Lambda, tag!("λ")) |
    value!(Tok::Combine, tag!("/\\")) |
    value!(Tok::Combine, tag!("∧")) |
    value!(Tok::Arrow, tag!("->")) |
    value!(Tok::Arrow, tag!("→")) |

    map!(boolean, Tok::Bool) |
    map!(keyword, Tok::Reserved) |
    map_opt!(natural, |s| usize::from_str(s).ok().map(|n| Tok::Natural(n))) |
    map!(integer, Tok::Integer) |
    map!(identifier, |s: &str| Tok::Identifier(s.to_owned())) |

    value!(Tok::ParenL, tag!("(")) |
    value!(Tok::ParenR, tag!(")")) |
    value!(Tok::BoolAnd, tag!("&&")) |
    value!(Tok::BoolOr, tag!("||")) |
    value!(Tok::CompareEQ, tag!("==")) |
    value!(Tok::CompareNE, tag!("!=")) |
    value!(Tok::Append, tag!("++")) |
    value!(Tok::Times, tag!("*")) |
    value!(Tok::Plus, tag!("+")) |
    value!(Tok::Dot, tag!(".")) |
    value!(Tok::Ascription, tag!(":")) |
    value!(Tok::Equals, tag!("="))
));

pub struct Lexer<'input> {
    input: &'input str,
    offset: usize,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Lexer {
            input: input,
            offset: 0,
        }
    }

    fn current_input(&mut self) -> &'input str {
        &self.input[self.offset..]
    }

    fn skip_whitespace(&mut self) {
        let input = self.current_input();
        let trimmed = input.trim_left();
        let whitespace_len = input.len() - trimmed.len();
        if whitespace_len > 0 {
            //println!("skipped {} whitespace bytes", whitespace_len);
            self.offset += whitespace_len;
        }
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Spanned<Tok, usize, LexicalError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.offset >= self.input.len() {
            return None;
        }

        use nom::IResult::*;
        self.skip_whitespace();
        let input = self.current_input();
        match token(input) {
            Done(rest, t) => {
                let parsed_len = input.len() - rest.len();
                //println!("parsed {} bytes => {:?}", parsed_len, t);
                let start = self.offset;
                self.offset += parsed_len;
                Some(Ok((start, t, self.offset)))
            }
            Error(e) => {
                self.offset = self.input.len();
                Some(Err(LexicalError::Error(e)))
            }
            Incomplete(needed) => {
                Some(Err(LexicalError::Incomplete(needed)))
            }
        }
    }
}

#[test]
fn test_lex() {
    use self::Tok::*;
    let s = "λ(b : Bool) → b == False";
    let expected = [Lambda,
                    ParenL,
                    Identifier("b".to_owned()),
                    Ascription,
                    Reserved(Keyword::Bool),
                    ParenR,
                    Arrow,
                    Identifier("b".to_owned()),
                    CompareEQ,
                    Bool(false)];
    let lexer = Lexer::new(s);
    let tokens = lexer.map(|r| r.unwrap().1).collect::<Vec<_>>();
    assert_eq!(&tokens, &expected);
}
