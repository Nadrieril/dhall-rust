use nom;

use std::str::FromStr;

use core::Const;

#[derive(Debug, PartialEq, Eq)]
pub enum Keyword {
    Let,
    In,
    If,
    Then,
    Else,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ListLike {
    List,
    Optional,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Builtin {
    Natural,
    NaturalFold,
    NaturalBuild,
    NaturalIsZero,
    NaturalEven,
    NaturalOdd,
    Integer,
    Double,
    Text,
    ListBuild,
    ListFold,
    ListLength,
    ListHead,
    ListLast,
    ListIndexed,
    ListReverse,
    OptionalFold,
    Bool,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Tok {
    Identifier(String),
    Keyword(Keyword),
    Builtin(Builtin),
    ListLike(ListLike),
    Const(Const),
    Bool(bool),
    Integer(isize),
    Natural(usize),

    // Symbols
    BraceL,
    BraceR,
    BracketL,
    BracketR,
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
    Comma,
    Dot,
    Ascription,
    Equals,
}

#[derive(Debug)]
pub enum LexicalError {
    Error(usize, nom::simple_errors::Err<u32>),
    Incomplete(nom::Needed),
}

pub type Spanned<Tok, Loc, Error> = Result<(Loc, Tok, Loc), Error>;

#[allow(dead_code)]
fn is_identifier_first_char(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}

fn is_identifier_rest_char(c: char) -> bool {
    c.is_alphabetic() || is_decimal(c) || c == '_' || c == '/'
}

fn is_decimal(c: char) -> bool {
    c.is_digit(10)
}

named!(identifier<&str, &str>, take_while1_s!(is_identifier_rest_char)); // FIXME use is_identifier_first_char
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

/// Parse an identifier, ensuring a whole identifier is parsed and not just a prefix.
macro_rules! ident_tag {
    ($i:expr, $tag:expr) => {
        match identifier($i) {
            nom::IResult::Done(i, s) => {
                if s == $tag {
                    nom::IResult::Done(i, s)
                } else {
                    nom::IResult::Error(error_position!(nom::ErrorKind::Tag, $i))
                }
            }
            r => r,
        }
    }
}

named!(keyword<&str, Keyword>, alt!(
    value!(Keyword::Let, ident_tag!("let")) |
    value!(Keyword::In, ident_tag!("in")) |
    value!(Keyword::If, ident_tag!("if")) |
    value!(Keyword::Then, ident_tag!("then")) |
    value!(Keyword::Else, ident_tag!("else"))
));

named!(type_const<&str, Const>, alt!(
    value!(Const::Type, ident_tag!("Type")) |
    value!(Const::Kind, ident_tag!("Kind"))
));

named!(list_like<&str, ListLike>, alt!(
    value!(ListLike::List, ident_tag!("List")) |
    value!(ListLike::Optional, ident_tag!("Optional"))
));

named!(builtin<&str, Builtin>, alt!(
    value!(Builtin::NaturalFold, ident_tag!("Natural/fold")) |
    value!(Builtin::NaturalBuild, ident_tag!("Natural/build")) |
    value!(Builtin::NaturalIsZero, ident_tag!("Natural/isZero")) |
    value!(Builtin::NaturalEven, ident_tag!("Natural/even")) |
    value!(Builtin::NaturalOdd, ident_tag!("Natural/odd")) |
    value!(Builtin::Natural, ident_tag!("Natural")) |
    value!(Builtin::Integer, ident_tag!("Integer")) |
    value!(Builtin::Double, ident_tag!("Double")) |
    value!(Builtin::Text, ident_tag!("Text")) |
    value!(Builtin::ListBuild, ident_tag!("List/build")) |
    value!(Builtin::ListFold, ident_tag!("List/fold")) |
    value!(Builtin::ListLength, ident_tag!("List/length")) |
    value!(Builtin::ListHead, ident_tag!("List/head")) |
    value!(Builtin::ListLast, ident_tag!("List/last")) |
    value!(Builtin::ListIndexed, ident_tag!("List/indexed")) |
    value!(Builtin::ListReverse, ident_tag!("List/reverse")) |
    value!(Builtin::OptionalFold, ident_tag!("Optional/fold")) |
    value!(Builtin::Bool, ident_tag!("Bool"))
));

named!(token<&str, Tok>, alt!(
    value!(Tok::Pi, ident_tag!("forall")) |
    value!(Tok::Pi, tag!("∀")) |
    value!(Tok::Lambda, tag!("\\")) |
    value!(Tok::Lambda, tag!("λ")) |
    value!(Tok::Combine, tag!("/\\")) |
    value!(Tok::Combine, tag!("∧")) |
    value!(Tok::Arrow, tag!("->")) |
    value!(Tok::Arrow, tag!("→")) |

    map!(type_const, Tok::Const) |
    map!(boolean, Tok::Bool) |
    map!(keyword, Tok::Keyword) |
    map!(builtin, Tok::Builtin) |
    map!(list_like, Tok::ListLike) |
    map_opt!(natural, |s| usize::from_str(s).ok().map(|n| Tok::Natural(n))) |
    map!(integer, Tok::Integer) |
    map!(identifier, |s: &str| Tok::Identifier(s.to_owned())) |

    value!(Tok::BraceL, tag!("{")) |
    value!(Tok::BraceR, tag!("}")) |
    value!(Tok::BracketL, tag!("[")) |
    value!(Tok::BracketR, tag!("]")) |
    value!(Tok::ParenL, tag!("(")) |
    value!(Tok::ParenR, tag!(")")) |
    value!(Tok::BoolAnd, tag!("&&")) |
    value!(Tok::BoolOr, tag!("||")) |
    value!(Tok::CompareEQ, tag!("==")) |
    value!(Tok::CompareNE, tag!("!=")) |
    value!(Tok::Append, tag!("++")) |
    value!(Tok::Times, tag!("*")) |
    value!(Tok::Plus, tag!("+")) |
    value!(Tok::Comma, tag!(",")) |
    value!(Tok::Dot, tag!(".")) |
    value!(Tok::Ascription, tag!(":")) |
    value!(Tok::Equals, tag!("="))
));

fn find_end(input: &str, ending: &str) -> Option<usize> {
    input.find(ending).map(|i| i + ending.len())
}

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

    fn skip_whitespace(&mut self) -> bool {
        let input = self.current_input();
        let trimmed = input.trim_left();
        let whitespace_len = input.len() - trimmed.len();
        let skipped = whitespace_len > 0;
        if skipped {
            // println!("skipped {} whitespace bytes in {}..{}", whitespace_len, self.offset, self.offset + whitespace_len);
            self.offset += whitespace_len;
        }
        skipped
    }

    fn skip_comments(&mut self) -> bool {
        let input = self.current_input();
        if !input.is_char_boundary(0) || !input.is_char_boundary(2) {
            return false;
        }
        let skip = match &input[0..2] {
            "{-" => find_end(input, "-}"),
            "--" => find_end(input, "\n"), // Also skips past \r\n (CRLF)
            _ => None,
        }.unwrap_or(0);
        // println!("skipped {} bytes of comment", skip);
        self.offset += skip;
        skip != 0
    }

    fn skip_comments_and_whitespace(&mut self) {
        while self.skip_whitespace() || self.skip_comments() {}
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Spanned<Tok, usize, LexicalError>;

    fn next(&mut self) -> Option<Self::Item> {
        use nom::IResult::*;
        self.skip_comments_and_whitespace();
        let input = self.current_input();
        if input.len() == 0 {
            return None;
        }
        match token(input) {
            Done(rest, t) => {
                let parsed_len = input.len() - rest.len();
                //println!("parsed {} bytes => {:?}", parsed_len, t);
                let start = self.offset;
                self.offset += parsed_len;
                Some(Ok((start, t, self.offset)))
            }
            Error(e) => {
                let offset = self.offset;
                self.offset = self.input.len();
                Some(Err(LexicalError::Error(offset, e)))
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
                    Builtin(self::Builtin::Bool),
                    ParenR,
                    Arrow,
                    Identifier("b".to_owned()),
                    CompareEQ,
                    Bool(false)];
    let lexer = Lexer::new(s);
    let tokens = lexer.map(|r| r.unwrap().1).collect::<Vec<_>>();
    assert_eq!(&tokens, &expected);
}
