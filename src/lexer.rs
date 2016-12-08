use nom;

use core::Const;
use core::BuiltinType;
use core::BuiltinType::*;
use core::BuiltinValue;
use core::BuiltinValue::*;

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
    Type(BuiltinType),
    Value(BuiltinValue),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Tok<'i> {
    Identifier(&'i str),
    Keyword(Keyword),
    Builtin(Builtin),
    ListLike(ListLike),
    Const(Const),
    Bool(bool),
    Integer(isize),
    Natural(usize),
    Text(String),

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
    is_identifier_first_char(c) || c.is_digit(10) || c == '/'
}

macro_rules! digits {
    ($i:expr, $t:tt, $radix:expr) => {{
        let r: nom::IResult<&str, $t> =
            map_res!($i, take_while1_s!(call!(|c: char| c.is_digit($radix))),
                     |s| $t::from_str_radix(s, $radix));
        r
    }}
}

named!(natural<&str, usize>, preceded!(tag!("+"), digits!(usize, 10)));
named!(integral<&str, isize>, digits!(isize, 10));
named!(integer<&str, isize>, alt!(
    preceded!(tag!("-"), map!(integral, |i: isize| -i)) |
    integral
));
named!(boolean<&str, bool>, alt!(
    value!(true, tag!("True")) |
    value!(false, tag!("False"))
));

named!(identifier<&str, &str>, recognize!(preceded!(
    take_while1_s!(is_identifier_first_char),
    take_while_s!(is_identifier_rest_char))
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

fn string_escape_single(c: char) -> Option<&'static str> {
    match c {
        'n'  => Some("\n"),
        'r'  => Some("\r"),
        't'  => Some("\t"),
        '"'  => Some("\""),
        '\'' => Some("'"),
        '\\' => Some("\\"),
        '0'  => Some("\0"),
        'a'  => Some("\x07"),
        'b'  => Some("\x08"),
        'f'  => Some("\x0c"),
        'v'  => Some("\x0b"),
        '&'  => Some(""),
        _    => None,
    }
}

named!(string_escape_numeric<&str, char>, map_opt!(alt!(
    preceded!(tag!("x"), digits!(u32, 16)) |
    preceded!(tag!("o"), digits!(u32, 8)) |
    digits!(u32, 10)
), ::std::char::from_u32));

fn string_lit_inner(input: &str) -> nom::IResult<&str, String> {
    use nom::IResult::*;;
    use nom::ErrorKind;
    let mut s = String::new();
    let mut cs = input.char_indices().peekable();
    while let Some((i, c)) = cs.next()  {
        match c {
            '"' => return nom::IResult::Done(&input[i..], s),
            '\\' => match cs.next() {
                Some((_, s)) if s.is_whitespace() => {
                    while cs.peek().map(|&(_, s)| s.is_whitespace()) == Some(true) {
                        let _ = cs.next();
                    }
                    if cs.next().map(|p| p.1) != Some('\\') {
                        return Error(error_position!(ErrorKind::Custom(4 /* FIXME */), input));
                    }
                }
                Some((j, ec)) => {
                    if let Some(esc) = string_escape_single(ec) {
                        s.push_str(esc);
                        // FIXME Named ASCII escapes and control character escapes
                    } else {
                        match string_escape_numeric(&input[j..]) {
                            Done(rest, esc) => {
                                let &(k, _) = cs.peek().unwrap();
                                // digits are always single byte ASCII characters
                                let consumed = input[k..].len() - rest.len();
                                for _ in 0..consumed { let _ = cs.next(); }
                                s.push(esc);
                            }
                            Incomplete(s) => return Incomplete(s),
                            Error(e) => return Error(e),
                        }
                    }
                },
                _ => return Error(error_position!(ErrorKind::Custom(5 /* FIXME */), input)),
            },
            _ => s.push(c),
        }
    }
    Error(error_position!(ErrorKind::Custom(3 /* FIXME */), input))
}

named!(string_lit<&str, String>, delimited!(tag!("\""), string_lit_inner, tag!("\"")));

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
    value!(Builtin::Value(NaturalFold), ident_tag!("Natural/fold")) |
    value!(Builtin::Value(NaturalBuild), ident_tag!("Natural/build")) |
    value!(Builtin::Value(NaturalIsZero), ident_tag!("Natural/isZero")) |
    value!(Builtin::Value(NaturalEven), ident_tag!("Natural/even")) |
    value!(Builtin::Value(NaturalOdd), ident_tag!("Natural/odd")) |
    value!(Builtin::Type(Natural), ident_tag!("Natural")) |
    value!(Builtin::Type(Integer), ident_tag!("Integer")) |
    value!(Builtin::Type(Double), ident_tag!("Double")) |
    value!(Builtin::Type(Text), ident_tag!("Text")) |
    value!(Builtin::Value(ListBuild), ident_tag!("List/build")) |
    value!(Builtin::Value(ListFold), ident_tag!("List/fold")) |
    value!(Builtin::Value(ListLength), ident_tag!("List/length")) |
    value!(Builtin::Value(ListHead), ident_tag!("List/head")) |
    value!(Builtin::Value(ListLast), ident_tag!("List/last")) |
    value!(Builtin::Value(ListIndexed), ident_tag!("List/indexed")) |
    value!(Builtin::Value(ListReverse), ident_tag!("List/reverse")) |
    value!(Builtin::Value(OptionalFold), ident_tag!("Optional/fold")) |
    value!(Builtin::Type(Bool), ident_tag!("Bool"))
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
    map!(natural, Tok::Natural) |
    map!(integer, Tok::Integer) |
    map!(identifier, Tok::Identifier) |
    map!(string_lit, Tok::Text) |

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
    type Item = Spanned<Tok<'input>, usize, LexicalError>;

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
                    Identifier("b"),
                    Ascription,
                    Builtin(self::Builtin::Type(::core::BuiltinType::Bool)),
                    ParenR,
                    Arrow,
                    Identifier("b"),
                    CompareEQ,
                    Bool(false)];
    let lexer = Lexer::new(s);
    let tokens = lexer.map(|r| r.unwrap().1).collect::<Vec<_>>();
    assert_eq!(&tokens, &expected);

    assert_eq!(string_lit(r#""a\&b""#).to_result(), Ok("ab".to_owned()));
    assert_eq!(string_lit(r#""a\     \b""#).to_result(), Ok("ab".to_owned()));
    assert!(string_lit(r#""a\     b""#).is_err());
    assert_eq!(string_lit(r#""a\nb""#).to_result(), Ok("a\nb".to_owned()));
    assert_eq!(string_lit(r#""\o141\x62\99""#).to_result(), Ok("abc".to_owned()));
}
