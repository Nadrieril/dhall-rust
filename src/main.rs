extern crate bytecount;
extern crate lalrpop_util;
#[macro_use]
extern crate nom;

mod core;
pub use core::*;
pub mod grammar;
mod grammar_util;
pub mod lexer;
pub mod parser;

use std::io::{self, Read};

fn print_error(message: &str, source: &str, start: usize, end: usize) {
    let line_number = bytecount::count(source[..start].as_bytes(), '\n' as u8);
    let line_start = source[..start].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let line_end = source[end..].find('\n').unwrap_or(0) + end;
    let context = &source[line_start..line_end];

    println!("error: {}", message);
    println!("  --> (stdin):{}:0", line_number);
    let line_number_str = line_number.to_string();
    let line_number_width = line_number_str.len();
    println!("{:w$} |", "", w = line_number_width);
    println!("{} | {}", line_number_str, context);
    println!("{:w$} | {:so$}{:^>ew$}", "", "", "",
             w = line_number_width,
             so = source[line_start..start].chars().count(),
             ew = ::std::cmp::max(1, source[start..end].chars().count()));
}

fn main() {
    let mut buffer = String::new();
    io::stdin().read_to_string(&mut buffer).unwrap();
    match parser::parse_expr(&buffer) {
        Ok(e) => println!("{:?}", e),
        Err(lalrpop_util::ParseError::User { error: lexer::LexicalError::Error(pos, e) }) => {
            print_error(&format!("Unexpected token {:?}", e), &buffer, pos, pos);
        }
        Err(lalrpop_util::ParseError::UnrecognizedToken { token: Some((start, t, end)), expected: e }) => {
            print_error(&format!("Unrecognized token {:?}", t), &buffer, start, end);
            if e.len() > 0 {
                println!("Expected {:?}", e);
            }
        }
        Err(e) => {
            print_error(&format!("Parser error {:?}", e), &buffer, 0, 0);
        }
    }

    /*
    expr <- case exprFromText (Directed "(stdin)" 0 0 0 0) inText of
        Left  err  -> Control.Exception.throwIO err
        Right expr -> return expr

    expr' <- load expr

    typeExpr <- case Dhall.TypeCheck.typeOf expr' of
        Left  err      -> Control.Exception.throwIO err
        Right typeExpr -> return typeExpr
    Data.Text.Lazy.IO.hPutStrLn stderr (pretty (normalize typeExpr))
    Data.Text.Lazy.IO.hPutStrLn stderr mempty
    Data.Text.Lazy.IO.putStrLn (pretty (normalize expr')) )
    */
}
