#![feature(box_patterns)]

use bytecount;
use lalrpop_util;
use lalrpop_util::lalrpop_mod;
use term_painter;

pub mod context;
mod core;
pub use crate::core::*;
lalrpop_mod!(pub grammar); // synthesized by LALRPOP
mod grammar_util;
pub mod lexer;
pub mod parser;
pub mod typecheck;

use std::io::{self, Read};
use std::error::Error;

use term_painter::ToStyle;

const ERROR_STYLE: term_painter::Color = term_painter::Color::Red;
const BOLD: term_painter::Attr = term_painter::Attr::Bold;

fn print_error(message: &str, source: &str, start: usize, end: usize) {
    let line_number = bytecount::count(source[..start].as_bytes(), b'\n');
    let line_start = source[..start].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let line_end = source[end..].find('\n').unwrap_or(0) + end;
    let context_prefix = &source[line_start..start];
    let context_highlighted = &source[start..end];
    let context_suffix = &source[end..line_end];

    let line_number_str = line_number.to_string();
    let line_number_width = line_number_str.len();

    BOLD.with(|| {
        ERROR_STYLE.with(|| {
            print!("error: ");
        });
        println!("{}", message);
    });
    BOLD.with(|| {
        print!("  -->");
    });
    println!(" {}:{}:0", "(stdin)", line_number);
    BOLD.with(|| {
        println!("{:w$} |", "", w = line_number_width);
        print!("{} |", line_number_str);
    });
    print!(" {}", context_prefix);
    BOLD.with(|| {
        ERROR_STYLE.with(|| {
            print!("{}", context_highlighted);
        });
    });
    println!("{}", context_suffix);
    BOLD.with(|| {
        print!("{:w$} |", "", w = line_number_width);
        ERROR_STYLE.with(|| {
            println!(" {:so$}{:^>ew$}", "", "",
                     so = source[line_start..start].chars().count(),
                     ew = ::std::cmp::max(1, source[start..end].chars().count()));
        });
    });
}

fn main() {
    let mut buffer = String::new();
    io::stdin().read_to_string(&mut buffer).unwrap();
    let expr = match parser::parse_expr(&buffer) {
        Ok(e) => e,
        Err(lalrpop_util::ParseError::User { error: lexer::LexicalError::Error(pos, e) }) => {
            print_error(&format!("Unexpected token {:?}", e), &buffer, pos, pos);
            return;
        }
        Err(lalrpop_util::ParseError::UnrecognizedToken { token: Some((start, t, end)), expected: e }) => {
            print_error(&format!("Unrecognized token {:?}", t), &buffer, start, end);
            if !e.is_empty() {
                println!("Expected {:?}", e);
            }
            return;
        }
        Err(e) => {
            print_error(&format!("Parser error {:?}", e), &buffer, 0, 0);
            return;
        }
    };

    /*
    expr' <- load expr
    */

    let type_expr = match typecheck::type_of(&expr) {
        Err(e) => {
            let explain = ::std::env::args().any(|s| s == "--explain");
            if !explain {
                term_painter::Color::BrightBlack.with(|| {
                    println!("Use \"dhall --explain\" for detailed errors");
                });
            }
            ERROR_STYLE.with(|| print!("Error: "));
            println!("{}", e.type_message.description());
            if explain {
                println!("{}", e.type_message);
            }
            println!("{}", e.current);
            // FIXME Print source position
            return;
        }
        Ok(type_expr) => type_expr,
    };

    println!("{}", type_expr);
    println!("");
    println!("{}", normalize::<_, X, _>(&expr));
}
