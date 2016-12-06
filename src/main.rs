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

fn main() {
    let mut buffer = String::new();
    io::stdin().read_to_string(&mut buffer).unwrap();
    match parser::parse_expr(&buffer) {
        Ok(e) => println!("{:?}", e),
        Err(lalrpop_util::ParseError::User { error: lexer::LexicalError::Error(pos, e) }) => {
            let context = &buffer[pos..::std::cmp::min(buffer.len(), pos + 20)];
            println!("Unexpected token in {:?}: {:?}...", e, context);
        }
        Err(e) => println!("{:?}", e),
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
