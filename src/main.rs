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
    let r = parser::parse_expr(&buffer);
    println!("{:?}", r);

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
