#[allow(unused_imports)]
use pest_derive::*;

#[derive(Parser)]
#[grammar = "dhall.pest"]
pub struct DhallParser;
