#![feature(slice_patterns)]
use pest_consume::{match_nodes, Parser};

#[derive(pest_derive::Parser)]
#[grammar = "../examples/csv/csv.pest"]
struct CSVParser;

type ParseResult<T> = Result<T, pest::error::Error<Rule>>;
type Node<'i> = pest_consume::Node<'i, Rule, ()>;

#[derive(Debug)]
enum CSVField<'a> {
    Number(f64),
    String(&'a str),
}

type CSVRecord<'a> = Vec<CSVField<'a>>;
type CSVFile<'a> = Vec<CSVRecord<'a>>;

#[pest_consume::parser(CSVParser, Rule)]
impl CSVParser {
    fn EOI(_input: Node) -> ParseResult<()> {
        Ok(())
    }

    fn number(input: Node) -> ParseResult<f64> {
        Ok(input.as_str().parse().unwrap())
    }

    fn string(input: Node) -> ParseResult<&str> {
        Ok(input.as_str())
    }

    fn field(input: Node) -> ParseResult<CSVField> {
        Ok(match_nodes!(input.children();
            [number(n)] => CSVField::Number(n),
            [string(s)] => CSVField::String(s),
        ))
    }

    fn record(input: Node) -> ParseResult<CSVRecord> {
        Ok(match_nodes!(input.children();
            [field(fields)..] => fields.collect(),
        ))
    }

    fn file(input: Node) -> ParseResult<CSVFile> {
        Ok(match_nodes!(input.children();
            [record(records).., EOI(_)] => records.collect(),
        ))
    }
}

fn parse_csv(input_str: &str) -> ParseResult<CSVFile> {
    let inputs = CSVParser::parse(Rule::file, input_str)?;
    Ok(match_nodes!(<CSVParser>; inputs;
        [file(e)] => e,
    ))
}

fn main() {
    let parsed = parse_csv("-273.15, ' a string '\n\n42, 0");
    println!("{:?}", parsed);
}
