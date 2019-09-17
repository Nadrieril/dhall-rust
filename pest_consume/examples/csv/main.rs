use pest_consume::{match_nodes, Error, Parser};

#[derive(Debug)]
enum CSVField<'a> {
    Number(f64),
    String(&'a str),
}
type CSVRecord<'a> = Vec<CSVField<'a>>;
type CSVFile<'a> = Vec<CSVRecord<'a>>;

type Result<T> = std::result::Result<T, Error<Rule>>;
type Node<'i> = pest_consume::Node<'i, Rule, ()>;

#[derive(Parser)]
#[grammar = "../examples/csv/csv.pest"]
struct CSVParser;

#[pest_consume::parser]
impl CSVParser {
    fn EOI(_input: Node) -> Result<()> {
        Ok(())
    }

    fn number(input: Node) -> Result<f64> {
        input
            .as_str()
            .parse::<f64>()
            // `input.error` links the error to the location in the input file where it occurred.
            .map_err(|e| input.error(e.to_string()))
    }

    fn string(input: Node) -> Result<&str> {
        Ok(input.as_str())
    }

    fn field(input: Node) -> Result<CSVField> {
        Ok(match_nodes!(input.children();
            [number(n)] => CSVField::Number(n),
            [string(s)] => CSVField::String(s),
        ))
    }

    fn record(input: Node) -> Result<CSVRecord> {
        Ok(match_nodes!(input.children();
            [field(fields)..] => fields.collect(),
        ))
    }

    fn file(input: Node) -> Result<CSVFile> {
        Ok(match_nodes!(input.children();
            [record(records).., EOI(_)] => records.collect(),
        ))
    }
}

fn parse_csv(input_str: &str) -> Result<CSVFile> {
    let inputs = CSVParser::parse(Rule::file, input_str)?;
    Ok(match_nodes!(<CSVParser>; inputs;
        [file(e)] => e,
    ))
}

fn main() {
    let successful_parse = parse_csv("-273.15, ' a string '\n\n42, 0");
    println!("success: {:?}", successful_parse.unwrap());

    let unsuccessful_parse = parse_csv("0, 273.15.12");
    println!("failure: {}", unsuccessful_parse.unwrap_err());
}
