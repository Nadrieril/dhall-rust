use std::fs::File;
use std::io::{Read,Write,BufReader,BufRead};
use std::collections::HashMap;
use itertools::Itertools;

use lalrpop;

fn abnf_to_pest(data: &Vec<u8>, visibility_map: &HashMap<String, bool>) -> std::io::Result<String> {
    use abnf::abnf::*;
    fn format_rule(x: Rule, visibility_map: &HashMap<String, bool>) -> String {
        let rulename = format_rulename(x.name);
        let contents = format_alternation(x.elements);
        let visible = visibility_map.get(&rulename).unwrap_or(&true);
        let visible = if *visible {""} else {"_"};
        format!("{} = {}{{ {} }}", rulename, visible, contents)
    }
    fn format_rulename(x: String) -> String {
        let x = x.replace("-", "_");
        if x == "if" || x == "else" || x == "as" || x == "let" || x == "in" || x == "fn" {
            x + "_"
        } else {
            x
        }
    }
    fn format_alternation(x: Alternation) -> String {
        x.concatenations.into_iter().map(format_concatenation).join("\n    | ")
    }
    fn format_concatenation(x: Concatenation) -> String {
        x.repetitions.into_iter().map(format_repetition).join(" ~ ")
    }
    fn format_repetition(x: Repetition) -> String {
        format!("{}{}", format_element(x.element), x.repeat.map(format_repeat).unwrap_or("".into()))
    }
    fn format_repeat(x: Repeat) -> String {
        match (x.min.unwrap_or(0), x.max) {
            (0, None) => "*".into(),
            (1, None) => "+".into(),
            (0, Some(1)) => "?".into(),
            (min, None) => format!("{{{},}}", min),
            (min, Some(max)) if min == max => format!("{{{}}}", min),
            (min, Some(max)) => format!("{{{},{}}}", min, max),
        }
    }
    fn format_element(x: Element) -> String {
        use abnf::abnf::Element::*;
        match x {
            Rulename(s) => format_rulename(s),
            Group(g) => format!("({})", format_alternation(g.alternation)),
            Option(o) => format!("({})?", format_alternation(o.alternation)),
            CharVal(s) => format!("^\"{}\"", s.replace("\"", "\\\"").replace("\\", "\\\\")),
            NumVal(r) => format_range(r),
            ProseVal(_) => unimplemented!(),
        }
    }
    fn format_range(x: Range) -> String {
        use abnf::abnf::Range::*;
        match x {
            Range(x, y) => format!("'{}'..'{}'", format_char(x), format_char(y)),
            OneOf(v) => format!("\"{}\"", v.into_iter().map(format_char).join("")),
        }
    }
    fn format_char(x: u64) -> String {
        if x <= (u8::max_value() as u64) {
            let x: u8 = x as u8;
            if x.is_ascii_graphic() {
                let x: char = x as char;
                if x != '"' && x != '\'' && x != '\\' {
                    return x.to_string();
                }
            }
        }
        format!("\\u{{{:02X}}}", x)
    }
    let make_err = |e| std::io::Error::new(std::io::ErrorKind::Other, format!("{}", e));

    let rules = rulelist_comp(&data).map_err(make_err)?.1;
    Ok(rules.into_iter().map(|x| format_rule(x, visibility_map)).join("\n"))
}

fn main() -> std::io::Result<()> {
    lalrpop::process_root().unwrap();
    println!("cargo:rerun-if-changed=src/grammar.lalrpop");


    let abnf_path = "dhall-lang/standard/dhall.abnf";
    let visibility_path = "src/dhall.pest.visibility";
    let pest_path = "src/dhall.pest";
    println!("cargo:rerun-if-changed={}", abnf_path);
    println!("cargo:rerun-if-changed={}", visibility_path);

    let mut file = File::open(abnf_path)?;
    let mut data = Vec::new();
    file.read_to_end(&mut data)?;
    data.push('\n' as u8);

    let mut visibility_map: HashMap<String, bool> = HashMap::new();
    for line in BufReader::new(File::open(visibility_path)?).lines() {
        let line = line?;
        if line.len() >= 2 && &line[0..2] == "# " {
            visibility_map.insert(line[2..].into(), false);
        } else {
            visibility_map.insert(line, true);
        }
    }

    let mut file = File::create(pest_path)?;
    writeln!(&mut file, "{}", abnf_to_pest(&data, &visibility_map)?)?;
    writeln!(&mut file, "final_expression = _{{ SOI ~ complete_expression ~ EOI }}")?;

    Ok(())
}
