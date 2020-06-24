use std::env;
use std::fs::{read_to_string, File};
use std::io::{BufRead, BufReader, Write};
use std::path::Path;

use abnf_to_pest::render_rules_to_pest;

fn convert_abnf_to_pest() -> std::io::Result<()> {
    let out_dir = env::var("OUT_DIR").unwrap();
    let abnf_path = "src/syntax/text/dhall.abnf";
    let visibility_path = "src/syntax/text/dhall.pest.visibility";
    let grammar_path = Path::new(&out_dir).join("dhall.pest");
    println!("cargo:rerun-if-changed={}", abnf_path);
    println!("cargo:rerun-if-changed={}", visibility_path);

    let mut data = read_to_string(abnf_path)?;
    data.push('\n');
    let data = data.replace('∀', ""); // TODO: waiting for abnf 0.6.1

    let mut rules = abnf_to_pest::parse_abnf(&data)?;
    for line in BufReader::new(File::open(visibility_path)?).lines() {
        let line = line?;
        if line.len() >= 2 && &line[0..2] == "# " {
            if let Some(x) = rules.get_mut(&line[2..]) {
                x.silent = true;
            }
        }
    }

    let mut file = File::create(grammar_path)?;
    writeln!(&mut file, "// AUTO-GENERATED FILE. See build.rs.")?;

    // Work around some greediness issue in the grammar.
    rules.remove("missing");
    writeln!(
        &mut file,
        r#"missing = {{ "missing" ~ !simple_label_next_char }}"#
    )?;

    // Prefer my nice error message to illegible parse errors.
    rules.remove("unicode_escape");
    rules.remove("unbraced_escape");
    rules.remove("braced_escape");
    rules.remove("braced_codepoint");
    rules.remove("unicode_suffix");
    writeln!(
        &mut file,
        r#"unicode_escape = _{{ HEXDIG{{4}} | "{{" ~ HEXDIG+ ~ "}}" }}"#
    )?;

    rules.remove("simple_label");
    writeln!(
        &mut file,
        "simple_label = {{
              keyword ~ simple_label_next_char+
            | !keyword ~ simple_label_first_char ~ simple_label_next_char*
    }}"
    )?;

    rules.remove("nonreserved_label");
    writeln!(
        &mut file,
        "nonreserved_label = _{{
            !(builtin ~ !simple_label_next_char) ~ label
    }}"
    )?;

    // Setup grammar for precedence climbing
    rules.remove("operator_expression");
    writeln!(
        &mut file,
        r##"
        import_alt = {{ "?" ~ whsp1 }}
        bool_or = {{ "||" }}
        natural_plus = {{ "+" ~ whsp1 }}
        text_append = {{ "++" }}
        list_append = {{ "#" }}
        bool_and = {{ "&&" }}
        natural_times = {{ "*" }}
        bool_eq = {{ "==" }}
        bool_ne = {{ "!=" }}

        operator = _{{
            equivalent |
            bool_ne |
            bool_eq |
            natural_times |
            combine_types |
            prefer |
            combine |
            bool_and |
            list_append |
            text_append |
            natural_plus |
            bool_or |
            import_alt
        }}
        operator_expression = {{ with_expression ~ (whsp ~ operator ~ whsp ~ with_expression)* }}
    "##
    )?;

    writeln!(
        &mut file,
        "final_expression = ${{ SOI ~ complete_expression ~ EOI }}"
    )?;

    writeln!(&mut file)?;
    writeln!(&mut file, "{}", render_rules_to_pest(rules).pretty(80))?;

    Ok(())
}

// Generate pest parser manually because otherwise we'd need to modify something outside of
// OUT_DIR and that's forbidden by docs.rs.
fn generate_pest_parser() -> std::io::Result<()> {
    let out_dir = env::var("OUT_DIR").unwrap();
    let grammar_path = Path::new(&out_dir).join("dhall.pest");
    let grammar_path = grammar_path.to_str();
    let output_path = Path::new(&out_dir).join("dhall_parser.rs");

    let pest = quote::quote!(
        #[grammar = #grammar_path]
        struct DhallParser;
    );
    let derived = pest_generator::derive_parser(pest, false);
    let file_contents = quote::quote!(
        struct DhallParser;
        #derived
    );

    let mut file = File::create(output_path)?;
    writeln!(file, "{}", file_contents)
}

fn main() -> std::io::Result<()> {
    convert_abnf_to_pest()?;
    generate_pest_parser()?;
    Ok(())
}
