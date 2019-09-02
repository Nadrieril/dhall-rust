use std::env;
use std::fs::File;
use std::io::{BufRead, BufReader, Read, Write};
use std::path::Path;

use abnf_to_pest::render_rules_to_pest;

fn main() -> std::io::Result<()> {
    // TODO: upstream changes to grammar
    // let abnf_path = "../dhall-lang/standard/dhall.abnf";
    let abnf_path = "src/dhall.abnf";
    let visibility_path = "src/dhall.pest.visibility";
    let pest_path = "src/dhall.pest";
    println!("cargo:rerun-if-changed={}", abnf_path);
    println!("cargo:rerun-if-changed={}", visibility_path);

    let mut file = File::open(abnf_path)?;
    let mut data = Vec::new();
    file.read_to_end(&mut data)?;
    data.push('\n' as u8);

    let mut rules = abnf_to_pest::parse_abnf(&data)?;
    for line in BufReader::new(File::open(visibility_path)?).lines() {
        let line = line?;
        if line.len() >= 2 && &line[0..2] == "# " {
            rules.get_mut(&line[2..]).map(|x| x.silent = true);
        }
    }

    let mut file = File::create(pest_path)?;
    writeln!(&mut file, "// AUTO-GENERATED FILE. See build.rs.")?;

    // TODO: this is a cheat; properly support RFC3986 URLs instead
    rules.remove("url_path");
    writeln!(&mut file, "url_path = _{{ path }}")?;

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
    writeln!(&mut file, r##"
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
        operator_expression = {{ application_expression ~ (whsp ~ operator ~ whsp ~ application_expression)* }}
    "##)?;

    writeln!(
        &mut file,
        "final_expression = ${{ SOI ~ complete_expression ~ EOI }}"
    )?;

    writeln!(&mut file)?;
    writeln!(&mut file, "{}", render_rules_to_pest(rules).pretty(80))?;

    // Generate pest parser manually to avoid spurious recompilations
    let derived = {
        let pest_path = "dhall.pest";
        let pest = quote::quote! {
            #[grammar = #pest_path]
            pub struct DhallParser;
        };
        pest_generator::derive_parser(pest, false)
    };

    let out_dir = env::var("OUT_DIR").unwrap();
    let grammar_path = Path::new(&out_dir).join("grammar.rs");
    let mut file = File::create(grammar_path)?;
    writeln!(file, "pub struct DhallParser;\n{}", derived,)?;

    Ok(())
}
