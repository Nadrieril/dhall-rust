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
    rules.remove("simple_label");

    let mut file = File::create(pest_path)?;
    writeln!(&mut file, "// AUTO-GENERATED FILE. See build.rs.")?;
    writeln!(&mut file, "{}", render_rules_to_pest(rules).pretty(80))?;

    writeln!(&mut file)?;
    writeln!(
        &mut file,
        "simple_label = {{
              keyword ~ simple_label_next_char+
            | !keyword ~ simple_label_first_char ~ simple_label_next_char*
    }}"
    )?;
    writeln!(
        &mut file,
        "keyword = _{{
            let_ | in_ | if_ | then
                | else_ | Infinity | NaN
    }}"
    )?;
    writeln!(
        &mut file,
        "final_expression = ${{ SOI ~ complete_expression ~ EOI }}"
    )?;

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
