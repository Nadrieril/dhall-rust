use std::fs::File;
use std::io::{Read,Write,BufReader,BufRead};
use std::collections::HashMap;

use abnf_to_pest::{PestRuleSettings, abnf_to_pest};

fn main() -> std::io::Result<()> {
    let abnf_path = "../dhall-lang/standard/dhall.abnf";
    let visibility_path = "src/dhall.pest.visibility";
    let pest_path = "src/dhall.pest";
    println!("cargo:rerun-if-changed={}", abnf_path);
    println!("cargo:rerun-if-changed={}", visibility_path);

    let mut file = File::open(abnf_path)?;
    let mut data = Vec::new();
    file.read_to_end(&mut data)?;
    data.push('\n' as u8);

    let mut rule_settings: HashMap<String, PestRuleSettings> = HashMap::new();
    for line in BufReader::new(File::open(visibility_path)?).lines() {
        let line = line?;
        if line.len() >= 2 && &line[0..2] == "# " {
            rule_settings.insert(line[2..].into(), PestRuleSettings { visible: false, ..Default::default() });
        } else {
            rule_settings.insert(line, PestRuleSettings { visible: true, ..Default::default() });
        }
    }

    let mut file = File::create(pest_path)?;
    writeln!(&mut file, "{}", abnf_to_pest(&data, &rule_settings)?)?;
    writeln!(&mut file, "final_expression = _{{ SOI ~ complete_expression ~ EOI }}")?;

    Ok(())
}
