use std::env;
use std::ffi::OsString;
use std::fs::{self, File};
use std::io::Write;
use std::path::Path;

fn dhall_files_in_dir<'a>(dir: &'a Path) -> impl Iterator<Item = String> + 'a {
    fs::read_dir(dir).unwrap().filter_map(move |path| {
        let path = path.unwrap().path();
        let path = path.strip_prefix(dir).unwrap();
        if path.extension() != Some(&OsString::from("dhall")) {
            return None;
        }
        let path = path.to_string_lossy();
        let path = path[..path.len() - 6].to_owned();
        Some(path)
    })
}

fn main() -> std::io::Result<()> {
    let out_dir = env::var("OUT_DIR").unwrap();
    let tests_dir = Path::new("../dhall-lang/tests/");

    let parser_tests_path = Path::new(&out_dir).join("parser_tests.rs");
    let mut file = File::create(parser_tests_path)?;

    for path in dhall_files_in_dir(&tests_dir.join("parser/success/")) {
        let name = &path[..path.len() - 1];
        // Skip this test; parser is way too slow indebug mode
        if name == "largeExpression" {
            continue;
        }
        writeln!(file, r#"make_spec_test!(ParserSuccess, spec_parser_success_{0}, "{0}");"#, name)?;
    }

    for path in dhall_files_in_dir(&tests_dir.join("parser/failure/")) {
        let name = &path;
        writeln!(file, r#"make_spec_test!(ParserFailure, spec_parser_failure_{0}, "{0}");"#, name)?;
    }

    Ok(())
}
