use std::env;
use std::ffi::OsString;
use std::fs::File;
use std::io::Write;
use std::path::Path;
use walkdir::WalkDir;

fn dhall_files_in_dir<'a>(dir: &'a Path) -> impl Iterator<Item = String> + 'a {
    WalkDir::new(dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter_map(move |path| {
            let path = path.path();
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
    println!("cargo:rerun-if-changed=../dhall-lang/.git");
    println!(
        "cargo:rerun-if-changed=../.git/modules/dhall-lang/refs/heads/master"
    );
    let out_dir = env::var("OUT_DIR").unwrap();
    let tests_dir = Path::new("../dhall-lang/tests/");

    let parser_tests_path = Path::new(&out_dir).join("parser_tests.rs");
    let mut file = File::create(parser_tests_path)?;

    for path in dhall_files_in_dir(&tests_dir.join("parser/success/")) {
        let path = &path[..path.len() - 1];
        let name = path.replace("/", "_");
        // Skip this test; parser is way too slow indebug mode
        if name == "largeExpression" {
            continue;
        }
        writeln!(
            file,
            r#"make_spec_test!(ParserSuccess, spec_parser_success_{}, "{}");"#,
            name, path
        )?;
    }

    for path in dhall_files_in_dir(&tests_dir.join("parser/failure/")) {
        let name = path.replace("/", "_");
        writeln!(
            file,
            r#"make_spec_test!(ParserFailure, spec_parser_failure_{}, "{}");"#,
            name, path
        )?;
    }

    Ok(())
}
