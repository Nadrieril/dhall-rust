use std::env;
use std::ffi::OsString;
use std::fs::{read_to_string, File};
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

use abnf_to_pest::render_rules_to_pest;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FileType {
    /// Dhall source file
    Text,
    /// Dhall binary file
    Binary,
    /// Text file with expected text output
    UI,
}

impl FileType {
    fn to_ext(self) -> &'static str {
        match self {
            FileType::Text => "dhall",
            FileType::Binary => "dhallb",
            FileType::UI => "txt",
        }
    }
    fn constructor(self) -> &'static str {
        match self {
            FileType::Text => "TestFile::Source",
            FileType::Binary => "TestFile::Binary",
            FileType::UI => "TestFile::UI",
        }
    }
    fn construct(self, path: &str) -> String {
        // e.g. with
        //  path = "tests/foor/barA"
        // returns something like:
        //  TestFile::Source("tests/foor/barA.dhall")
        format!(r#"{}("{}.{}")"#, self.constructor(), path, self.to_ext())
    }
}

fn dhall_files_in_dir<'a>(
    dir: &'a Path,
    take_ab_suffix: bool,
    filetype: FileType,
) -> impl Iterator<Item = (String, String)> + 'a {
    WalkDir::new(dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter_map(move |path| {
            let path = path.path().strip_prefix(dir).unwrap();
            let ext = path.extension()?;
            if *ext != OsString::from(filetype.to_ext()) {
                return None;
            }
            let path = path.to_string_lossy();
            let path = &path[..path.len() - 1 - ext.len()];
            let path = if take_ab_suffix && &path[path.len() - 1..] != "A" {
                return None;
            } else if take_ab_suffix {
                path[..path.len() - 1].to_owned()
            } else {
                path.to_owned()
            };
            // Transform path into a valid Rust identifier
            let name = path.replace("/", "_").replace("-", "_");
            Some((name, path))
        })
}

struct TestFeature {
    /// Name of the module, used in the output of `cargo test`
    module_name: &'static str,
    /// Directory containing the tests files, relative to the base tests directory
    directory: &'static str,
    /// Relevant variant of `dhall::tests::Test`
    variant: &'static str,
    /// Given a file name, whether to only include it in release tests
    too_slow_path: Box<dyn FnMut(&str) -> bool>,
    /// Given a file name, whether to exclude it
    exclude_path: Box<dyn FnMut(&str) -> bool>,
    /// Type of the input file
    input_type: FileType,
    /// Type of the output file, if any
    output_type: Option<FileType>,
}

fn make_test_module(
    w: &mut impl Write, // Where to output the generated code
    base_paths: &[&Path],
    mut feature: TestFeature,
) -> std::io::Result<()> {
    writeln!(w, "mod {} {{", feature.module_name)?;
    let take_ab_suffix = feature.output_type.is_some()
        && feature.output_type != Some(FileType::UI);
    for base_path in base_paths {
        let tests_dir = base_path.join(feature.directory);
        for (name, path) in
            dhall_files_in_dir(&tests_dir, take_ab_suffix, feature.input_type)
        {
            if (feature.exclude_path)(&path) {
                continue;
            }
            if (feature.too_slow_path)(&path) {
                writeln!(w, "#[cfg(not(debug_assertions))]")?;
            }
            let path = tests_dir.join(path);
            let path = path.to_string_lossy();
            let test = match feature.output_type {
                None => {
                    let input = feature.input_type.construct(&path);
                    format!("{}({})", feature.variant, input)
                }
                Some(output_type @ FileType::UI) => {
                    let input = feature.input_type.construct(&path);
                    // All ui outputs are in the local `tests/` directory.
                    let output_file = PathBuf::from("tests/").join(
                        PathBuf::from(path.as_ref())
                            .strip_prefix(base_path)
                            .unwrap(),
                    );
                    let output =
                        output_type.construct(&output_file.to_str().unwrap());
                    format!("{}({}, {})", feature.variant, input, output)
                }
                Some(output_type) => {
                    let input =
                        feature.input_type.construct(&format!("{}A", path));
                    let output = output_type.construct(&format!("{}B", path));
                    format!("{}({}, {})", feature.variant, input, output)
                }
            };
            writeln!(w, "make_spec_test!({}, {});", test, name)?;
        }
    }
    writeln!(w, "}}")?;
    Ok(())
}

fn generate_tests() -> std::io::Result<()> {
    // Tries to detect when the submodule gets updated.
    // To force regeneration of the test list, just `touch dhall-lang/.git`
    println!("cargo:rerun-if-changed=../dhall-lang/.git");
    println!(
        "cargo:rerun-if-changed=../.git/modules/dhall-lang/refs/heads/master"
    );
    let out_dir = env::var("OUT_DIR").unwrap();

    let parser_tests_path = Path::new(&out_dir).join("spec_tests.rs");
    let spec_tests_dirs =
        vec![Path::new("../dhall-lang/tests/"), Path::new("tests/")];

    #[allow(clippy::nonminimal_bool)]
    let tests = vec![
        TestFeature {
            module_name: "parser_success",
            directory: "parser/success/",
            variant: "ParserSuccess",
            too_slow_path: Box::new(|path: &str| path == "largeExpression"),
            exclude_path: Box::new(|path: &str| {
                false
                    // Pretty sure the test is incorrect
                    || path == "unit/import/urls/quotedPathFakeUrlEncode"
                    // TODO: RFC3986 URLs
                    || path == "unit/import/urls/emptyPath0"
                    || path == "unit/import/urls/emptyPath1"
                    || path == "unit/import/urls/emptyPathSegment"
                    || path == "usingToMap"
            }),
            input_type: FileType::Text,
            output_type: Some(FileType::Binary),
        },
        TestFeature {
            module_name: "parser_failure",
            directory: "parser/failure/",
            variant: "ParserFailure",
            too_slow_path: Box::new(|_path: &str| false),
            exclude_path: Box::new(|_path: &str| false),
            input_type: FileType::Text,
            output_type: Some(FileType::UI),
        },
        TestFeature {
            module_name: "printer",
            directory: "parser/success/",
            variant: "Printer",
            too_slow_path: Box::new(|path: &str| path == "largeExpression"),
            exclude_path: Box::new(|path: &str| {
                false
                    // TODO: RFC3986 URLs
                    || path == "unit/import/urls/emptyPath0"
                    || path == "unit/import/urls/emptyPath1"
                    || path == "unit/import/urls/emptyPathSegment"
                    || path == "usingToMap"
            }),
            input_type: FileType::Text,
            output_type: Some(FileType::Binary),
        },
        TestFeature {
            module_name: "binary_encoding",
            directory: "parser/success/",
            variant: "BinaryEncoding",
            too_slow_path: Box::new(|path: &str| path == "largeExpression"),
            exclude_path: Box::new(|path: &str| {
                false
                    // Pretty sure the test is incorrect
                    || path == "unit/import/urls/quotedPathFakeUrlEncode"
                    // See https://github.com/pyfisch/cbor/issues/109
                    || path == "double"
                    || path == "unit/DoubleLitExponentNoDot"
                    || path == "unit/DoubleLitSecretelyInt"
                    // TODO: RFC3986 URLs
                    || path == "unit/import/urls/emptyPath0"
                    || path == "unit/import/urls/emptyPath1"
                    || path == "unit/import/urls/emptyPathSegment"
                    || path == "usingToMap"
            }),
            input_type: FileType::Text,
            output_type: Some(FileType::Binary),
        },
        TestFeature {
            module_name: "binary_decoding_success",
            directory: "binary-decode/success/",
            variant: "BinaryDecodingSuccess",
            too_slow_path: Box::new(|_path: &str| false),
            exclude_path: Box::new(|path: &str| {
                false
                    // We don't support bignums
                    || path == "unit/IntegerBigNegative"
                    || path == "unit/IntegerBigPositive"
                    || path == "unit/NaturalBig"
            }),
            input_type: FileType::Binary,
            output_type: Some(FileType::Text),
        },
        TestFeature {
            module_name: "binary_decoding_failure",
            directory: "binary-decode/failure/",
            variant: "BinaryDecodingFailure",
            too_slow_path: Box::new(|_path: &str| false),
            exclude_path: Box::new(|_path: &str| false),
            input_type: FileType::Binary,
            output_type: Some(FileType::UI),
        },
        TestFeature {
            module_name: "import_success",
            directory: "import/success/",
            variant: "ImportSuccess",
            too_slow_path: Box::new(|_path: &str| false),
            exclude_path: Box::new(|path: &str| {
                false
                    // TODO: import hash
                    || path == "alternativeHashMismatch"
                    || path == "hashFromCache"
                    || path == "unit/AlternativeHashMismatch"
                    // TODO: the standard does not respect https://tools.ietf.org/html/rfc3986#section-5.2
                    || path == "unit/asLocation/RemoteCanonicalize4"
                    // TODO: import headers
                    || path == "customHeaders"
                    || path == "headerForwarding"
                    || path == "noHeaderForwarding"
            }),
            input_type: FileType::Text,
            output_type: Some(FileType::Text),
        },
        TestFeature {
            module_name: "import_failure",
            directory: "import/failure/",
            variant: "ImportFailure",
            too_slow_path: Box::new(|_path: &str| false),
            exclude_path: Box::new(|path: &str| {
                false
                    // TODO: import hash
                    || path == "hashMismatch"
                    // TODO: import headers
                    || path == "customHeadersUsingBoundVariable"
            }),
            input_type: FileType::Text,
            output_type: Some(FileType::UI),
        },
        TestFeature {
            module_name: "beta_normalize",
            directory: "normalization/success/",
            variant: "Normalization",
            too_slow_path: Box::new(|path: &str| path == "remoteSystems"),
            exclude_path: Box::new(|path: &str| {
                false
                    // Cannot typecheck
                    || path == "unit/Sort"
                    // We don't support bignums
                    || path == "simple/integerToDouble"
                    // TODO: fix Double/show
                    || path == "prelude/JSON/number/1"
                    // TODO: Further record simplifications
                    || path == "simplifications/issue661"
                    || path == "unit/RightBiasedRecordMergeWithinRecordProjection"
            }),
            input_type: FileType::Text,
            output_type: Some(FileType::Text),
        },
        TestFeature {
            module_name: "alpha_normalize",
            directory: "alpha-normalization/success/",
            variant: "AlphaNormalization",
            too_slow_path: Box::new(|_path: &str| false),
            exclude_path: Box::new(|path: &str| {
                // This test is designed to not typecheck
                path == "unit/FunctionNestedBindingXXFree"
            }),
            input_type: FileType::Text,
            output_type: Some(FileType::Text),
        },
        TestFeature {
            module_name: "type_inference_success",
            directory: "type-inference/success/",
            variant: "TypeInferenceSuccess",
            too_slow_path: Box::new(|_path: &str| false),
            exclude_path: Box::new(|path: &str| {
                false
                    // Too slow, but also not all features implemented
                    // For now needs support for hashed imports
                    || path == "prelude"
            }),
            input_type: FileType::Text,
            output_type: Some(FileType::Text),
        },
        TestFeature {
            module_name: "type_inference_failure",
            directory: "type-inference/failure/",
            variant: "TypeInferenceFailure",
            too_slow_path: Box::new(|_path: &str| false),
            exclude_path: Box::new(|path: &str| {
                false
                    // TODO: enable free variable checking
                    || path == "unit/MergeHandlerFreeVar"
            }),
            input_type: FileType::Text,
            output_type: Some(FileType::UI),
        },
    ];

    let mut file = File::create(parser_tests_path)?;
    for test in tests {
        make_test_module(&mut file, &spec_tests_dirs, test)?;
    }

    Ok(())
}

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

    // TODO: this is a cheat; properly support RFC3986 URLs instead
    rules.remove("url_path");
    writeln!(&mut file, "url_path = _{{ path }}")?;

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

// Generate pest parser manually becaue otherwise we'd need to modify something outside of
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
    generate_tests()?;
    Ok(())
}
