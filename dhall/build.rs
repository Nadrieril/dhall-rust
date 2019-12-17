use std::env;
use std::ffi::OsString;
use std::fs::File;
use std::io::{BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

use abnf_to_pest::render_rules_to_pest;

#[derive(Debug, Clone, Copy)]
enum FileType {
    Text,
    Binary,
}

impl FileType {
    fn to_ext(self) -> &'static str {
        match self {
            FileType::Text => "dhall",
            FileType::Binary => "dhallb",
        }
    }
}

fn dhall_files_in_dir<'a>(
    dir: &'a Path,
    take_a_suffix: bool,
    filetype: FileType,
) -> impl Iterator<Item = (String, String)> + 'a {
    WalkDir::new(dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter_map(move |path| {
            let path = path.path().strip_prefix(dir).unwrap();
            let ext = path.extension()?;
            if ext != &OsString::from(filetype.to_ext()) {
                return None;
            }
            let path = path.to_string_lossy();
            let path = &path[..path.len() - 1 - ext.len()];
            let path = if take_a_suffix && &path[path.len() - 1..] != "A" {
                return None;
            } else if take_a_suffix {
                path[..path.len() - 1].to_owned()
            } else {
                path.to_owned()
            };
            // Transform path into a valie Rust identifier
            let name = path.replace("/", "_").replace("-", "_");
            Some((name, path))
        })
}

#[derive(Debug, Clone)]
struct TestFeature<F> {
    /// Name of the module, used in the output of `cargo test`
    module_name: &'static str,
    /// Directory containing the tests files
    directory: PathBuf,
    /// Relevant variant of `dhall::tests::Test`
    variant: &'static str,
    /// Given a file name, whether to exclude it
    path_filter: F,
    /// Type of the input file
    input_type: FileType,
    /// Type of the output file, if any
    output_type: Option<FileType>,
}

fn make_test_module(
    w: &mut impl Write, // Where to output the generated code
    mut feature: TestFeature<impl FnMut(&str) -> bool>,
) -> std::io::Result<()> {
    let tests_dir = feature.directory;
    writeln!(w, "mod {} {{", feature.module_name)?;
    let take_a_suffix = feature.output_type.is_some();
    for (name, path) in
        dhall_files_in_dir(&tests_dir, take_a_suffix, feature.input_type)
    {
        if (feature.path_filter)(&path) {
            continue;
        }
        let path = tests_dir.join(path);
        let path = path.to_string_lossy();
        let test = match feature.output_type {
            None => {
                let input_file =
                    format!("\"{}.{}\"", path, feature.input_type.to_ext());
                format!("{}({})", feature.variant, input_file)
            }
            Some(output_type) => {
                let input_file =
                    format!("\"{}A.{}\"", path, feature.input_type.to_ext());
                let output_file =
                    format!("\"{}B.{}\"", path, output_type.to_ext());
                format!("{}({}, {})", feature.variant, input_file, output_file)
            }
        };
        writeln!(w, "make_spec_test!({}, {});", test, name)?;
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
    let spec_tests_dir = Path::new("../dhall-lang/tests/");
    let mut file = File::create(parser_tests_path)?;

    make_test_module(
        &mut file,
        TestFeature {
            module_name: "parser_success",
            directory: spec_tests_dir.join("parser/success/"),
            variant: "ParserSuccess",
            path_filter: |path: &str| {
                false
                    // Too slow in debug mode
                    || path == "largeExpression"
                    // Pretty sure the test is incorrect
                    || path == "unit/import/urls/quotedPathFakeUrlEncode"
                    // TODO: RFC3986 URLs
                    || path == "unit/import/urls/emptyPath0"
                    || path == "unit/import/urls/emptyPath1"
                    || path == "unit/import/urls/emptyPathSegment"
            },
            input_type: FileType::Text,
            output_type: Some(FileType::Binary),
        },
    )?;

    make_test_module(
        &mut file,
        TestFeature {
            module_name: "parser_failure",
            directory: spec_tests_dir.join("parser/failure/"),
            variant: "ParserFailure",
            path_filter: |_path: &str| false,
            input_type: FileType::Text,
            output_type: None,
        },
    )?;

    make_test_module(
        &mut file,
        TestFeature {
            module_name: "printer",
            directory: spec_tests_dir.join("parser/success/"),
            variant: "Printer",
            path_filter: |path: &str| {
                false
                    // Too slow in debug mode
                    || path == "largeExpression"
                    // TODO: RFC3986 URLs
                    || path == "unit/import/urls/emptyPath0"
                    || path == "unit/import/urls/emptyPath1"
                    || path == "unit/import/urls/emptyPathSegment"
            },
            input_type: FileType::Text,
            output_type: Some(FileType::Binary),
        },
    )?;

    make_test_module(
        &mut file,
        TestFeature {
            module_name: "binary_encoding",
            directory: spec_tests_dir.join("parser/success/"),
            variant: "BinaryEncoding",
            path_filter: |path: &str| {
                false
                    // Too slow in debug mode
                    || path == "largeExpression"
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
            },
            input_type: FileType::Text,
            output_type: Some(FileType::Binary),
        },
    )?;

    make_test_module(
        &mut file,
        TestFeature {
            module_name: "binary_decoding_success",
            directory: spec_tests_dir.join("binary-decode/success/"),
            variant: "BinaryDecodingSuccess",
            path_filter: |_path: &str| false,
            input_type: FileType::Binary,
            output_type: Some(FileType::Text),
        },
    )?;

    make_test_module(
        &mut file,
        TestFeature {
            module_name: "binary_decoding_failure",
            directory: spec_tests_dir.join("binary-decode/failure/"),
            variant: "BinaryDecodingFailure",
            path_filter: |_path: &str| false,
            input_type: FileType::Binary,
            output_type: None,
        },
    )?;

    make_test_module(
        &mut file,
        TestFeature {
            module_name: "import_success",
            directory: spec_tests_dir.join("import/success/"),
            variant: "ImportSuccess",
            path_filter: |path: &str| {
                false
                    || path == "alternativeEnvNatural"
                    || path == "alternativeEnvSimple"
                    || path == "alternativeHashMismatch"
                    || path == "asLocation"
                    || path == "asText"
                    || path == "customHeaders"
                    || path == "hashFromCache"
                    || path == "headerForwarding"
                    || path == "noHeaderForwarding"
            },
            input_type: FileType::Text,
            output_type: Some(FileType::Text),
        },
    )?;

    make_test_module(
        &mut file,
        TestFeature {
            module_name: "import_failure",
            directory: spec_tests_dir.join("import/failure/"),
            variant: "ImportFailure",
            path_filter: |path: &str| {
                false
                    || path == "alternativeEnv"
                    || path == "alternativeEnvMissing"
                    || path == "hashMismatch"
                    || path == "missing"
                    || path == "referentiallyInsane"
            },
            input_type: FileType::Text,
            output_type: None,
        },
    )?;

    make_test_module(
        &mut file,
        TestFeature {
            module_name: "beta_normalize",
            directory: spec_tests_dir.join("normalization/success/"),
            variant: "Normalization",
            path_filter: |path: &str| {
                // We don't support bignums
                path == "simple/integerToDouble"
                    // Too slow
                    || path == "remoteSystems"
                    // TODO: projection by expression
                    || path == "unit/RecordProjectionByTypeEmpty"
                    || path == "unit/RecordProjectionByTypeNonEmpty"
                    || path == "unit/RecordProjectionByTypeNormalizeProjection"
                    // TODO: fix Double/show
                    || path == "prelude/JSON/number/1"
                    // TODO: toMap
                    || path == "unit/EmptyToMap"
                    || path == "unit/ToMap"
                    || path == "unit/ToMapWithType"
                    // TODO: Further record simplifications
                    || path == "simplifications/rightBiasedMergeWithinRecordProjectionWithinFieldSelection0"
                    || path == "simplifications/rightBiasedMergeWithinRecordProjectionWithinFieldSelection1"
                    || path == "simplifications/rightBiasedMergeWithinRecursiveRecordMergeWithinFieldselection"
                    || path == "simplifications/issue661"
                    || path == "unit/RecordProjectionByTypeWithinFieldSelection"
                    || path == "unit/RecordProjectionWithinFieldSelection"
                    || path == "unit/RecursiveRecordMergeWithinFieldSelection0"
                    || path == "unit/RecursiveRecordMergeWithinFieldSelection1"
                    || path == "unit/RecursiveRecordMergeWithinFieldSelection2"
                    || path == "unit/RecursiveRecordMergeWithinFieldSelection3"
                    || path == "unit/RightBiasedMergeWithinFieldSelection0"
                    || path == "unit/RightBiasedMergeWithinFieldSelection1"
                    || path == "unit/RightBiasedMergeWithinFieldSelection2"
                    || path == "unit/RightBiasedMergeWithinFieldSelection3"
                    || path == "unit/RightBiasedRecordMergeWithinRecordProjection"
                    || path == "unit/RightBiasedMergeEquivalentArguments"
                    || path == "unit/NestedRecordProjection"
                    || path == "unit/NestedRecordProjectionByType"
            },
            input_type: FileType::Text,
            output_type: Some(FileType::Text),
        },
    )?;

    make_test_module(
        &mut file,
        TestFeature {
            module_name: "alpha_normalize",
            directory: spec_tests_dir.join("alpha-normalization/success/"),
            variant: "AlphaNormalization",
            path_filter: |path: &str| {
                // This test doesn't typecheck
                path == "unit/FunctionNestedBindingXXFree"
            },
            input_type: FileType::Text,
            output_type: Some(FileType::Text),
        },
    )?;

    make_test_module(
        &mut file,
        TestFeature {
            module_name: "type_inference_success",
            directory: spec_tests_dir.join("type-inference/success/"),
            variant: "TypeInferenceSuccess",
            path_filter: |path: &str| {
                false
                    // Too slow
                    || path == "prelude"
                    // TODO: projection by expression
                    || path == "unit/RecordProjectionByType"
                    || path == "unit/RecordProjectionByTypeEmpty"
                    || path == "unit/RecordProjectionByTypeJudgmentalEquality"
                    // TODO: toMap
                    || path == "unit/ToMap"
                    || path == "unit/ToMapAnnotated"
                    || path == "simple/toMapEmptyNormalizeAnnotation"
            },
            input_type: FileType::Text,
            output_type: Some(FileType::Text),
        },
    )?;

    make_test_module(
        &mut file,
        TestFeature {
            module_name: "type_inference_failure",
            directory: spec_tests_dir.join("type-inference/failure/"),
            variant: "TypeInferenceFailure",
            path_filter: |path: &str| {
                false
                    // TODO: Enable imports in typecheck tests
                    || path == "importBoundary"
                    || path == "customHeadersUsingBoundVariable"
                    // TODO: projection by expression
                    || path == "unit/RecordProjectionByTypeFieldTypeMismatch"
                    || path == "unit/RecordProjectionByTypeNotPresent"
                    // TODO: toMap
                    || path == "unit/EmptyToMap"
                    || path == "unit/HeterogenousToMap"
                    || path == "unit/MistypedToMap1"
                    || path == "unit/MistypedToMap2"
                    || path == "unit/MistypedToMap3"
                    || path == "unit/MistypedToMap4"
                    || path == "unit/NonRecordToMap"
                    || path == "unit/ToMapWrongKind"
            },
            input_type: FileType::Text,
            output_type: None,
        },
    )?;

    make_test_module(
        &mut file,
        TestFeature {
            module_name: "type_error",
            directory: spec_tests_dir.join("type-inference/failure/"),
            variant: "TypeError",
            path_filter: |path: &str| {
                false
                    // TODO: Enable imports in typecheck tests
                    || path == "importBoundary"
                    || path == "customHeadersUsingBoundVariable"
                    // TODO: projection by expression
                    || path == "unit/RecordProjectionByTypeFieldTypeMismatch"
                    || path == "unit/RecordProjectionByTypeNotPresent"
                    // TODO: toMap
                    || path == "unit/EmptyToMap"
                    || path == "unit/HeterogenousToMap"
                    || path == "unit/MistypedToMap1"
                    || path == "unit/MistypedToMap2"
                    || path == "unit/MistypedToMap3"
                    || path == "unit/MistypedToMap4"
                    || path == "unit/NonRecordToMap"
                    || path == "unit/ToMapWrongKind"
            },
            input_type: FileType::Text,
            output_type: None,
        },
    )?;

    Ok(())
}

fn convert_abnf_to_pest() -> std::io::Result<()> {
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

    Ok(())
}

fn main() -> std::io::Result<()> {
    convert_abnf_to_pest()?;
    generate_tests()?;
    Ok(())
}
