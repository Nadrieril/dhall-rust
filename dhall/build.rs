use std::env;
use std::ffi::OsString;
use std::fs::File;
use std::io::Write;
use std::path::Path;
use walkdir::WalkDir;

fn dhall_files_in_dir<'a>(
    dir: &'a Path,
    take_a_suffix: bool,
) -> impl Iterator<Item = (String, String)> + 'a {
    WalkDir::new(dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter_map(move |path| {
            let path = path.path();
            let path = path.strip_prefix(dir).unwrap();
            let ext = path.extension();
            if ext != Some(&OsString::from("dhall"))
                && ext != Some(&OsString::from("dhallb"))
            {
                return None;
            }
            let ext = ext.unwrap();
            let path = path.to_string_lossy();
            let path = &path[..path.len() - 1 - ext.len()];
            let path = if take_a_suffix {
                if &path[path.len() - 1..] != "A" {
                    return None;
                } else {
                    path[..path.len() - 1].to_owned()
                }
            } else {
                path.to_owned()
            };
            let name = path.replace("/", "_").replace("-", "_");
            Some((name, path))
        })
}

fn make_test_module(
    w: &mut impl Write, // Where to output the generated code
    mod_name: &str, // Name of the module, used in the output of `cargo test`
    subdir: &str,   // Directory containing the tests files
    feature: &str,  // Relevant variant of `dhall::tests::Feature`
    mut exclude: impl FnMut(&str) -> bool, // Given a file name, whether to exclude it
) -> std::io::Result<()> {
    let all_tests_dir = Path::new("../dhall-lang/tests/");
    let tests_dir = all_tests_dir.join(subdir);
    writeln!(w, "mod {} {{", mod_name)?;
    for (name, path) in dhall_files_in_dir(&tests_dir.join("success/"), true) {
        if exclude(&("success/".to_owned() + &path)) {
            continue;
        }
        writeln!(
            w,
            r#"make_spec_test!({}, Success, success_{}, "{}/success/{}");"#,
            feature,
            name,
            tests_dir.to_string_lossy(),
            path
        )?;
    }
    for (name, path) in dhall_files_in_dir(&tests_dir.join("failure/"), false) {
        if exclude(&("failure/".to_owned() + &path)) {
            continue;
        }
        writeln!(
            w,
            r#"make_spec_test!({}, Failure, failure_{}, "{}/failure/{}");"#,
            feature,
            name,
            tests_dir.to_string_lossy(),
            path
        )?;
    }
    writeln!(w, "}}")?;
    Ok(())
}

fn main() -> std::io::Result<()> {
    // Tries to detect when the submodule gets updated.
    // To force regeneration of the test list, just `touch dhall-lang/.git`
    println!("cargo:rerun-if-changed=../dhall-lang/.git");
    println!(
        "cargo:rerun-if-changed=../.git/modules/dhall-lang/refs/heads/master"
    );
    let out_dir = env::var("OUT_DIR").unwrap();

    let parser_tests_path = Path::new(&out_dir).join("spec_tests.rs");
    let mut file = File::create(parser_tests_path)?;

    make_test_module(&mut file, "parse", "parser/", "Parser", |path| {
        // Too slow in debug mode
        path == "success/largeExpression"
            // TODO: Inline headers
            || path == "success/unit/import/parenthesizeUsing"
            || path == "success/unit/import/inlineUsing"
            // TODO: projection by expression
            || path == "success/recordProjectionByExpression"
            || path == "success/RecordProjectionByType"
            || path == "success/unit/RecordProjectionByType"
            || path == "success/unit/RecordProjectionByTypeEmpty"
            || path == "success/unit/RecordProjectFields"
            // TODO: RFC3986 URLs
            || path == "success/unit/import/urls/emptyPath0"
            || path == "success/unit/import/urls/emptyPath1"
            || path == "success/unit/import/urls/emptyPathSegment"
            // TODO: toMap
            || path == "success/toMap"
    })?;

    make_test_module(&mut file, "printer", "parser/", "Printer", |path| {
        // Failure tests are only for the parser
        path.starts_with("failure/")
            // Too slow in debug mode
            || path == "success/largeExpression"
            // TODO: Inline headers
            || path == "success/unit/import/inlineUsing"
            // TODO: projection by expression
            || path == "success/recordProjectionByExpression"
            || path == "success/RecordProjectionByType"
            || path == "success/unit/RecordProjectionByType"
            || path == "success/unit/RecordProjectionByTypeEmpty"
            // TODO: RFC3986 URLs
            || path == "success/unit/import/urls/emptyPath0"
            || path == "success/unit/import/urls/emptyPath1"
            || path == "success/unit/import/urls/emptyPathSegment"
            // TODO: toMap
            || path == "success/toMap"
    })?;

    make_test_module(
        &mut file,
        "binary_encoding",
        "parser/",
        "BinaryEncoding",
        |path| {
            // Failure tests are only for the parser
            path.starts_with("failure/")
            // Too slow in debug mode
            || path == "success/largeExpression"
            // Too much of a pain to implement; shouldn't make a difference
            // since lets disappear on normalization.
            || path == "success/multilet"
            // See https://github.com/pyfisch/cbor/issues/109
            || path == "success/double"
            // TODO: Inline headers
            || path == "success/unit/import/inlineUsing"
            // TODO: projection by expression
            || path == "success/recordProjectionByExpression"
            || path == "success/RecordProjectionByType"
            || path == "success/unit/RecordProjectionByType"
            || path == "success/unit/RecordProjectionByTypeEmpty"
            // TODO: RFC3986 URLs
            || path == "success/unit/import/urls/emptyPath0"
            || path == "success/unit/import/urls/emptyPath1"
            || path == "success/unit/import/urls/emptyPathSegment"
            // TODO: toMap
            || path == "success/toMap"
        },
    )?;

    make_test_module(
        &mut file,
        "binary_decoding",
        "binary-decode/",
        "BinaryDecoding",
        |path| {
            false
            // TODO: projection by expression
            || path == "success/unit/RecordProjectFields"
            || path == "success/unit/recordProjectionByExpression"
            // TODO: test is wrong
            || path == "success/unit/BuiltinNaturalSubtract"
            // TODO: toMap
            || path == "success/unit/ToMap"
            || path == "success/unit/ToMapAnnotated"
        },
    )?;

    make_test_module(
        &mut file,
        "beta_normalize",
        "normalization/",
        "Normalization",
        |path| {
            // We don't support bignums
            path == "success/simple/integerToDouble"
            // Too slow
            || path == "success/remoteSystems"
            // TODO: projection by expression
            || path == "success/unit/RecordProjectionByTypeEmpty"
            || path == "success/unit/RecordProjectionByTypeNonEmpty"
            || path == "success/unit/RecordProjectionByTypeNormalizeProjection"
            // TODO: fix Double/show
            || path == "success/prelude/JSON/number/1"
            // TODO: toMap
            || path == "success/unit/EmptyToMap"
            || path == "success/unit/ToMap"
            || path == "success/unit/ToMapWithType"
            // TODO: Normalize field selection further by inspecting the argument
            || path == "success/simplifications/rightBiasedMergeWithinRecordProjectionWithinFieldSelection0"
            || path == "success/simplifications/rightBiasedMergeWithinRecordProjectionWithinFieldSelection1"
            || path == "success/simplifications/rightBiasedMergeWithinRecursiveRecordMergeWithinFieldselection"
            || path == "success/unit/RecordProjectionByTypeWithinFieldSelection"
            || path == "success/unit/RecordProjectionWithinFieldSelection"
            || path == "success/unit/RecursiveRecordMergeWithinFieldSelection0"
            || path == "success/unit/RecursiveRecordMergeWithinFieldSelection1"
            || path == "success/unit/RecursiveRecordMergeWithinFieldSelection2"
            || path == "success/unit/RightBiasedMergeWithinFieldSelection0"
            || path == "success/unit/RightBiasedMergeWithinFieldSelection1"
            || path == "success/unit/RightBiasedMergeWithinFieldSelection2"
        },
    )?;

    make_test_module(
        &mut file,
        "alpha_normalize",
        "alpha-normalization/",
        "AlphaNormalization",
        |_| false,
    )?;

    make_test_module(
        &mut file,
        "typecheck",
        "typecheck/",
        "Typecheck",
        |path| {
            false
            // TODO: Enable imports in typecheck tests
            || path == "failure/importBoundary"
            // Too slow
            || path == "success/prelude"
            // TODO: Inline headers
            || path == "failure/customHeadersUsingBoundVariable"
            // TODO: projection by expression
            || path == "failure/unit/RecordProjectionByTypeFieldTypeMismatch"
            || path == "failure/unit/RecordProjectionByTypeNotPresent"
            // TODO: toMap
            || path == "failure/unit/EmptyToMap"
            || path == "failure/unit/HeterogenousToMap"
            || path == "failure/unit/MistypedToMap1"
            || path == "failure/unit/MistypedToMap2"
            || path == "failure/unit/MistypedToMap3"
            || path == "failure/unit/MistypedToMap4"
            || path == "failure/unit/NonRecordToMap"
        },
    )?;

    make_test_module(
        &mut file,
        "type_inference",
        "type-inference/",
        "TypeInference",
        |path| {
            false
            // TODO: projection by expression
            || path == "success/unit/RecordProjectionByType"
            || path == "success/unit/RecordProjectionByTypeEmpty"
            || path == "success/unit/RecordProjectionByTypeJudgmentalEquality"
            // TODO: toMap
            || path == "success/unit/ToMap"
            || path == "success/unit/ToMapAnnotated"
        },
    )?;

    Ok(())
}
