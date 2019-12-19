#[cfg(not(test))]
use assert_eq as assert_eq_pretty;
#[cfg(test)]
use pretty_assertions::assert_eq as assert_eq_pretty;

macro_rules! assert_eq_display {
    ($left:expr, $right:expr) => {{
        match (&$left, &$right) {
            (left_val, right_val) => {
                if !(*left_val == *right_val) {
                    panic!(
                        r#"assertion failed: `(left == right)`
 left: `{}`,
right: `{}`"#,
                        left_val, right_val
                    )
                }
            }
        }
    }};
}

/// Wrapper around string slice that makes debug output `{:?}` to print string same way as `{}`.
/// Used in different `assert*!` macros in combination with `pretty_assertions` crate to make
/// test failures to show nice diffs.
#[derive(PartialEq, Eq)]
#[doc(hidden)]
pub struct PrettyString(String);

/// Make diff to display string as multi-line string
impl std::fmt::Debug for PrettyString {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

macro_rules! assert_eq_pretty_str {
    ($left:expr, $right:expr) => {
        assert_eq_pretty!(
            PrettyString($left.to_string()),
            PrettyString($right.to_string())
        );
    };
}

use std::fs::File;
use std::io::{Read, Write};
use std::path::PathBuf;

use crate::semantics::error::{Error, Result};
use crate::semantics::phase::Parsed;

#[allow(dead_code)]
#[derive(Clone)]
pub enum Test<'a> {
    ParserSuccess(&'a str, &'a str),
    ParserFailure(&'a str),
    Printer(&'a str, &'a str),
    BinaryEncoding(&'a str, &'a str),
    BinaryDecodingSuccess(&'a str, &'a str),
    BinaryDecodingFailure(&'a str),
    ImportSuccess(&'a str, &'a str),
    ImportFailure(&'a str),
    TypeInferenceSuccess(&'a str, &'a str),
    TypeInferenceFailure(&'a str),
    TypeError(&'a str),
    Normalization(&'a str, &'a str),
    AlphaNormalization(&'a str, &'a str),
}

fn parse_file_str(file_path: &str) -> Result<Parsed> {
    Parsed::parse_file(&PathBuf::from(file_path))
}

#[allow(dead_code)]
pub fn run_test_stringy_error(
    test: Test<'_>,
) -> std::result::Result<(), String> {
    run_test(test).map_err(|e| e.to_string()).map(|_| ())
}

pub fn run_test(test: Test<'_>) -> Result<()> {
    use self::Test::*;
    match test {
        ParserSuccess(expr_file_path, expected_file_path) => {
            let expr = parse_file_str(&expr_file_path)?;
            // This exercices both parsing and binary decoding
            // Compare parse/decoded
            let expected =
                Parsed::parse_binary_file(&PathBuf::from(expected_file_path))?;
            assert_eq_pretty!(expr, expected);
        }
        ParserFailure(file_path) => {
            let err = parse_file_str(&file_path).unwrap_err();
            match &err {
                Error::Parse(_) => {}
                Error::IO(e) if e.kind() == std::io::ErrorKind::InvalidData => {
                }
                e => panic!("Expected parse error, got: {:?}", e),
            }
        }
        BinaryEncoding(expr_file_path, expected_file_path) => {
            let expr = parse_file_str(&expr_file_path)?;
            let mut expected_data = Vec::new();
            {
                File::open(&PathBuf::from(&expected_file_path))?
                    .read_to_end(&mut expected_data)?;
            }
            let expr_data = expr.encode()?;

            // Compare bit-by-bit
            if expr_data != expected_data {
                // use std::io::Write;
                // File::create(&expected_file_path)?.write_all(&expr_data)?;
                // Pretty-print difference
                assert_eq_pretty!(
                    serde_cbor::de::from_slice::<serde_cbor::value::Value>(
                        &expr_data
                    )
                    .unwrap(),
                    serde_cbor::de::from_slice::<serde_cbor::value::Value>(
                        &expected_data
                    )
                    .unwrap()
                );
                // If difference was not visible in the cbor::Value
                assert_eq!(expr_data, expected_data);
            }
        }
        BinaryDecodingSuccess(expr_file_path, expected_file_path) => {
            let expr =
                Parsed::parse_binary_file(&PathBuf::from(expr_file_path))?;
            let expected = parse_file_str(&expected_file_path)?;
            assert_eq_pretty!(expr, expected);
        }
        BinaryDecodingFailure(file_path) => {
            Parsed::parse_binary_file(&PathBuf::from(file_path)).unwrap_err();
        }
        Printer(expr_file_path, _) => {
            let expected = parse_file_str(&expr_file_path)?;
            // Round-trip pretty-printer
            let expr: Parsed = Parsed::parse_str(&expected.to_string())?;
            assert_eq!(expr, expected);
        }
        ImportSuccess(expr_file_path, expected_file_path) => {
            let expr = parse_file_str(&expr_file_path)?
                .resolve()?
                .typecheck()?
                .normalize();
            let expected = parse_file_str(&expected_file_path)?
                .resolve()?
                .typecheck()?
                .normalize();

            assert_eq_display!(expr, expected);
        }
        ImportFailure(file_path) => {
            parse_file_str(&file_path)?.resolve().unwrap_err();
        }
        TypeInferenceSuccess(expr_file_path, expected_file_path) => {
            let expr =
                parse_file_str(&expr_file_path)?.resolve()?.typecheck()?;
            let ty = expr.get_type()?.normalize();
            let expected = parse_file_str(&expected_file_path)?
                .resolve()?
                .typecheck()?
                .normalize();
            assert_eq_display!(ty, expected);
        }
        TypeInferenceFailure(file_path) => {
            let mut res =
                parse_file_str(&file_path)?.skip_resolve()?.typecheck();
            if let Ok(e) = &res {
                // If e did typecheck, check that get_type fails
                res = e.get_type();
            }
            res.unwrap_err();
        }
        // Checks the output of the type error against a text file. If the text file doesn't exist,
        // we instead write to it the output we got. This makes it easy to update those files: just
        // `rm -r dhall/tests/type-errors` and run the tests again.
        TypeError(file_path) => {
            let mut res =
                parse_file_str(&file_path)?.skip_resolve()?.typecheck();
            let file_path = PathBuf::from(file_path);
            let error_file_path = file_path
                .strip_prefix("../dhall-lang/tests/type-inference/failure/")
                .unwrap();
            let error_file_path =
                PathBuf::from("tests/type-errors/").join(error_file_path);
            let error_file_path = error_file_path.with_extension("txt");
            if let Ok(e) = &res {
                // If e did typecheck, check that get_type fails
                res = e.get_type();
            }
            let err: Error = res.unwrap_err().into();

            if error_file_path.is_file() {
                let expected_msg = std::fs::read_to_string(error_file_path)?;
                let msg = format!("{}\n", err);
                assert_eq_pretty_str!(msg, expected_msg);
            } else {
                std::fs::create_dir_all(error_file_path.parent().unwrap())?;
                let mut file = File::create(error_file_path)?;
                writeln!(file, "{}", err)?;
            }
        }
        Normalization(expr_file_path, expected_file_path) => {
            let expr = parse_file_str(&expr_file_path)?
                .resolve()?
                .typecheck()?
                .normalize();
            let expected = parse_file_str(&expected_file_path)?
                .resolve()?
                .typecheck()?
                .normalize();

            assert_eq_display!(expr, expected);
        }
        AlphaNormalization(expr_file_path, expected_file_path) => {
            let expr = parse_file_str(&expr_file_path)?
                .resolve()?
                .typecheck()?
                .normalize()
                .to_expr_alpha();
            let expected = parse_file_str(&expected_file_path)?
                .resolve()?
                .typecheck()?
                .normalize();

            assert_eq_display!(expr, expected.to_expr());
        }
    }
    Ok(())
}

#[cfg(test)]
mod spec {
    macro_rules! make_spec_test {
        ($type:expr, $name:ident) => {
            #[test]
            #[allow(non_snake_case)]
            fn $name() {
                use crate::tests::Test::*;
                use crate::tests::*;
                match run_test_stringy_error($type) {
                    Ok(_) => {}
                    Err(s) => panic!(s),
                }
            }
        };
    }

    // See build.rs
    include!(concat!(env!("OUT_DIR"), "/spec_tests.rs"));
}
