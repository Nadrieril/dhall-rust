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

#[macro_export]
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

use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

use crate::error::{Error, Result};
use crate::phase::Parsed;

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
    TypecheckSuccess(&'a str, &'a str),
    TypecheckFailure(&'a str),
    TypeInferenceSuccess(&'a str, &'a str),
    TypeInferenceFailure(&'a str),
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
        TypecheckSuccess(expr_file_path, expected_file_path) => {
            let expr = parse_file_str(&expr_file_path)?.resolve()?;
            let expected = parse_file_str(&expected_file_path)?
                .resolve()?
                .typecheck()?
                .normalize();

            expr.typecheck_with(&expected.into_typed())?.get_type()?;
        }
        TypecheckFailure(file_path) => {
            let res = parse_file_str(&file_path)?.skip_resolve()?.typecheck();
            match res {
                Err(_) => {}
                // If e did typecheck, check that it doesn't have a type
                Ok(e) => {
                    e.get_type().unwrap_err();
                }
            }
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
            let res = parse_file_str(&file_path)?.skip_resolve()?.typecheck();
            match res {
                Err(_) => {}
                // If e did typecheck, check that it doesn't have a type
                Ok(e) => {
                    e.get_type().unwrap_err();
                }
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
    // See build.rs
    include!(concat!(env!("OUT_DIR"), "/spec_tests.rs"));
}
