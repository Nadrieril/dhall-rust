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
    ($type:ident, $status:ident, $name:ident, $path:expr) => {
        #[test]
        #[allow(non_snake_case)]
        fn $name() {
            use crate::tests::*;
            match run_test_stringy_error($path, Feature::$type, Status::$status)
            {
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

#[derive(Copy, Clone)]
pub enum Feature {
    Parser,
    Printer,
    BinaryEncoding,
    BinaryDecoding,
    Import,
    Normalization,
    AlphaNormalization,
    Typecheck,
    TypeInference,
}

#[derive(Copy, Clone)]
pub enum Status {
    Success,
    Failure,
}

fn parse_file_str<'i>(file_path: &str) -> Result<Parsed> {
    Parsed::parse_file(&PathBuf::from(file_path))
}

pub fn run_test_stringy_error(
    base_path: &str,
    feature: Feature,
    status: Status,
) -> std::result::Result<(), String> {
    let base_path: String = base_path.to_string();
    run_test(&base_path, feature, status)
        .map_err(|e| e.to_string())
        .map(|_| ())
}

pub fn run_test(
    base_path: &str,
    feature: Feature,
    status: Status,
) -> Result<()> {
    use self::Feature::*;
    use self::Status::*;
    let base_path = base_path.to_owned();
    match status {
        Success => {
            match feature {
                BinaryDecoding => {
                    let expr_file_path = base_path.clone() + "A.dhallb";
                    let expr_file_path = PathBuf::from(&expr_file_path);
                    let mut expr_data = Vec::new();
                    {
                        File::open(&expr_file_path)?
                            .read_to_end(&mut expr_data)?;
                    }
                    let expr = Parsed::parse_binary(&expr_data)?;
                    let expected_file_path = base_path + "B.dhall";
                    let expected = parse_file_str(&expected_file_path)?;
                    assert_eq_pretty!(expr, expected);

                    return Ok(());
                }
                _ => {}
            }
            let expr_file_path = base_path.clone() + "A.dhall";
            let expr = parse_file_str(&expr_file_path)?;

            match feature {
                Parser => {
                    // This exercices both parsing and binary decoding
                    // Compare parse/decoded
                    let expected_file_path = base_path + "B.dhallb";
                    let expected_file_path = PathBuf::from(&expected_file_path);
                    let mut expected_data = Vec::new();
                    {
                        File::open(&expected_file_path)?
                            .read_to_end(&mut expected_data)?;
                    }
                    let expected = Parsed::parse_binary(&expected_data)?;
                    assert_eq_pretty!(expr, expected);

                    return Ok(());
                }
                Printer => {
                    // Round-trip pretty-printer
                    let expr_string = expr.to_string();
                    let expected = expr;
                    let expr: Parsed = Parsed::parse_str(&expr_string)?;
                    assert_eq!(expr, expected);

                    return Ok(());
                }
                BinaryEncoding => {
                    let expected_file_path = base_path + "B.dhallb";
                    let expected_file_path = PathBuf::from(&expected_file_path);
                    let mut expected_data = Vec::new();
                    {
                        File::open(&expected_file_path)?
                            .read_to_end(&mut expected_data)?;
                    }
                    let expr_data = expr.encode()?;

                    // Compare bit-by-bit
                    if expr_data != expected_data {
                        // use std::io::Write;
                        // File::create(&expected_file_path)?.write_all(&expr_data)?;
                        // Pretty-print difference
                        assert_eq_pretty!(
                            serde_cbor::de::from_slice::<
                                serde_cbor::value::Value,
                            >(&expr_data)
                            .unwrap(),
                            serde_cbor::de::from_slice::<
                                serde_cbor::value::Value,
                            >(&expected_data)
                            .unwrap()
                        );
                        // If difference was not visible in the cbor::Value
                        assert_eq!(expr_data, expected_data);
                    }

                    return Ok(());
                }
                _ => {}
            }

            let expr = expr.resolve()?;

            let expected_file_path = base_path + "B.dhall";
            let expected = parse_file_str(&expected_file_path)?
                .resolve()?
                .typecheck()?
                .normalize();

            match feature {
                Parser | Printer | BinaryEncoding | BinaryDecoding => {
                    unreachable!()
                }
                Import => {
                    let expr = expr.typecheck()?.normalize();
                    assert_eq_display!(expr, expected);
                }
                Typecheck => {
                    expr.typecheck_with(&expected.into_typed())?.get_type()?;
                }
                TypeInference => {
                    let expr = expr.typecheck()?;
                    let ty = expr.get_type()?.into_owned().normalize();
                    assert_eq_display!(ty, expected);
                }
                Normalization => {
                    let expr = expr.typecheck()?.normalize();
                    assert_eq_display!(expr, expected);
                }
                AlphaNormalization => {
                    let expr = expr.typecheck()?.normalize().to_expr_alpha();
                    assert_eq_display!(expr, expected.to_expr());
                }
            }
        }
        Failure => {
            let file_path = base_path + ".dhall";
            match feature {
                Parser => {
                    let err = parse_file_str(&file_path).unwrap_err();
                    match &err {
                        Error::Parse(_) => {}
                        Error::IO(e)
                            if e.kind() == std::io::ErrorKind::InvalidData => {}
                        e => panic!("Expected parse error, got: {:?}", e),
                    }
                }
                Printer | BinaryEncoding => unreachable!(),
                BinaryDecoding => {
                    let expr_file_path = file_path + "b";
                    let mut expr_data = Vec::new();
                    {
                        File::open(&PathBuf::from(&expr_file_path))?
                            .read_to_end(&mut expr_data)?;
                    }
                    Parsed::parse_binary(&expr_data).unwrap_err();
                }
                Import => {
                    parse_file_str(&file_path)?.resolve().unwrap_err();
                }
                Normalization | AlphaNormalization => unreachable!(),
                Typecheck | TypeInference => {
                    let res =
                        parse_file_str(&file_path)?.skip_resolve()?.typecheck();
                    match res {
                        Err(_) => {}
                        // If e did typecheck, check that it doesn't have a type
                        Ok(e) => {
                            e.get_type().unwrap_err();
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

mod spec {
    // See build.rs
    include!(concat!(env!("OUT_DIR"), "/spec_tests.rs"));
}
