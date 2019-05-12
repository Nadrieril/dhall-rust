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
    let feature_prefix = match feature {
        Parser => "parser/",
        Printer => "parser/",
        BinaryEncoding => "parser/",
        Import => "import/",
        Normalization => "normalization/",
        AlphaNormalization => "alpha-normalization/",
        Typecheck => "typecheck/",
        TypeInference => "type-inference/",
    };
    let base_path =
        "../dhall-lang/tests/".to_owned() + feature_prefix + base_path;
    match status {
        Success => {
            let expr_file_path = base_path.clone() + "A.dhall";
            let expr = parse_file_str(&expr_file_path)?;

            match feature {
                Parser => {
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
                .skip_typecheck()
                .normalize();

            match feature {
                Parser | Printer | BinaryEncoding => unreachable!(),
                Import => {
                    let expr = expr.skip_typecheck().normalize();
                    assert_eq_display!(expr, expected);
                }
                Typecheck => {
                    expr.typecheck_with(&expected.to_type())?;
                }
                TypeInference => {
                    let expr = expr.typecheck()?;
                    let ty = expr.get_type()?.into_owned();
                    assert_eq_display!(ty.to_normalized(), expected);
                }
                Normalization => {
                    let expr = expr.skip_typecheck().normalize();
                    assert_eq_display!(expr, expected);
                }
                AlphaNormalization => {
                    let expr =
                        expr.skip_typecheck().normalize().to_expr_alpha();
                    assert_eq_display!(expr, expected.to_expr());
                }
            }
        }
        Failure => {
            let file_path = base_path + ".dhall";
            match feature {
                Parser => {
                    let err = parse_file_str(&file_path).unwrap_err();
                    match err {
                        Error::Parse(_) => {}
                        e => panic!("Expected parse error, got: {:?}", e),
                    }
                }
                Printer | BinaryEncoding => unreachable!(),
                Import => {
                    parse_file_str(&file_path)?.resolve().unwrap_err();
                }
                Normalization | AlphaNormalization => unreachable!(),
                Typecheck | TypeInference => {
                    parse_file_str(&file_path)?
                        .skip_resolve()?
                        .typecheck()
                        .unwrap_err();
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
