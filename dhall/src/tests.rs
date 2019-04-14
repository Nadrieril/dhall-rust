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
            run_test_with_bigger_stack($path, Feature::$type, Status::$status)
                .unwrap();
        }
    };
}

use crate::error::{Error, Result};
use crate::expr::Parsed;
use crate::traits::DynamicType;
use std::path::PathBuf;

#[derive(Copy, Clone)]
pub enum Feature {
    Parser,
    Import,
    Normalization,
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

fn parse_binary_file_str<'i>(file_path: &str) -> Result<Parsed> {
    Parsed::parse_binary_file(&PathBuf::from(file_path))
}

pub fn run_test_with_bigger_stack(
    base_path: &str,
    feature: Feature,
    status: Status,
) -> std::result::Result<(), String> {
    // Many tests stack overflow in debug mode
    let base_path: String = base_path.to_string();
    std::thread::Builder::new()
        .stack_size(4 * 1024 * 1024)
        .spawn(move || {
            run_test(&base_path, feature, status)
                .map_err(|e| e.to_string())
                .map(|_| ())
        })
        .unwrap()
        .join()
        .unwrap()
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
        Import => "import/",
        Normalization => "normalization/",
        Typecheck => "typecheck/",
        TypeInference => "type-inference/",
    };
    let status_prefix = match status {
        Success => "success/",
        Failure => "failure/",
    };
    let base_path = "../dhall-lang/tests/".to_owned()
        + feature_prefix
        + status_prefix
        + base_path;
    match status {
        Success => {
            let expr_file_path = base_path.clone() + "A.dhall";
            let expr = parse_file_str(&expr_file_path)?;

            if let Parser = feature {
                let expected_file_path = base_path + "B.dhallb";
                let expected = parse_binary_file_str(&expected_file_path)?;

                assert_eq_pretty!(expr, expected);

                // Round-trip pretty-printer
                let expr_string = expr.to_string();
                let expr: Parsed = crate::de::from_str(&expr_string, None)?;
                assert_eq!(expr, expected);

                return Ok(());
            }

            let expr = expr.resolve()?;

            let expected_file_path = base_path + "B.dhall";
            let expected = parse_file_str(&expected_file_path)?
                .resolve()?
                .skip_typecheck()
                .skip_normalize();

            match feature {
                Parser => unreachable!(),
                Import => {
                    // Not sure whether to normalize or not
                    let expr = expr.skip_typecheck().skip_normalize();
                    assert_eq_display!(expr, expected);
                }
                Typecheck => {
                    expr.typecheck_with(&expected.into_type())?;
                }
                TypeInference => {
                    let expr = expr.typecheck()?;
                    let ty = expr.get_type()?;
                    assert_eq_display!(ty.as_normalized()?, &expected);
                }
                Normalization => {
                    let expr = expr.skip_typecheck().normalize();
                    assert_eq_display!(expr, expected);
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
                Import => {
                    parse_file_str(&file_path)?.resolve().unwrap_err();
                }
                Normalization => unreachable!(),
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
