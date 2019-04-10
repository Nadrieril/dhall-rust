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
    ($type:ident, $name:ident, $path:expr) => {
        #[test]
        #[allow(non_snake_case)]
        fn $name() {
            use crate::tests::*;
            run_test($path, Feature::$type);
        }
    };
}

use crate::error::{Error, Result};
use crate::expr::Parsed;
use crate::*;
use dhall_core::*;
use dhall_generator as dhall;
use std::path::PathBuf;

#[allow(dead_code)]
pub enum Feature {
    ParserSuccess,
    ParserFailure,
    Normalization,
    TypecheckSuccess,
    TypecheckFailure,
    TypeInferenceSuccess,
    TypeInferenceFailure,
}

// Deprecated
fn read_dhall_file<'i>(file_path: &str) -> Result<Expr<X, X>> {
    crate::imports::load_dhall_file(&PathBuf::from(file_path), true)
}

fn parse_file_str<'i>(file_path: &str) -> Result<Parsed> {
    Parsed::parse_file(&PathBuf::from(file_path))
}

fn parse_binary_file_str<'i>(file_path: &str) -> Result<Parsed> {
    Parsed::parse_binary_file(&PathBuf::from(file_path))
}

pub fn run_test(base_path: &str, feature: Feature) {
    use self::Feature::*;
    let base_path_prefix = match feature {
        ParserSuccess => "parser/success/",
        ParserFailure => "parser/failure/",
        Normalization => "normalization/success/",
        TypecheckSuccess => "typecheck/success/",
        TypecheckFailure => "typecheck/failure/",
        TypeInferenceSuccess => "type-inference/success/",
        TypeInferenceFailure => "type-inference/failure/",
    };
    let base_path =
        "../dhall-lang/tests/".to_owned() + base_path_prefix + base_path;
    match feature {
        ParserSuccess => {
            let expr_file_path = base_path.clone() + "A.dhall";
            let expected_file_path = base_path + "B.dhallb";
            let expr = parse_file_str(&expr_file_path)
                .map_err(|e| println!("{}", e))
                .unwrap();

            let expected = parse_binary_file_str(&expected_file_path)
                .map_err(|e| println!("{}", e))
                .unwrap();

            assert_eq_pretty!(expr, expected);

            // Round-trip pretty-printer
            let expr: Parsed =
                crate::from_str(&expr.to_string(), None).unwrap();
            assert_eq!(expr, expected);
        }
        ParserFailure => {
            let file_path = base_path + ".dhall";
            let err = parse_file_str(&file_path).unwrap_err();
            match err {
                Error::Parse(_) => {}
                e => panic!("Expected parse error, got: {:?}", e),
            }
        }
        Normalization => {
            let expr_file_path = base_path.clone() + "A.dhall";
            let expected_file_path = base_path + "B.dhall";
            let expr = parse_file_str(&expr_file_path)
                .unwrap()
                .resolve()
                .unwrap()
                .skip_typecheck()
                .normalize();
            let expected = parse_file_str(&expected_file_path)
                .unwrap()
                .resolve()
                .unwrap()
                .skip_typecheck()
                .normalize();

            assert_eq_display!(expr, expected);
        }
        TypecheckFailure => {
            let file_path = base_path + ".dhall";
            parse_file_str(&file_path)
                .unwrap()
                .skip_resolve()
                .unwrap()
                .typecheck()
                .unwrap_err();
        }
        TypecheckSuccess => {
            // Many tests stack overflow in debug mode
            std::thread::Builder::new()
                .stack_size(4 * 1024 * 1024)
                .spawn(|| {
                    let expr_file_path = base_path.clone() + "A.dhall";
                    let expected_file_path = base_path + "B.dhall";
                    let expr = rc(read_dhall_file(&expr_file_path).unwrap());
                    let expected =
                        rc(read_dhall_file(&expected_file_path).unwrap());
                    typecheck::type_of(dhall::subexpr!(expr: expected))
                        .unwrap();
                })
                .unwrap()
                .join()
                .unwrap();
        }
        TypeInferenceFailure => {
            let file_path = base_path + ".dhall";
            parse_file_str(&file_path)
                .unwrap()
                .skip_resolve()
                .unwrap()
                .typecheck()
                .unwrap_err();
        }
        TypeInferenceSuccess => {
            let expr_file_path = base_path.clone() + "A.dhall";
            let expected_file_path = base_path + "B.dhall";
            let expr = parse_file_str(&expr_file_path)
                .unwrap()
                .skip_resolve()
                .unwrap()
                .typecheck()
                .unwrap();
            let ty = expr.get_type().as_normalized().unwrap();
            let expected = parse_file_str(&expected_file_path)
                .unwrap()
                .skip_resolve()
                .unwrap()
                .skip_typecheck()
                .skip_normalize();
            assert_eq_display!(ty, &expected);
        }
    }
}
