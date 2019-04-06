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
            use crate::common::*;
            run_test($path, Feature::$type);
        }
    };
}

use dhall::*;
use dhall_core::*;
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

pub fn read_dhall_file<'i>(file_path: &str) -> Result<Expr<X, X>, DhallError> {
    load_dhall_file(&PathBuf::from(file_path), true)
}

pub fn read_dhall_file_no_resolve_imports<'i>(
    file_path: &str,
) -> Result<ParsedExpr, DhallError> {
    load_dhall_file_no_resolve_imports(&PathBuf::from(file_path))
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
            let expr = read_dhall_file_no_resolve_imports(&expr_file_path)
                .map_err(|e| println!("{}", e))
                .unwrap();

            use std::fs::File;
            use std::io::Read;
            let mut file = File::open(expected_file_path).unwrap();
            let mut data = Vec::new();
            file.read_to_end(&mut data).unwrap();
            let expected = dhall::binary::decode(&data).unwrap();

            assert_eq_pretty!(expr, expected);

            // Round-trip pretty-printer
            let expr = parse_expr(&expr.to_string()).unwrap();
            assert_eq!(expr, expected);
        }
        ParserFailure => {
            let file_path = base_path + ".dhall";
            let err =
                read_dhall_file_no_resolve_imports(&file_path).unwrap_err();
            match err {
                DhallError::ParseError(_) => {}
                e => panic!("Expected parse error, got: {:?}", e),
            }
        }
        Normalization => {
            let expr_file_path = base_path.clone() + "A.dhall";
            let expected_file_path = base_path + "B.dhall";
            let expr = rc(read_dhall_file(&expr_file_path).unwrap());
            let expected = rc(read_dhall_file(&expected_file_path).unwrap());

            assert_eq_display!(normalize(expr), normalize(expected));
        }
        TypecheckFailure => {
            let file_path = base_path + ".dhall";
            let expr = rc(read_dhall_file(&file_path).unwrap());
            typecheck::type_of(expr).unwrap_err();
        }
        TypecheckSuccess => {
            let expr_file_path = base_path.clone() + "A.dhall";
            let expected_file_path = base_path + "B.dhall";
            let expr = rc(read_dhall_file(&expr_file_path).unwrap());
            let expected = rc(read_dhall_file(&expected_file_path).unwrap());
            typecheck::type_of(rc(ExprF::Annot(expr, expected))).unwrap();
        }
        TypeInferenceFailure => {
            let file_path = base_path + ".dhall";
            let expr = rc(read_dhall_file(&file_path).unwrap());
            typecheck::type_of(expr).unwrap_err();
        }
        TypeInferenceSuccess => {
            let expr_file_path = base_path.clone() + "A.dhall";
            let expected_file_path = base_path + "B.dhall";
            let expr = rc(read_dhall_file(&expr_file_path).unwrap());
            let expected = rc(read_dhall_file(&expected_file_path).unwrap());
            assert_eq_display!(typecheck::type_of(expr).unwrap(), expected);
        }
    }
}
