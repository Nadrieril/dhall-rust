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

            if cfg!(feature = "nothreads") {
                run_test($path, Feature::$type);
            } else {
                use std::thread;
                // The parser stack overflows even on small files
                // when compiled without optimizations
                thread::Builder::new()
                    .stack_size(8 * 1024 * 1024)
                    .spawn(move || {
                        run_test($path, Feature::$type);
                    })
                    .unwrap()
                    .join()
                    .unwrap();
            }
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
}

pub fn read_dhall_file<'i>(file_path: &str) -> Result<Expr<X, X>, DhallError> {
    load_dhall_file(&PathBuf::from(file_path), true)
}

pub fn run_test(base_path: &str, feature: Feature) {
    use self::Feature::*;
    let base_path_prefix = match feature {
        ParserSuccess => "parser/success/",
        ParserFailure => "parser/failure/",
        Normalization => "normalization/success/",
        TypecheckSuccess => "typecheck/success/",
        TypecheckFailure => "typecheck/failure/",
    };
    let base_path =
        "../dhall-lang/tests/".to_owned() + base_path_prefix + base_path;
    match feature {
        ParserSuccess => {
            let expr_file_path = base_path.clone() + "A.dhall";
            let expected_file_path = base_path + "B.dhallb";
            let expr = read_dhall_file(&expr_file_path)
                .map_err(|e| println!("{}", e))
                .unwrap();

            use std::fs::File;
            use std::io::Read;
            let mut file = File::open(expected_file_path).unwrap();
            let mut data = Vec::new();
            file.read_to_end(&mut data).unwrap();
            let expected = dhall::binary::decode(&data).unwrap();
            let expected = dhall::imports::panic_imports(&expected);

            assert_eq_pretty!(expr, expected);

            // Round-trip pretty-printer
            let expr = parser::parse_expr(&expr.to_string()).unwrap();
            let expr = dhall::imports::panic_imports(&expr);
            assert_eq!(expr, expected);
        }
        ParserFailure => {
            let file_path = base_path + ".dhall";
            let err = read_dhall_file(&file_path).unwrap_err();
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
            typecheck::type_of(rc(Expr::Annot(expr, expected))).unwrap();
        }
    }
}
