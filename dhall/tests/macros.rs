#[macro_export]
macro_rules! assert_eq_ {
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
macro_rules! run_spec_test {
    (normalization, $path:expr) => {
        let base_path = concat!("../dhall-lang/tests/", $path);
        run_test(base_path, Feature::Normalization, ExpectedResult::Success);
    };
    (parser, $path:expr) => {
        let base_path = concat!("../dhall-lang/tests/", $path);
        run_test(base_path, Feature::Parser, ExpectedResult::Success);
    };
    (parser_failure, $path:expr) => {
        let base_path = concat!("../dhall-lang/tests/", $path);
        run_test(base_path, Feature::Parser, ExpectedResult::Failure);
    };
    (typecheck_success, $path:expr) => {
        let base_path = concat!("../dhall-lang/tests/", $path);
        run_test(base_path, Feature::Typecheck, ExpectedResult::Success);
    };
    (typecheck_failure, $path:expr) => {
        let base_path = concat!("../dhall-lang/tests/", $path);
        run_test(base_path, Feature::Typecheck, ExpectedResult::Failure);
    };
}

#[macro_export]
macro_rules! make_spec_test {
    ($type:ident, $name:ident, $path:expr) => {
        #[test]
        #[allow(non_snake_case)]
        #[allow(unused_variables)]
        #[allow(unused_imports)]
        fn $name() {
            use crate::macros::*;
            use dhall::*;
            use dhall_core::*;
            use std::thread;

            // The parser stack overflows even on small files
            // when compiled without optimizations
            thread::Builder::new()
                .stack_size(4 * 1024 * 1024)
                .spawn(move || {
                    run_spec_test!($type, $path);
                })
                .unwrap()
                .join()
                .unwrap();
        }
    };
}

use dhall::*;
use dhall_core::*;
use std::path::PathBuf;

pub enum Feature {
    Parser,
    Normalization,
    Typecheck,
}

pub enum ExpectedResult {
    Success,
    Failure,
}

pub fn read_dhall_file<'i>(file_path: &str) -> Result<Expr<X, X>, DhallError> {
    load_dhall_file(&PathBuf::from(file_path), true)
}

pub fn run_test(base_path: &str, feature: Feature, expected: ExpectedResult) {
    use self::{ExpectedResult, Feature};
    match (feature, expected) {
        (Feature::Parser, ExpectedResult::Success) => {
            let expr_file_path = base_path.to_owned() + "A.dhall";
            let expected_file_path = base_path.to_owned() + "B.dhallb";
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

            assert_eq!(expr, expected);
        }
        (Feature::Parser, ExpectedResult::Failure) => {
            let file_path = base_path.to_owned() + ".dhall";
            let err = read_dhall_file(&file_path).unwrap_err();
            match err {
                DhallError::ParseError(_) => {}
                e => panic!("Expected parse error, got: {:?}", e),
            }
        }
        (Feature::Normalization, ExpectedResult::Success) => {
            let expr_file_path = base_path.to_owned() + "A.dhall";
            let expected_file_path = base_path.to_owned() + "B.dhall";
            let expr = read_dhall_file(&expr_file_path).unwrap();
            let expected = read_dhall_file(&expected_file_path).unwrap();

            assert_eq_!(
                normalize::<_, X, _>(&expr),
                normalize::<_, X, _>(&expected)
            );
        }
        (Feature::Typecheck, ExpectedResult::Failure) => {
            let file_path = base_path.to_owned() + ".dhall";
            let expr = read_dhall_file(&file_path).unwrap();
            typecheck::type_of(&expr).unwrap_err();
        }
        (Feature::Typecheck, ExpectedResult::Success) => {
            let expr_file_path = base_path.to_owned() + "A.dhall";
            let expected_file_path = base_path.to_owned() + "B.dhall";
            let expr = read_dhall_file(&expr_file_path).unwrap();
            let expected = read_dhall_file(&expected_file_path).unwrap();
            typecheck::type_of(&Expr::Annot(bx(expr), bx(expected))).unwrap();
        }
        _ => unimplemented!(),
    }
}
