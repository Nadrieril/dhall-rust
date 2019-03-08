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
            use dhall::imports::resolve_imports;
            use dhall::*;
            use dhall_core::*;
            use std::thread;

            // The parser stack overflows even on small files
            // when compiled without optimizations
            thread::Builder::new()
                .stack_size(16 * 1024 * 1024)
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
use dhall_core::parser::*;
use dhall_core::*;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

pub enum Feature {
    Parser,
    Normalization,
}

pub enum ExpectedResult {
    Success,
    Failure,
}

pub fn read_dhall_file<'i>(
    file_path: &str,
    mut buffer: &'i mut String,
) -> Result<Box<Expr<'i, X, Import>>, ParseError> {
    let mut file = File::open(&file_path).unwrap();
    file.read_to_string(&mut buffer).unwrap();
    parser::parse_expr(&*buffer)
}

pub fn run_test(base_path: &str, feature: Feature, expected: ExpectedResult) {
    use self::{ExpectedResult, Feature};
    let mut source_pool = Vec::new();
    match (feature, expected) {
        (Feature::Parser, ExpectedResult::Success) => {
            let file_path: PathBuf = (base_path.to_owned() + "A.dhall").into();
            let _expr = load_dhall_file(&file_path, &mut source_pool, true)
                .map_err(|e| println!("{}", e))
                .unwrap();
            // panic!("{:?}", _expr);
        }
        (Feature::Parser, ExpectedResult::Failure) => {
            let file_path: PathBuf = (base_path.to_owned() + ".dhall").into();
            let err = load_dhall_file(&file_path, &mut source_pool, true).unwrap_err();
            match err {
                DhallError::ParseError(_) => {},
                e => panic!("Expected parse error, got: {:?}", e),
            }
        }
        (Feature::Normalization, ExpectedResult::Success) => {
            let expr_file_path = base_path.to_owned() + "A.dhall";
            let mut expr_buffer = String::new();
            let expr = read_dhall_file(&expr_file_path, &mut expr_buffer).unwrap();
            let expected_file_path = base_path.to_owned() + "B.dhall";
            let mut expected_buffer = String::new();
            let expected = read_dhall_file(&expected_file_path, &mut expected_buffer).unwrap();

            assert_eq_!(
                normalize::<_, _, X, _>(&expr),
                normalize::<_, _, X, _>(&expected)
            );
        }
        _ => unimplemented!(),
    }
}
