#[macro_export]
macro_rules! include_test_str {
    ($x:expr) => { include_str!(concat!("../../dhall-lang/tests/", $x, ".dhall")) };
}

#[macro_export]
macro_rules! include_test_strs_ab {
    ($x:expr) => { (include_test_str!(concat!($x, "A")), include_test_str!(concat!($x, "B"))) };
}

#[macro_export]
macro_rules! parse_str {
    ($str:expr) => {
        {
            let pest_expr = parser::parse_expr_pest(&$str).map_err(|e| println!("{}", e)).unwrap();
            // Check with old parser
            match parser::parse_expr_lalrpop(&$str) {
                Ok(larlpop_expr) => assert_eq!(pest_expr, larlpop_expr),
                Err(_) => {},
            };
            // panic!("{:?}", pest_expr);
            pest_expr
        }
    };
}

#[macro_export]
macro_rules! run_spec_test {
    (normalization, $path:expr) => {
        let (expr_str, expected_str) = include_test_strs_ab!($path);
        let expr = parse_str!(expr_str);
        let expected = parse_str!(expected_str);
        // assert_eq!(normalize::<_, X, _>(&expr), normalize::<_, X, _>(&expected));
    };
    (parser, $path:expr) => {
        let expr_str = include_test_str!(concat!($path, "A"));
        parse_str!(expr_str);
    };
    (parser_failure, $path:expr) => {
        let expr_str = include_test_str!($path);
        parser::parse_expr_pest(&expr_str).unwrap_err();
    };
}

#[macro_export]
macro_rules! make_spec_test {
    ($type:ident, $name:ident, $path:expr) => {
        #[test]
        #[allow(non_snake_case)]
        #[allow(unused_variables)]
        #[allow(unused_imports)]
        fn $name(){
            use std::thread;
            use dhall::*;

            thread::Builder::new().stack_size(16 * 1024 * 1024).spawn(move || {
                run_spec_test!($type, $path);
            }).unwrap().join().unwrap();
        }
    };
}
