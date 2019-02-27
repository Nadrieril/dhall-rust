use dhall::*;

macro_rules! include_test_str {
    ($x:expr) => { include_str!(concat!("../dhall-lang/tests/", $x, ".dhall")) };
}

macro_rules! include_test_strs_ab {
    ($x:expr) => { (include_test_str!(concat!($x, "A")), include_test_str!(concat!($x, "B"))) };
}

macro_rules! test_normalization {
    ($x:expr) => {
        let (expr_str, expected_str) = include_test_strs_ab!($x);
        let expr = parser::parse_expr(&expr_str).unwrap();
        let expected = parser::parse_expr(&expected_str).unwrap();
        assert_eq!(normalize::<_, X, _>(&expr), normalize::<_, X, _>(&expected));
    };
}


#[test]
fn test(){
    test_normalization!("normalization/success/simple/naturalPlus");
    test_normalization!("normalization/success/simple/naturalShow");
}
