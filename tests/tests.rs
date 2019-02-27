use dhall::*;

#[test]
fn test(){
    let buffer_expr = String::from(include_str!("../dhall-lang/tests/normalization/success/simple/naturalPlusA.dhall"));
    let buffer_expected = String::from(include_str!("../dhall-lang/tests/normalization/success/simple/naturalPlusB.dhall"));
    let expr = parser::parse_expr(&buffer_expr).unwrap();
    let expected = parser::parse_expr(&buffer_expected).unwrap();
    // let type_expr = typecheck::type_of(&expr).unwrap();
    // let normalized = normalize::<_, X, _>(&expr);
    assert_eq!(normalize::<_, X, _>(&expr), normalize::<_, X, _>(&expected));
}
