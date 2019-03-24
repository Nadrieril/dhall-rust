#![feature(proc_macro_hygiene)]
use dhall_core::*;
use dhall_generator::*;

#[derive(DhallType)]
struct A {
    _field1: bool,
    // field2: Option<bool>,
}

#[test]
fn test_dhall_type_a() {
    assert_eq!(A::dhall_type(), dhall_expr!(False));
    // assert_eq!(A::dhall_type(), dhall_expr!({ field1: Bool }));
}
