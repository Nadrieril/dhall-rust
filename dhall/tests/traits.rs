#![feature(proc_macro_hygiene)]
use dhall::de::{StaticType, Type};
use dhall_proc_macros::subexpr;
use dhall_syntax::{SubExpr, X};

#[test]
fn test_static_type() {
    fn mktype(x: SubExpr<X, X>) -> Type {
        Type::from_normalized_expr(x)
    }

    assert_eq!(bool::static_type(), mktype(subexpr!(Bool)));
    assert_eq!(String::static_type(), mktype(subexpr!(Text)));
    assert_eq!(
        <Option<bool>>::static_type(),
        mktype(subexpr!(Optional Bool))
    );
    assert_eq!(
        <(bool, Vec<String>)>::static_type(),
        mktype(subexpr!({ _1: Bool, _2: List Text }))
    );

    #[derive(dhall::de::StaticType)]
    #[allow(dead_code)]
    struct A {
        field1: bool,
        field2: Option<bool>,
    }
    assert_eq!(
        <A as dhall::de::StaticType>::static_type(),
        mktype(subexpr!({ field1: Bool, field2: Optional Bool }))
    );

    #[derive(StaticType)]
    #[allow(dead_code)]
    struct B<'a, T: 'a> {
        field1: &'a T,
        field2: Option<T>,
    }
    assert_eq!(<B<'static, bool>>::static_type(), A::static_type());

    #[derive(StaticType)]
    #[allow(dead_code)]
    struct C<T>(T, Option<String>);
    assert_eq!(
        <C<bool>>::static_type(),
        <(bool, Option<String>)>::static_type()
    );

    #[derive(StaticType)]
    #[allow(dead_code)]
    struct D();
    assert_eq!(
        <C<D>>::static_type(),
        mktype(subexpr!({ _1: {}, _2: Optional Text }))
    );

    #[derive(StaticType)]
    #[allow(dead_code)]
    enum E<T> {
        A(T),
        B(String),
    };
    assert_eq!(
        <E<bool>>::static_type(),
        mktype(subexpr!(< A: Bool | B: Text >))
    );

    #[derive(StaticType)]
    #[allow(dead_code)]
    enum F {
        A,
        B(bool),
    };
    assert_eq!(F::static_type(), mktype(subexpr!(< A | B: Bool >)));
}
