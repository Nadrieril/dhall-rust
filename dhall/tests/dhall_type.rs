#![feature(proc_macro_hygiene)]
use dhall::Type;
use dhall_generator::dhall_expr;

#[test]
fn test_dhall_type() {
    assert_eq!(bool::get_type(), dhall_expr!(Bool));
    assert_eq!(String::get_type(), dhall_expr!(Text));
    assert_eq!(
        <(bool, Option<String>)>::get_type(),
        dhall_expr!({ _1: Bool, _2: Optional Text })
    );

    #[derive(dhall::Type)]
    #[allow(dead_code)]
    struct A {
        field1: bool,
        field2: Option<bool>,
    }
    assert_eq!(
        <A as dhall::Type>::get_type(),
        dhall_expr!({ field1: Bool, field2: Optional Bool })
    );

    #[derive(Type)]
    #[allow(dead_code)]
    struct B<'a, T: 'a> {
        field1: &'a T,
        field2: Option<T>,
    }
    assert_eq!(<B<'static, bool>>::get_type(), A::get_type());

    #[derive(Type)]
    #[allow(dead_code)]
    struct C<T>(T, Option<String>);
    assert_eq!(<C<bool>>::get_type(), <(bool, Option<String>)>::get_type());

    #[derive(Type)]
    #[allow(dead_code)]
    struct D();
    assert_eq!(
        <C<D>>::get_type(),
        dhall_expr!({ _1: {}, _2: Optional Text })
    );

    #[derive(Type)]
    #[allow(dead_code)]
    enum E<T> {
        A(T),
        B(String),
    };
    assert_eq!(<E<bool>>::get_type(), dhall_expr!(< A: Bool | B: Text >));
}
