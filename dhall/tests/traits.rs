#![feature(proc_macro_hygiene)]
use dhall::de::SimpleStaticType;
use dhall_proc_macros;
use dhall_syntax::{SubExpr, X};

#[test]
fn test_static_type() {
    fn mktype(x: SubExpr<X, X>) -> dhall::expr::SimpleType<'static> {
        x.into()
    }

    assert_eq!(
        bool::get_simple_static_type(),
        mktype(dhall_proc_macros::subexpr!(Bool))
    );
    assert_eq!(
        String::get_simple_static_type(),
        mktype(dhall_proc_macros::subexpr!(Text))
    );
    assert_eq!(
        <Option<bool>>::get_simple_static_type(),
        mktype(dhall_proc_macros::subexpr!(Optional Bool))
    );
    assert_eq!(
        <(bool, Option<String>)>::get_simple_static_type(),
        mktype(dhall_proc_macros::subexpr!({ _1: Bool, _2: Optional Text }))
    );

    #[derive(dhall::de::SimpleStaticType)]
    #[allow(dead_code)]
    struct A {
        field1: bool,
        field2: Option<bool>,
    }
    assert_eq!(
        <A as dhall::de::SimpleStaticType>::get_simple_static_type(),
        mktype(
            dhall_proc_macros::subexpr!({ field1: Bool, field2: Optional Bool })
        )
    );

    #[derive(SimpleStaticType)]
    #[allow(dead_code)]
    struct B<'a, T: 'a> {
        field1: &'a T,
        field2: Option<T>,
    }
    assert_eq!(
        <B<'static, bool>>::get_simple_static_type(),
        A::get_simple_static_type()
    );

    #[derive(SimpleStaticType)]
    #[allow(dead_code)]
    struct C<T>(T, Option<String>);
    assert_eq!(
        <C<bool>>::get_simple_static_type(),
        <(bool, Option<String>)>::get_simple_static_type()
    );

    #[derive(SimpleStaticType)]
    #[allow(dead_code)]
    struct D();
    assert_eq!(
        <C<D>>::get_simple_static_type(),
        mktype(dhall_proc_macros::subexpr!({ _1: {}, _2: Optional Text }))
    );

    #[derive(SimpleStaticType)]
    #[allow(dead_code)]
    enum E<T> {
        A(T),
        B(String),
    };
    assert_eq!(
        <E<bool>>::get_simple_static_type(),
        mktype(dhall_proc_macros::subexpr!(< A: Bool | B: Text >))
    );
}
