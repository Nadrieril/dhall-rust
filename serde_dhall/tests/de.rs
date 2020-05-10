use serde::Deserialize;
use serde_dhall::{from_str, FromDhall, NumKind, SimpleValue};

#[test]
fn test_de_untyped() {
    use std::collections::BTreeMap;
    use std::collections::HashMap;

    fn parse<T: FromDhall>(s: &str) -> T {
        from_str(s).parse().unwrap()
    }

    // Test tuples on record of wrong type
    assert_eq!(
        parse::<(u64, String, i64)>(r#"{ y = "foo", x = 1, z = +42 }"#),
        (1, "foo".to_owned(), 42)
    );

    let mut expected_map = HashMap::new();
    expected_map.insert("x".to_string(), 1);
    expected_map.insert("y".to_string(), 2);
    assert_eq!(
        parse::<HashMap<String, u64>>("{ x = 1, y = 2 }"),
        expected_map
    );
    assert_eq!(
        parse::<HashMap<String, u64>>("toMap { x = 1, y = 2 }"),
        expected_map
    );

    let mut expected_map = HashMap::new();
    expected_map.insert("if".to_string(), 1);
    expected_map.insert("FOO_BAR".to_string(), 2);
    expected_map.insert("baz-kux".to_string(), 3);
    assert_eq!(
        parse::<HashMap<String, u64>>("{ `if` = 1, FOO_BAR = 2, baz-kux = 3 }"),
        expected_map
    );

    let mut expected_map = BTreeMap::new();
    expected_map.insert("x".to_string(), 1);
    expected_map.insert("y".to_string(), 2);
    assert_eq!(
        parse::<BTreeMap<String, u64>>("{ x = 1, y = 2 }"),
        expected_map
    );

    #[derive(Debug, PartialEq, Eq, Deserialize)]
    struct Foo {
        x: u64,
        y: Option<u64>,
    }
    // Omit optional field
    assert_eq!(parse::<Foo>("{ x = 1 }"), Foo { x: 1, y: None });

    // https://github.com/Nadrieril/dhall-rust/issues/155
    assert!(from_str("List/length [True, 42]").parse::<bool>().is_err());
}

#[test]
fn test_de_simplevalue() {
    let bool_true = SimpleValue::Num(NumKind::Bool(true));
    // https://github.com/Nadrieril/dhall-rust/issues/184
    assert_eq!(
        from_str("[ True ]").parse::<Vec<SimpleValue>>().unwrap(),
        vec![bool_true.clone()]
    );

    assert_eq!(
        from_str("< Foo >.Foo").parse::<SimpleValue>().unwrap(),
        SimpleValue::Union("Foo".into(), None)
    );
    assert_eq!(
        from_str("< Foo: Bool >.Foo True")
            .parse::<SimpleValue>()
            .unwrap(),
        SimpleValue::Union("Foo".into(), Some(Box::new(bool_true.clone())))
    );

    #[derive(Debug, PartialEq, Eq, Deserialize)]
    struct Foo {
        foo: SimpleValue,
    }
    assert_eq!(
        from_str("{ foo = True }").parse::<Foo>().unwrap(),
        Foo {
            foo: bool_true.clone()
        },
    );
}

// TODO: test various builder configurations
// In particular test cloning and reusing builder
