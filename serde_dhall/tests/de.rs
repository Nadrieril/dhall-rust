use serde::Deserialize;
use serde_dhall::{from_str, FromDhall, StaticType};

#[test]
fn test_de_typed() {
    fn parse<T: FromDhall + StaticType>(s: &str) -> T {
        from_str(s).static_type_annotation().parse().unwrap()
    }

    assert_eq!(parse::<bool>("True"), true);

    assert_eq!(parse::<u64>("1"), 1);
    assert_eq!(parse::<u32>("1"), 1);
    assert_eq!(parse::<usize>("1"), 1);

    assert_eq!(parse::<i64>("+1"), 1);
    assert_eq!(parse::<i32>("+1"), 1);
    assert_eq!(parse::<isize>("+1"), 1);

    assert_eq!(parse::<f64>("1.0"), 1.0);
    assert_eq!(parse::<f32>("1.0"), 1.0);

    assert_eq!(parse::<String>(r#""foo""#), "foo".to_owned());
    assert_eq!(parse::<Vec<u64>>("[] : List Natural"), vec![]);
    assert_eq!(parse::<Vec<u64>>("[1, 2]"), vec![1, 2]);
    assert_eq!(parse::<Option<u64>>("None Natural"), None);
    assert_eq!(parse::<Option<u64>>("Some 1"), Some(1));

    assert_eq!(
        parse::<(u64, String)>(r#"{ _1 = 1, _2 = "foo" }"#),
        (1, "foo".to_owned())
    );

    #[derive(Debug, PartialEq, Eq, Deserialize, StaticType)]
    struct Foo {
        x: u64,
        y: i64,
    }
    assert_eq!(parse::<Foo>("{ x = 1, y = -2 }"), Foo { x: 1, y: -2 });

    #[derive(Debug, PartialEq, Eq, Deserialize, StaticType)]
    enum Bar {
        X(u64),
        Y(i64),
    }
    assert_eq!(parse::<Bar>("< X: Natural | Y: Integer >.X 1"), Bar::X(1));

    #[derive(Debug, PartialEq, Eq, Deserialize, StaticType)]
    enum Baz {
        X,
        Y(i64),
    }
    assert_eq!(parse::<Baz>("< X | Y: Integer >.X"), Baz::X);

    assert!(from_str("< X | Y: Integer >.Y")
        .static_type_annotation()
        .parse::<Baz>()
        .is_err());
}

#[test]
fn test_de_untyped() {
    use std::collections::BTreeMap;
    use std::collections::HashMap;

    fn parse<T: FromDhall>(s: &str) -> T {
        from_str(s).parse().unwrap()
    }

    // Test tuples on record of wrong type
    assert_eq!(
        parse::<(u64, String, isize)>(r#"{ y = "foo", x = 1, z = +42 }"#),
        (1, "foo".to_owned(), 42)
    );

    let mut expected_map = HashMap::new();
    expected_map.insert("x".to_string(), 1);
    expected_map.insert("y".to_string(), 2);
    assert_eq!(
        parse::<HashMap<String, usize>>("{ x = 1, y = 2 }"),
        expected_map
    );

    let mut expected_map = HashMap::new();
    expected_map.insert("if".to_string(), 1);
    expected_map.insert("FOO_BAR".to_string(), 2);
    expected_map.insert("baz-kux".to_string(), 3);
    assert_eq!(
        parse::<HashMap<String, usize>>(
            "{ `if` = 1, FOO_BAR = 2, baz-kux = 3 }"
        ),
        expected_map
    );

    let mut expected_map = BTreeMap::new();
    expected_map.insert("x".to_string(), 1);
    expected_map.insert("y".to_string(), 2);
    assert_eq!(
        parse::<BTreeMap<String, usize>>("{ x = 1, y = 2 }"),
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

// TODO: test various builder configurations
// In particular test cloning and reusing builder
