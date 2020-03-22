use serde::Deserialize;
use serde_dhall::{from_str, from_str_static_type, StaticType};

#[test]
fn test_de_typed() {
    fn parse<T: serde_dhall::Deserialize + StaticType>(s: &str) -> T {
        from_str_static_type(s).unwrap()
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

    assert!(from_str_static_type::<Baz>("< X | Y: Integer >.Y").is_err());
}

#[test]
fn test_de_untyped() {
    fn parse<T: serde_dhall::Deserialize>(s: &str) -> T {
        from_str(s).unwrap()
    }

    // Test tuples on record of wrong type
    assert_eq!(
        parse::<(u64, String, isize)>(r#"{ y = "foo", x = 1, z = +42 }"#),
        (1, "foo".to_owned(), 42)
    );

    use std::collections::HashMap;
    let mut expected_map = HashMap::new();
    expected_map.insert("x".to_string(), 1);
    expected_map.insert("y".to_string(), 2);
    assert_eq!(
        parse::<HashMap<String, usize>>("{ x = 1, y = 2 }"),
        expected_map
    );

    use std::collections::BTreeMap;
    let mut expected_map = BTreeMap::new();
    expected_map.insert("x".to_string(), 1);
    expected_map.insert("y".to_string(), 2);
    assert_eq!(
        parse::<BTreeMap<String, usize>>("{ x = 1, y = 2 }"),
        expected_map
    );

    // https://github.com/Nadrieril/dhall-rust/issues/155
    assert!(from_str::<bool>("List/length [True, 42]").is_err());
}
