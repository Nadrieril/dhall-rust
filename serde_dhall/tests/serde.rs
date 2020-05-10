mod serde {
    use serde::{Deserialize, Serialize};
    use serde_dhall::{from_str, serialize, FromDhall, StaticType, ToDhall};

    fn assert_de<T>(s: &str, x: T)
    where
        T: FromDhall + StaticType + PartialEq + std::fmt::Debug,
    {
        assert_eq!(
            from_str(s)
                .static_type_annotation()
                .parse::<T>()
                .map_err(|e| e.to_string()),
            Ok(x)
        );
    }
    fn assert_ser<T>(s: &str, x: T)
    where
        T: ToDhall + StaticType + PartialEq + std::fmt::Debug,
    {
        assert_eq!(
            serialize(&x)
                .static_type_annotation()
                .to_string()
                .map_err(|e| e.to_string()),
            Ok(s.to_string())
        );
    }
    fn assert_serde<T>(s: &str, x: T)
    where
        T: ToDhall
            + FromDhall
            + StaticType
            + PartialEq
            + std::fmt::Debug
            + Clone,
    {
        assert_de(s, x.clone());
        assert_ser(s, x);
    }

    #[test]
    fn numbers() {
        assert_serde("True", true);

        assert_serde("1", 1u64);
        assert_serde("1", 1u32);
        assert_serde("1", 1usize);

        assert_serde("+1", 1i64);
        assert_serde("+1", 1i32);
        assert_serde("+1", 1isize);

        assert_serde("1.0", 1.0f64);
        assert_serde("1.0", 1.0f32);
    }

    #[test]
    fn text() {
        assert_serde(r#""foo""#, "foo".to_owned());
        assert_ser(r#""foo""#, "foo");
    }

    #[test]
    fn list() {
        assert_serde("[] : List Natural", <Vec<u64>>::new());
        assert_serde("[] : List Text", <Vec<String>>::new());
        assert_serde(
            r#"["foo", "bar"]"#,
            vec!["foo".to_owned(), "bar".to_owned()],
        );
        assert_ser(r#"["foo", "bar"]"#, vec!["foo", "bar"]);
        assert_serde::<Vec<u64>>("[1, 2]", vec![1, 2]);
    }

    #[test]
    fn optional() {
        assert_serde::<Option<u64>>("None Natural", None);
        assert_serde::<Option<String>>("None Text", None);
        assert_serde("Some 1", Some(1u64));
    }

    #[test]
    fn tuple() {
        assert_serde::<()>(r#"{=}"#, ());
        assert_serde::<(u64, String)>(
            r#"{ _1 = 1, _2 = "foo" }"#,
            (1, "foo".to_owned()),
        );
        assert_serde::<(u64, u64, u64, u64)>(
            r#"{ _1 = 1, _2 = 2, _3 = 3, _4 = 4 }"#,
            (1, 2, 3, 4),
        );
    }

    #[test]
    fn structs() {
        // #[derive(
        //     Debug, Clone, PartialEq, Eq, Deserialize, Serialize, StaticType,
        // )]
        // struct Foo;
        // assert_serde::<Foo>("{=}", Foo);

        // #[derive(
        //     Debug, Clone, PartialEq, Eq, Deserialize, Serialize, StaticType,
        // )]
        // struct Bar(u64);
        // assert_serde::<Bar>("{ _1 = 1 }", Bar (1));

        #[derive(
            Debug, Clone, PartialEq, Eq, Deserialize, Serialize, StaticType,
        )]
        struct Baz {
            x: u64,
            y: i64,
        }
        assert_serde::<Baz>("{ x = 1, y = -2 }", Baz { x: 1, y: -2 });
    }

    #[test]
    fn enums() {
        #[derive(
            Debug, Clone, PartialEq, Eq, Deserialize, Serialize, StaticType,
        )]
        enum Foo {
            X(u64),
            Y(i64),
        }
        assert_serde::<Foo>("< X: Natural | Y: Integer >.X 1", Foo::X(1));

        #[derive(
            Debug, Clone, PartialEq, Eq, Deserialize, Serialize, StaticType,
        )]
        enum Bar {
            X,
            Y(i64),
        }
        assert_serde::<Bar>("< X | Y: Integer >.X", Bar::X);

        assert!(from_str("< X | Y: Integer >.Y")
            .static_type_annotation()
            .parse::<Bar>()
            .is_err());
    }
}
