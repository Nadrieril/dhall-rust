mod simple_value {
    use serde::{Deserialize, Serialize};
    use serde_dhall::{
        from_str, serialize, FromDhall, NumKind, SimpleValue, ToDhall, Value,
    };

    fn assert_de<T>(s: &str, x: T)
    where
        T: FromDhall + PartialEq + std::fmt::Debug,
    {
        assert_eq!(from_str(s).parse::<T>().map_err(|e| e.to_string()), Ok(x));
    }
    fn assert_ser<T>(s: &str, x: T)
    where
        T: ToDhall + PartialEq + std::fmt::Debug,
    {
        assert_eq!(
            serialize(&x).to_string().map_err(|e| e.to_string()),
            Ok(s.to_string())
        );
    }
    fn assert_serde<T>(s: &str, x: T)
    where
        T: ToDhall + FromDhall + PartialEq + std::fmt::Debug + Clone,
    {
        assert_de(s, x.clone());
        assert_ser(s, x);
    }

    #[test]
    fn test_serde() {
        let bool_true = SimpleValue::Num(NumKind::Bool(true));
        // https://github.com/Nadrieril/dhall-rust/issues/184
        assert_serde("[True]", vec![bool_true.clone()]);

        assert_de("< Foo >.Foo", SimpleValue::Union("Foo".into(), None));
        assert_de(
            "< Foo: Bool >.Foo True",
            SimpleValue::Union("Foo".into(), Some(Box::new(bool_true.clone()))),
        );

        assert_eq!(
            serialize(&SimpleValue::Union("Foo".into(), None)).to_string().map_err(|e| e.to_string()),
            Err("cannot serialize value without a type annotation: Union(\"Foo\", None)".to_string())
        );

        #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
        struct Foo {
            foo: SimpleValue,
        }
        assert_serde(
            "{ foo = True }",
            Foo {
                foo: bool_true.clone(),
            },
        );

        // Neither a simple value or a simple type.
        let not_simple = "Type → Type";
        assert_eq!(
            from_str(not_simple)
                .parse::<Value>()
                .map_err(|e| e.to_string()),
            Err(format!(
                "this is neither a simple type nor a simple value: {}",
                not_simple
            ))
        );
    }
}
