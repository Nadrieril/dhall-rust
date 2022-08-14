mod simple_type {
    use std::collections::HashMap;

    use serde_dhall::{serialize, SimpleType, StaticType, ToDhall};

    fn assert_ser<T>(s: &str, x: T)
    where
        T: ToDhall + std::fmt::Debug,
    {
        assert_eq!(
            serialize(&x).to_string().map_err(|e| e.to_string()),
            Ok(s.to_string())
        );
    }

    #[test]
    fn test_serialize() {
        let mut m = HashMap::new();
        m.insert("Foo".to_string(), u64::static_type());
        m.insert("Bar".to_string(), u64::static_type());
        let t = SimpleType::Record(m);

        assert_ser("{ Bar : Natural, Foo : Natural }", t);
    }
}
