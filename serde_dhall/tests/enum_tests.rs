mod test_enum {
    use serde::{Deserialize, Serialize};
    use serde_dhall::{SimpleType, StaticType};

    #[derive(
        Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize, StaticType,
    )]
    pub struct ParentStruct {
        pub id0: i32,
        pub id1: i32,
    }

    #[derive(Clone, Serialize, Deserialize, Debug, PartialEq, StaticType)]
    pub enum EnumVariants {
        SimpleStruct {
            x: f64,
            y: f64,
            z: f64,
        },
        InheritStruct {
            field_a: ParentStruct,
            field_b: ParentStruct,
        },

        Unitary,
    }

    fn build_type() -> SimpleType {
        let ty: SimpleType = serde_dhall::from_str(
            r#"
let ParentStruct = {id0: Integer, id1: Integer }

let EnumVariant =
        < SimpleStruct : { x : Double, y : Double, z : Double }
        | InheritStruct: { field_a: ParentStruct, field_b: ParentStruct }
        | Unitary
        >       
in EnumVariant"#,
        )
        .parse()
        .unwrap();
        ty
    }

    #[test]
    fn test_enum_simple_struct() {
        let v = EnumVariants::SimpleStruct {
            x: 1.0,
            y: 2.0,
            z: 3.0,
        };
        let v_str = serde_dhall::serialize(&v)
            .type_annotation(&build_type())
            .to_string()
            .unwrap();
        println!("{v_str:?}");
        let v_deser: EnumVariants =
            serde_dhall::from_str(&v_str).parse().unwrap();
        assert_eq!(v_deser, v);
    }

    #[test]
    fn test_enum_inherit_struct() {
        let v = EnumVariants::InheritStruct {
            field_a: ParentStruct { id0: 399, id1: 0 },
            field_b: ParentStruct { id0: 301, id1: 0 },
        };

        let v_str = serde_dhall::serialize(&v)
            .type_annotation(&build_type())
            .to_string()
            .unwrap();
        println!("{v_str:?}");
        let v_deser: EnumVariants =
            serde_dhall::from_str(&v_str).parse().unwrap();
        assert_eq!(v_deser, v);
    }

    #[test]
    fn test_enum_unitary() {
        let v = EnumVariants::Unitary;

        let v_str = serde_dhall::serialize(&v)
            .type_annotation(&build_type())
            .to_string()
            .unwrap();
        println!("{v_str:?}");
        let v_deser: EnumVariants =
            serde_dhall::from_str(&v_str).parse().unwrap();
        assert_eq!(v_deser, v);
    }
}
