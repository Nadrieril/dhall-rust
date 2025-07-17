use serde::ser;
use std::collections::BTreeMap;

use dhall::syntax::NumKind;

use crate::value::SimpleValue;
use crate::{Error, ErrorKind, Result, SimpleType, Value};
use SimpleValue::*;

pub trait Sealed {}

/// A data structure that can be serialized from a Dhall expression.
///
/// This is automatically implemented for any type that [serde] can serialize.
/// In fact, this trait cannot be implemented manually. To implement it for your type,
/// use serde's derive mechanism.
///
/// # Example
///
/// ```rust
/// # fn main() -> serde_dhall::Result<()> {
/// use serde::Serialize;
///
/// // Use serde's derive
/// #[derive(Serialize)]
/// struct Point {
///     x: u64,
///     y: u64,
/// }
///
/// // Convert a Point to a Dhall string.
/// let point = Point { x: 0, y: 0 };
/// let point_str = serde_dhall::serialize(&point).to_string()?;
/// assert_eq!(point_str, "{ x = 0, y = 0 }".to_string());
/// # Ok(())
/// # }
/// ```
///
/// [serde]: https://serde.rs
pub trait ToDhall: Sealed {
    #[doc(hidden)]
    fn to_dhall(&self, ty: Option<&SimpleType>) -> Result<Value>;
}

impl<T> Sealed for T where T: ser::Serialize {}

impl<T> ToDhall for T
where
    T: ser::Serialize,
{
    fn to_dhall(&self, ty: Option<&SimpleType>) -> Result<Value> {
        let sval: SimpleValue = self.serialize(Serializer)?;
        sval.into_value(ty)
    }
}

#[derive(Default, Clone, Copy)]
struct Serializer;

impl ser::Serializer for Serializer {
    type Ok = SimpleValue;
    type Error = Error;

    type SerializeSeq = SeqSerializer;
    type SerializeTuple = TupleSerializer;
    type SerializeTupleStruct = ser::Impossible<Self::Ok, Self::Error>;
    type SerializeTupleVariant = ser::Impossible<Self::Ok, Self::Error>;
    type SerializeMap = MapSerializer;
    type SerializeStruct = StructSerializer;
    type SerializeStructVariant = StructVariantSerializer;

    fn serialize_bool(self, v: bool) -> Result<Self::Ok> {
        Ok(Num(NumKind::Bool(v)))
    }

    fn serialize_i8(self, v: i8) -> Result<Self::Ok> {
        self.serialize_i64(i64::from(v))
    }
    fn serialize_i16(self, v: i16) -> Result<Self::Ok> {
        self.serialize_i64(i64::from(v))
    }
    fn serialize_i32(self, v: i32) -> Result<Self::Ok> {
        self.serialize_i64(i64::from(v))
    }
    fn serialize_i64(self, v: i64) -> Result<Self::Ok> {
        Ok(Num(NumKind::Integer(v)))
    }

    fn serialize_u8(self, v: u8) -> Result<Self::Ok> {
        self.serialize_u64(u64::from(v))
    }
    fn serialize_u16(self, v: u16) -> Result<Self::Ok> {
        self.serialize_u64(u64::from(v))
    }
    fn serialize_u32(self, v: u32) -> Result<Self::Ok> {
        self.serialize_u64(u64::from(v))
    }
    fn serialize_u64(self, v: u64) -> Result<Self::Ok> {
        Ok(Num(NumKind::Natural(v)))
    }

    fn serialize_f32(self, v: f32) -> Result<Self::Ok> {
        self.serialize_f64(f64::from(v))
    }
    fn serialize_f64(self, v: f64) -> Result<Self::Ok> {
        Ok(Num(NumKind::Double(v.into())))
    }

    fn serialize_char(self, v: char) -> Result<Self::Ok> {
        self.serialize_str(&v.to_string())
    }
    fn serialize_str(self, v: &str) -> Result<Self::Ok> {
        Ok(Text(v.to_owned()))
    }

    fn serialize_bytes(self, _v: &[u8]) -> Result<Self::Ok> {
        Err(ErrorKind::Serialize(
            "Unsupported data for serialization: byte array".to_owned(),
        )
        .into())
    }

    fn serialize_none(self) -> Result<Self::Ok> {
        Ok(Optional(None))
    }
    fn serialize_some<T>(self, v: &T) -> Result<Self::Ok>
    where
        T: ?Sized + ser::Serialize,
    {
        Ok(Optional(Some(Box::new(v.serialize(self)?))))
    }

    fn serialize_unit(self) -> Result<Self::Ok> {
        Ok(Record(Default::default()))
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok> {
        self.serialize_unit()
    }
    fn serialize_newtype_struct<T>(
        self,
        _name: &'static str,
        _value: &T,
    ) -> Result<Self::Ok>
    where
        T: ?Sized + ser::Serialize,
    {
        Err(ErrorKind::Serialize(
            "Unsupported data for serialization: newtype struct".to_owned(),
        )
        .into())
    }
    fn serialize_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStruct> {
        Ok(StructSerializer::default())
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok> {
        Ok(Union(variant.to_owned(), None))
    }
    fn serialize_newtype_variant<T>(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok>
    where
        T: ?Sized + ser::Serialize,
    {
        let value = value.serialize(self)?;
        Ok(Union(variant.to_owned(), Some(Box::new(value))))
    }
    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant> {
        Err(ErrorKind::Serialize(
            "Unsupported data for serialization: tuple variant".to_owned(),
        )
        .into())
    }
    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant> {
        Ok(StructVariantSerializer {
            variant,
            value: BTreeMap::new(),
        })
    }

    fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple> {
        Ok(TupleSerializer::default())
    }
    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleStruct> {
        Err(ErrorKind::Serialize(
            "Unsupported data for serialization: tuple struct".to_owned(),
        )
        .into())
    }

    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq> {
        Ok(SeqSerializer::default())
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap> {
        Ok(MapSerializer::default())
    }
}

#[derive(Default)]
struct SeqSerializer(Vec<SimpleValue>);

impl ser::SerializeSeq for SeqSerializer {
    type Ok = SimpleValue;
    type Error = Error;

    fn serialize_element<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + ser::Serialize,
    {
        self.0.push(value.serialize(Serializer)?);
        Ok(())
    }

    fn end(self) -> Result<Self::Ok> {
        Ok(List(self.0))
    }
}

#[derive(Default)]
struct TupleSerializer(Vec<SimpleValue>);

impl ser::SerializeTuple for TupleSerializer {
    type Ok = SimpleValue;
    type Error = Error;

    fn serialize_element<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + ser::Serialize,
    {
        self.0.push(value.serialize(Serializer)?);
        Ok(())
    }

    fn end(self) -> Result<Self::Ok> {
        Ok(Record(
            self.0
                .into_iter()
                .enumerate()
                .map(|(i, x)| (format!("_{}", i + 1), x))
                .collect(),
        ))
    }
}

#[derive(Default)]
struct MapSerializer {
    map: BTreeMap<String, SimpleValue>,
    key: Option<String>,
    val: Option<SimpleValue>,
}

impl ser::SerializeMap for MapSerializer {
    type Ok = SimpleValue;
    type Error = Error;

    fn serialize_key<T>(&mut self, key: &T) -> Result<()>
    where
        T: ?Sized + ser::Serialize,
    {
        let key = match key.serialize(Serializer)? {
            Text(key) => key,
            _ => return Err(<Error as ser::Error>::custom("not a string")),
        };
        if let Some(val) = self.val.take() {
            self.map.insert(key, val);
        } else {
            self.key = Some(key);
        }
        Ok(())
    }

    fn serialize_value<T>(&mut self, val: &T) -> Result<()>
    where
        T: ?Sized + ser::Serialize,
    {
        let val: SimpleValue = val.serialize(Serializer)?;
        if let Some(key) = self.key.take() {
            self.map.insert(key, val);
        } else {
            self.val = Some(val);
        }
        Ok(())
    }

    fn end(self) -> Result<Self::Ok> {
        Ok(Record(self.map))
    }
}

#[derive(Default)]
struct StructSerializer(BTreeMap<String, SimpleValue>);

impl ser::SerializeStruct for StructSerializer {
    type Ok = SimpleValue;
    type Error = Error;

    fn serialize_field<T>(&mut self, key: &'static str, val: &T) -> Result<()>
    where
        T: ?Sized + ser::Serialize,
    {
        let val: SimpleValue = val.serialize(Serializer)?;
        self.0.insert(key.into(), val);
        Ok(())
    }

    fn end(self) -> Result<Self::Ok> {
        Ok(Record(self.0))
    }
}

struct StructVariantSerializer {
    variant: &'static str,
    value: BTreeMap<String, SimpleValue>,
}

impl ser::SerializeStructVariant for StructVariantSerializer {
    type Ok = SimpleValue;
    type Error = Error;

    fn serialize_field<T>(&mut self, key: &'static str, val: &T) -> Result<()>
    where
        T: ?Sized + ser::Serialize,
    {
        let val: SimpleValue = val.serialize(Serializer)?;
        self.value.insert(key.into(), val);
        Ok(())
    }

    fn end(self) -> Result<Self::Ok> {
        Ok(SimpleValue::Union(
            self.variant.to_string(),
            Some(Box::new(Record(self.value))),
        ))
    }
}

impl serde::ser::Serialize for SimpleValue {
    fn serialize<S>(
        &self,
        serializer: S,
    ) -> std::result::Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        use serde::ser::{SerializeMap, SerializeSeq};
        use NumKind::*;
        use SimpleValue::*;

        match self {
            Num(Bool(x)) => serializer.serialize_bool(*x),
            Num(Natural(x)) => serializer.serialize_u64(*x),
            Num(Integer(x)) => serializer.serialize_i64(*x),
            Num(Double(x)) => serializer.serialize_f64((*x).into()),
            Text(x) => serializer.serialize_str(x),
            List(xs) => {
                let mut seq = serializer.serialize_seq(Some(xs.len()))?;
                for x in xs {
                    seq.serialize_element(x)?;
                }
                seq.end()
            }
            Optional(None) => serializer.serialize_none(),
            Optional(Some(x)) => serializer.serialize_some(x),
            Record(m) => {
                let mut map = serializer.serialize_map(Some(m.len()))?;
                for (k, v) in m {
                    map.serialize_entry(k, v)?;
                }
                map.end()
            }
            // serde's enum support is yet again really limited. We can't avoid a memleak here :(.
            Union(field_name, None) => {
                let field_name: Box<str> = field_name.clone().into();
                serializer.serialize_unit_variant(
                    "SimpleValue",
                    0,
                    Box::leak(field_name),
                )
            }
            Union(field_name, Some(x)) => {
                let field_name: Box<str> = field_name.clone().into();
                serializer.serialize_newtype_variant(
                    "SimpleValue",
                    0,
                    Box::leak(field_name),
                    x,
                )
            }
        }
    }
}
