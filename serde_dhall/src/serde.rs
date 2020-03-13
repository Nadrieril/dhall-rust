use std::borrow::Cow;

use serde::de::value::{
    MapAccessDeserializer, MapDeserializer, SeqDeserializer,
};

use dhall::syntax::NumKind;
use dhall::{SValKind, SimpleValue};

use crate::{Deserialize, Error, Result};

impl<'a, T> crate::sealed::Sealed for T where T: serde::Deserialize<'a> {}

struct Deserializer<'a>(Cow<'a, SimpleValue>);

impl<'a, T> Deserialize for T
where
    T: serde::Deserialize<'a>,
{
    fn from_dhall(v: &dhall::Value) -> Result<Self> {
        let sval = v.to_simple_value().ok_or_else(|| {
            Error::Deserialize(format!(
                "this cannot be deserialized into the serde data model: {}",
                v
            ))
        })?;
        T::deserialize(Deserializer(Cow::Owned(sval)))
    }
}

impl<'de: 'a, 'a> serde::de::IntoDeserializer<'de, Error> for Deserializer<'a> {
    type Deserializer = Deserializer<'a>;
    fn into_deserializer(self) -> Self::Deserializer {
        self
    }
}

impl<'de: 'a, 'a> serde::Deserializer<'de> for Deserializer<'a> {
    type Error = Error;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        use std::convert::TryInto;
        use NumKind::*;
        use SValKind::*;

        let val = |x| Deserializer(Cow::Borrowed(x));
        match self.0.kind() {
            Num(Bool(x)) => visitor.visit_bool(*x),
            Num(Natural(x)) => {
                if let Ok(x64) = (*x).try_into() {
                    visitor.visit_u64(x64)
                } else if let Ok(x32) = (*x).try_into() {
                    visitor.visit_u32(x32)
                } else {
                    unimplemented!()
                }
            }
            Num(Integer(x)) => {
                if let Ok(x64) = (*x).try_into() {
                    visitor.visit_i64(x64)
                } else if let Ok(x32) = (*x).try_into() {
                    visitor.visit_i32(x32)
                } else {
                    unimplemented!()
                }
            }
            Num(Double(x)) => visitor.visit_f64((*x).into()),
            Text(x) => visitor.visit_str(x),
            List(xs) => {
                visitor.visit_seq(SeqDeserializer::new(xs.iter().map(val)))
            }
            Optional(None) => visitor.visit_none(),
            Optional(Some(x)) => visitor.visit_some(val(x)),
            Record(m) => visitor.visit_map(MapDeserializer::new(
                m.iter().map(|(k, v)| (k.as_ref(), val(v))),
            )),
            Union(field_name, Some(x)) => visitor.visit_enum(
                MapAccessDeserializer::new(MapDeserializer::new(
                    Some((field_name.as_str(), val(x))).into_iter(),
                )),
            ),
            Union(field_name, None) => visitor.visit_enum(
                MapAccessDeserializer::new(MapDeserializer::new(
                    Some((field_name.as_str(), ())).into_iter(),
                )),
            ),
        }
    }

    fn deserialize_tuple<V>(self, _: usize, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let val = |x| Deserializer(Cow::Borrowed(x));
        match self.0.kind() {
            // Blindly takes keys in sorted order.
            SValKind::Record(m) => visitor
                .visit_seq(SeqDeserializer::new(m.iter().map(|(_, v)| val(v)))),
            _ => self.deserialize_any(visitor),
        }
    }

    serde::forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string
        bytes byte_buf option unit unit_struct newtype_struct seq
        tuple_struct map struct enum identifier ignored_any
    }
}
