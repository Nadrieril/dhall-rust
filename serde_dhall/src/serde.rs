use std::borrow::Cow;

use dhall::phase::NormalizedExpr;
use dhall::syntax::ExprF;

use crate::de::{Deserialize, Error, Result};
use crate::Value;

impl<'a, T> Deserialize for T
where
    T: serde::Deserialize<'a>,
{
    fn from_dhall(v: &Value) -> Result<Self> {
        T::deserialize(Deserializer(Cow::Owned(v.to_expr())))
    }
}

struct Deserializer<'a>(Cow<'a, NormalizedExpr>);

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
        use ExprF::*;
        match self.0.as_ref().as_ref() {
            NaturalLit(n) => {
                if let Ok(n64) = (*n).try_into() {
                    visitor.visit_u64(n64)
                } else if let Ok(n32) = (*n).try_into() {
                    visitor.visit_u32(n32)
                } else {
                    unimplemented!()
                }
            }
            IntegerLit(n) => {
                if let Ok(n64) = (*n).try_into() {
                    visitor.visit_i64(n64)
                } else if let Ok(n32) = (*n).try_into() {
                    visitor.visit_i32(n32)
                } else {
                    unimplemented!()
                }
            }
            RecordLit(m) => visitor.visit_map(
                serde::de::value::MapDeserializer::new(m.iter().map(
                    |(k, v)| (k.as_ref(), Deserializer(Cow::Borrowed(v))),
                )),
            ),
            _ => unimplemented!(),
        }
    }

    serde::forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string
        bytes byte_buf option unit unit_struct newtype_struct seq tuple
        tuple_struct map struct enum identifier ignored_any
    }
}
