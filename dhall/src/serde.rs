use crate::error::{Error, Result};
use crate::expr::{Normalized, Type};
use crate::traits::Deserialize;
use dhall_core::*;
use std::borrow::Cow;

impl<'a, T: serde::Deserialize<'a>> Deserialize<'a> for T {
    fn from_str(s: &'a str, ty: Option<&Type>) -> Result<Self> {
        let expr = Normalized::from_str(s, ty)?;
        T::deserialize(Deserializer(Cow::Owned(expr.0)))
    }
}

struct Deserializer<'a>(Cow<'a, SubExpr<X, X>>);

impl serde::de::Error for Error {
    fn custom<T>(msg: T) -> Self
    where
        T: std::fmt::Display,
    {
        Error::Deserialize(msg.to_string())
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
        use ExprF::*;
        match self.0.as_ref().as_ref() {
            NaturalLit(n) => match (*n).try_into() {
                Ok(n64) => visitor.visit_u64(n64),
                Err(_) => match (*n).try_into() {
                    Ok(n32) => visitor.visit_u32(n32),
                    Err(_) => unimplemented!(),
                },
            },
            IntegerLit(n) => match (*n).try_into() {
                Ok(n64) => visitor.visit_i64(n64),
                Err(_) => match (*n).try_into() {
                    Ok(n32) => visitor.visit_i32(n32),
                    Err(_) => unimplemented!(),
                },
            },
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
