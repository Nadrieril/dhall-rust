use std::borrow::Cow;
use std::collections::BTreeMap;
use std::convert::TryInto as _;
use std::fmt;

use serde::de::value::{
    MapAccessDeserializer, MapDeserializer, SeqDeserializer,
};
use serde::de::VariantAccess as _;

use dhall::syntax::NumKind;

use crate::value::SimpleValue;
use crate::{Error, ErrorKind, Value};

pub trait Sealed {}

/// A data structure that can be deserialized from a Dhall expression.
///
/// This is automatically implemented for any type that [serde] can deserialize.
/// In fact, this trait cannot be implemented manually. To implement it for your type,
/// use serde's derive mechanism.
///
/// # Example
///
/// ```rust
/// # fn main() -> serde_dhall::Result<()> {
/// use serde::Deserialize;
///
/// // Use serde's derive
/// #[derive(Deserialize)]
/// struct Point {
///     x: u64,
///     y: u64,
/// }
///
/// // Convert a Dhall string to a Point.
/// let point: Point = serde_dhall::from_str("{ x = 1, y = 1 + 1 }").parse()?;
/// # Ok(())
/// # }
/// ```
///
/// [serde]: https://serde.rs
pub trait FromDhall: Sealed + Sized {
    #[doc(hidden)]
    fn from_dhall(v: &Value) -> crate::Result<Self>;
}

impl<T> Sealed for T where T: serde::de::DeserializeOwned {}

struct Deserializer<'a>(Cow<'a, SimpleValue>);

/// Deserialize a Rust value from a Dhall [`SimpleValue`].
///
/// # Example
///
/// ```rust
/// # fn main() -> serde_dhall::Result<()> {
/// use std::collections::BTreeMap;
/// use serde::Deserialize;
///
/// // We use serde's derive feature
/// #[derive(Deserialize)]
/// struct Point {
///     x: u64,
///     y: u64,
/// }
///
/// // Some Dhall data
/// let mut data = BTreeMap::new();
/// data.insert(
///     "x".to_string(),
///     serde_dhall::SimpleValue::Num(serde_dhall::NumKind::Natural(1))
/// );
/// data.insert(
///     "y".to_string(),
///     serde_dhall::SimpleValue::Num(serde_dhall::NumKind::Natural(2))
/// );
/// let data = serde_dhall::SimpleValue::Record(data);
///
/// // Parse the Dhall value as a Point.
/// let point: Point = serde_dhall::from_simple_value(data)?;
///
/// assert_eq!(point.x, 1);
/// assert_eq!(point.y, 2);
/// # Ok(())
/// # }
/// ```
///
/// [`SimpleValue`]: enum.SimpleValue.html
pub fn from_simple_value<T>(v: SimpleValue) -> crate::Result<T>
where
    T: serde::de::DeserializeOwned,
{
    T::deserialize(Deserializer(Cow::Owned(v)))
}

impl<T> FromDhall for T
where
    T: serde::de::DeserializeOwned,
{
    fn from_dhall(v: &Value) -> crate::Result<Self> {
        let sval = v.to_simple_value().ok_or_else(|| {
            Error(ErrorKind::Deserialize(format!(
                "this cannot be deserialized into the serde data model: {}",
                v
            )))
        })?;
        from_simple_value(sval)
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

    fn deserialize_any<V>(self, visitor: V) -> crate::Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        use std::convert::TryInto;
        use NumKind::*;
        use SimpleValue::*;

        let val = |x| Deserializer(Cow::Borrowed(x));
        match self.0.as_ref() {
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

    fn deserialize_tuple<V>(
        self,
        _: usize,
        visitor: V,
    ) -> crate::Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let val = |x| Deserializer(Cow::Borrowed(x));
        match self.0.as_ref() {
            // Blindly takes keys in sorted order.
            SimpleValue::Record(m) => visitor
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

struct SimpleValueVisitor;

impl<'de> serde::de::Visitor<'de> for SimpleValueVisitor {
    type Value = SimpleValue;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("any valid Dhall value")
    }

    fn visit_bool<E>(self, value: bool) -> Result<SimpleValue, E> {
        Ok(SimpleValue::Num(NumKind::Bool(value)))
    }

    fn visit_i64<E>(self, value: i64) -> Result<SimpleValue, E> {
        // TODO: use `i64` instead of `isize` in `NumKind`.
        Ok(SimpleValue::Num(NumKind::Integer(
            value.try_into().unwrap(),
        )))
    }

    fn visit_u64<E>(self, value: u64) -> Result<SimpleValue, E> {
        // TODO: use `u64` instead of `usize` in `NumKind`.
        Ok(SimpleValue::Num(NumKind::Natural(
            value.try_into().unwrap(),
        )))
    }

    fn visit_f64<E>(self, value: f64) -> Result<SimpleValue, E> {
        Ok(SimpleValue::Num(NumKind::Double(value.into())))
    }

    fn visit_str<E>(self, value: &str) -> Result<SimpleValue, E> {
        Ok(SimpleValue::Text(String::from(value)))
    }

    fn visit_string<E>(self, value: String) -> Result<SimpleValue, E> {
        Ok(SimpleValue::Text(value))
    }

    fn visit_none<E>(self) -> Result<SimpleValue, E> {
        Ok(SimpleValue::Optional(None))
    }

    fn visit_some<D>(self, val: D) -> Result<SimpleValue, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let val = val.deserialize_any(SimpleValueVisitor)?;
        Ok(SimpleValue::Optional(Some(Box::new(val))))
    }

    fn visit_enum<V>(self, visitor: V) -> Result<SimpleValue, V::Error>
    where
        V: serde::de::EnumAccess<'de>,
    {
        let (name, variant): (String, _) = visitor.variant()?;
        // Serde does not allow me to check what kind of variant it is. This will work for dhall
        // values, because there are only two possible kinds of cvariants, but doesn't work in
        // general. Given that the `serde_value` crate ignores enums, I assume this is not fixable
        // :(.
        let val = variant.newtype_variant().ok();
        Ok(SimpleValue::Union(name, val))
    }

    fn visit_seq<V>(self, mut visitor: V) -> Result<SimpleValue, V::Error>
    where
        V: serde::de::SeqAccess<'de>,
    {
        let mut vec = Vec::new();
        while let Some(elem) = visitor.next_element()? {
            vec.push(elem);
        }
        Ok(SimpleValue::List(vec))
    }

    fn visit_map<V>(self, mut visitor: V) -> Result<SimpleValue, V::Error>
    where
        V: serde::de::MapAccess<'de>,
    {
        let mut record = BTreeMap::default();
        while let Some((key, value)) = visitor.next_entry()? {
            record.insert(key, value);
        }
        Ok(SimpleValue::Record(record))
    }
}

impl<'de> serde::de::Deserialize<'de> for SimpleValue {
    fn deserialize<D>(deserializer: D) -> Result<SimpleValue, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(SimpleValueVisitor)
    }
}
