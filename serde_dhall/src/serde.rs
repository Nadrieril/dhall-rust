use std::borrow::Cow;

use serde::de::value::{
    MapAccessDeserializer, MapDeserializer, SeqDeserializer,
};

use dhall::semantics::phase::NormalizedExpr;
use dhall::syntax::ExprKind;

use crate::de::{Deserialize, Error, Result};
use crate::Value;

impl<'a, T> crate::de::sealed::Sealed for T where T: serde::Deserialize<'a> {}

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
        use ExprKind::*;
        let expr = self.0.as_ref();
        let not_serde_compatible = || {
            Err(Error::Deserialize(format!(
                "this cannot be deserialized into the serde data model: {}",
                expr
            )))
        };

        match expr.as_ref() {
            BoolLit(x) => visitor.visit_bool(*x),
            NaturalLit(x) => {
                if let Ok(x64) = (*x).try_into() {
                    visitor.visit_u64(x64)
                } else if let Ok(x32) = (*x).try_into() {
                    visitor.visit_u32(x32)
                } else {
                    unimplemented!()
                }
            }
            IntegerLit(x) => {
                if let Ok(x64) = (*x).try_into() {
                    visitor.visit_i64(x64)
                } else if let Ok(x32) = (*x).try_into() {
                    visitor.visit_i32(x32)
                } else {
                    unimplemented!()
                }
            }
            DoubleLit(x) => visitor.visit_f64((*x).into()),
            TextLit(x) => {
                // Normal form ensures that the tail is empty.
                assert!(x.tail().is_empty());
                visitor.visit_str(x.head())
            }
            EmptyListLit(..) => {
                visitor.visit_seq(SeqDeserializer::new(None::<()>.into_iter()))
            }
            NEListLit(xs) => visitor.visit_seq(SeqDeserializer::new(
                xs.iter().map(|x| Deserializer(Cow::Borrowed(x))),
            )),
            SomeLit(x) => visitor.visit_some(Deserializer(Cow::Borrowed(x))),
            App(f, x) => match f.as_ref() {
                Builtin(dhall::syntax::Builtin::OptionalNone) => {
                    visitor.visit_none()
                }
                Field(y, name) => match y.as_ref() {
                    UnionType(..) => {
                        let name: String = name.into();
                        visitor.visit_enum(MapAccessDeserializer::new(
                            MapDeserializer::new(
                                Some((name, Deserializer(Cow::Borrowed(x))))
                                    .into_iter(),
                            ),
                        ))
                    }
                    _ => not_serde_compatible(),
                },
                _ => not_serde_compatible(),
            },
            RecordLit(m) => visitor
                .visit_map(MapDeserializer::new(m.iter().map(|(k, v)| {
                    (k.as_ref(), Deserializer(Cow::Borrowed(v)))
                }))),
            Field(y, name) => match y.as_ref() {
                UnionType(..) => {
                    let name: String = name.into();
                    visitor.visit_enum(MapAccessDeserializer::new(
                        MapDeserializer::new(Some((name, ())).into_iter()),
                    ))
                }
                _ => not_serde_compatible(),
            },
            Const(..) | Var(..) | Lam(..) | Pi(..) | Let(..) | Annot(..)
            | Assert(..) | Builtin(..) | BinOp(..) | BoolIf(..)
            | RecordType(..) | UnionType(..) | Merge(..) | ToMap(..)
            | Projection(..) | ProjectionByExpr(..) | Completion(..)
            | Import(..) | Embed(..) => not_serde_compatible(),
        }
    }

    fn deserialize_tuple<V>(self, _: usize, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        use ExprKind::*;
        let expr = self.0.as_ref();

        match expr.as_ref() {
            // Blindly takes keys in sorted order.
            RecordLit(m) => visitor.visit_seq(SeqDeserializer::new(
                m.iter().map(|(_, v)| Deserializer(Cow::Borrowed(v))),
            )),
            _ => self.deserialize_any(visitor),
        }
    }

    serde::forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string
        bytes byte_buf option unit unit_struct newtype_struct seq
        tuple_struct map struct enum identifier ignored_any
    }
}
