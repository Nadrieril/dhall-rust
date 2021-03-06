use itertools::Itertools;
use serde::de;
use std::collections::BTreeMap;
use std::fmt;
use std::iter::FromIterator;

use crate::error::DecodeError;
use crate::operations::OpKind;
use crate::syntax;
use crate::syntax::{
    Expr, ExprKind, FilePath, FilePrefix, Hash, ImportMode, ImportTarget,
    Integer, InterpolatedText, Label, Natural, NumKind, Scheme, Span,
    UnspannedExpr, URL, V,
};
type DecodedExpr = Expr;

pub fn decode(data: &[u8]) -> Result<DecodedExpr, DecodeError> {
    match serde_cbor::de::from_slice(data) {
        Ok(v) => cbor_value_to_dhall(&v),
        Err(e) => Err(DecodeError::CBORError(e)),
    }
}

/// An enum that can encode most CBOR values.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Null,
    Bool(bool),
    U64(u64),
    I64(i64),
    F64(f64),
    String(String),
    Array(Vec<Value>),
    Object(BTreeMap<String, Value>),
    Bytes(Vec<u8>),
}

// Should probably rename this
fn rc(x: UnspannedExpr) -> Expr {
    Expr::new(x, Span::Decoded)
}

fn cbor_value_to_dhall(data: &Value) -> Result<DecodedExpr, DecodeError> {
    use crate::builtins::Builtin;
    use crate::operations::BinOp;
    use syntax::Const;
    use ExprKind::*;
    use OpKind::*;
    use Value::*;
    Ok(rc(match data {
        String(s) => match Builtin::parse(s) {
            Some(b) => ExprKind::Builtin(b),
            None => match s.as_str() {
                "True" => Num(NumKind::Bool(true)),
                "False" => Num(NumKind::Bool(false)),
                "Type" => Const(Const::Type),
                "Kind" => Const(Const::Kind),
                "Sort" => Const(Const::Sort),
                _ => {
                    return Err(DecodeError::WrongFormatError(
                        "builtin".to_owned(),
                    ))
                }
            },
        },
        U64(n) => Var(V(Label::from("_"), *n as usize)),
        F64(x) => Num(NumKind::Double((*x).into())),
        Bool(b) => Num(NumKind::Bool(*b)),
        Array(vec) => match vec.as_slice() {
            [String(l), U64(n)] => {
                if l.as_str() == "_" {
                    return Err(DecodeError::WrongFormatError(
                        "`_` variable was encoded incorrectly".to_owned(),
                    ));
                }
                let l = Label::from(l.as_str());
                Var(V(l, *n as usize))
            }
            [U64(0), f, args @ ..] => {
                if args.is_empty() {
                    return Err(DecodeError::WrongFormatError(
                        "Function application must have at least one argument"
                            .to_owned(),
                    ));
                }
                let mut f = cbor_value_to_dhall(&f)?;
                for a in args {
                    let a = cbor_value_to_dhall(&a)?;
                    f = rc(Op(App(f, a)))
                }
                return Ok(f);
            }
            [U64(1), x, y] => {
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                Lam(Label::from("_"), x, y)
            }
            [U64(1), String(l), x, y] => {
                if l.as_str() == "_" {
                    return Err(DecodeError::WrongFormatError(
                        "`_` variable was encoded incorrectly".to_owned(),
                    ));
                }
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                let l = Label::from(l.as_str());
                Lam(l, x, y)
            }
            [U64(2), x, y] => {
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                Pi(Label::from("_"), x, y)
            }
            [U64(2), String(l), x, y] => {
                if l.as_str() == "_" {
                    return Err(DecodeError::WrongFormatError(
                        "`_` variable was encoded incorrectly".to_owned(),
                    ));
                }
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                let l = Label::from(l.as_str());
                Pi(l, x, y)
            }
            [U64(3), U64(13), x, y] => {
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                Op(Completion(x, y))
            }
            [U64(3), U64(n), x, y] => {
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                use BinOp::*;
                let op = match n {
                    0 => BoolOr,
                    1 => BoolAnd,
                    2 => BoolEQ,
                    3 => BoolNE,
                    4 => NaturalPlus,
                    5 => NaturalTimes,
                    6 => TextAppend,
                    7 => ListAppend,
                    8 => RecursiveRecordMerge,
                    9 => RightBiasedRecordMerge,
                    10 => RecursiveRecordTypeMerge,
                    11 => ImportAlt,
                    12 => Equivalence,
                    _ => {
                        return Err(DecodeError::WrongFormatError(
                            "binop".to_owned(),
                        ))
                    }
                };
                Op(BinOp(op, x, y))
            }
            [U64(4), t] => {
                let t = cbor_value_to_dhall(&t)?;
                EmptyListLit(rc(Op(App(
                    rc(ExprKind::Builtin(Builtin::List)),
                    t,
                ))))
            }
            [U64(4), Null, rest @ ..] => {
                let rest = rest
                    .iter()
                    .map(cbor_value_to_dhall)
                    .collect::<Result<Vec<_>, _>>()?;
                NEListLit(rest)
            }
            [U64(5), Null, x] => {
                let x = cbor_value_to_dhall(&x)?;
                SomeLit(x)
            }
            // Old-style optional literals
            [U64(5), t] => {
                let t = cbor_value_to_dhall(&t)?;
                Op(App(rc(ExprKind::Builtin(Builtin::OptionalNone)), t))
            }
            [U64(5), t, x] => {
                let x = cbor_value_to_dhall(&x)?;
                let t = cbor_value_to_dhall(&t)?;
                Annot(
                    rc(SomeLit(x)),
                    rc(Op(App(rc(ExprKind::Builtin(Builtin::Optional)), t))),
                )
            }
            [U64(6), x, y] => {
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                Op(Merge(x, y, None))
            }
            [U64(6), x, y, z] => {
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                let z = cbor_value_to_dhall(&z)?;
                Op(Merge(x, y, Some(z)))
            }
            [U64(7), Object(map)] => {
                let map = cbor_map_to_dhall_map(map)?;
                RecordType(map)
            }
            [U64(8), Object(map)] => {
                let map = cbor_map_to_dhall_map(map)?;
                RecordLit(map)
            }
            [U64(9), x, String(l)] => {
                let x = cbor_value_to_dhall(&x)?;
                let l = Label::from(l.as_str());
                Op(Field(x, l))
            }
            [U64(10), x, Array(arr)] => {
                let x = cbor_value_to_dhall(&x)?;
                if let [y] = arr.as_slice() {
                    let y = cbor_value_to_dhall(&y)?;
                    Op(ProjectionByExpr(x, y))
                } else {
                    return Err(DecodeError::WrongFormatError(
                        "projection-by-expr".to_owned(),
                    ));
                }
            }
            [U64(10), x, rest @ ..] => {
                let x = cbor_value_to_dhall(&x)?;
                let labels = rest
                    .iter()
                    .map(|s| match s {
                        String(s) => Ok(Label::from(s.as_str())),
                        _ => Err(DecodeError::WrongFormatError(
                            "projection".to_owned(),
                        )),
                    })
                    .collect::<Result<_, _>>()?;
                Op(Projection(x, labels))
            }
            [U64(11), Object(map)] => {
                let map = cbor_map_to_dhall_opt_map(map)?;
                UnionType(map)
            }
            [U64(12), ..] => {
                return Err(DecodeError::WrongFormatError(
                    "Union literals are not supported anymore".to_owned(),
                ))
            }
            [U64(14), x, y, z] => {
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                let z = cbor_value_to_dhall(&z)?;
                Op(BoolIf(x, y, z))
            }
            [U64(15), U64(x)] => Num(NumKind::Natural(*x as Natural)),
            [U64(16), U64(x)] => Num(NumKind::Integer(*x as Integer)),
            [U64(16), I64(x)] => Num(NumKind::Integer(*x as Integer)),
            [U64(18), String(first), rest @ ..] => {
                TextLit(InterpolatedText::from((
                    first.clone(),
                    rest.iter()
                        .tuples()
                        .map(|(x, y)| {
                            let x = cbor_value_to_dhall(&x)?;
                            let y = match y {
                                String(s) => s.clone(),
                                _ => {
                                    return Err(DecodeError::WrongFormatError(
                                        "text".to_owned(),
                                    ))
                                }
                            };
                            Ok((x, y))
                        })
                        .collect::<Result<_, _>>()?,
                )))
            }
            [U64(19), t] => {
                let t = cbor_value_to_dhall(&t)?;
                Assert(t)
            }
            [U64(24), hash, U64(mode), U64(scheme), rest @ ..] => {
                let mode = match mode {
                    0 => ImportMode::Code,
                    1 => ImportMode::RawText,
                    2 => ImportMode::Location,
                    _ => {
                        return Err(DecodeError::WrongFormatError(format!(
                            "import/mode/unknown_mode: {:?}",
                            mode
                        )))
                    }
                };
                let hash = match hash {
                    Null => None,
                    Bytes(bytes) => match bytes.as_slice() {
                        [18, 32, rest @ ..] => {
                            Some(Hash::SHA256(rest.to_vec().into()))
                        }
                        _ => {
                            return Err(DecodeError::WrongFormatError(format!(
                                "import/hash/unknown_multihash: {:?}",
                                bytes
                            )))
                        }
                    },
                    _ => {
                        return Err(DecodeError::WrongFormatError(
                            "import/hash/should_be_bytes".to_owned(),
                        ))
                    }
                };
                let mut rest = rest.iter();
                let location = match scheme {
                    0 | 1 => {
                        let scheme = match scheme {
                            0 => Scheme::HTTP,
                            _ => Scheme::HTTPS,
                        };
                        let headers = match rest.next() {
                            Some(Null) => None,
                            Some(x) => {
                                let x = cbor_value_to_dhall(&x)?;
                                Some(x)
                            }
                            _ => {
                                return Err(DecodeError::WrongFormatError(
                                    "import/remote/headers".to_owned(),
                                ))
                            }
                        };
                        let authority = match rest.next() {
                            Some(String(s)) => s.to_owned(),
                            _ => {
                                return Err(DecodeError::WrongFormatError(
                                    "import/remote/authority".to_owned(),
                                ))
                            }
                        };
                        let query = match rest.next_back() {
                            Some(Null) => None,
                            Some(String(s)) => Some(s.to_owned()),
                            _ => {
                                return Err(DecodeError::WrongFormatError(
                                    "import/remote/query".to_owned(),
                                ))
                            }
                        };
                        let file_path = rest
                            .map(|s| match s.as_string() {
                                Some(s) => Ok(s.clone()),
                                None => Err(DecodeError::WrongFormatError(
                                    "import/remote/path".to_owned(),
                                )),
                            })
                            .collect::<Result<_, _>>()?;
                        let path = FilePath { file_path };
                        ImportTarget::Remote(URL {
                            scheme,
                            authority,
                            path,
                            query,
                            headers,
                        })
                    }
                    2 | 3 | 4 | 5 => {
                        let prefix = match scheme {
                            2 => FilePrefix::Absolute,
                            3 => FilePrefix::Here,
                            4 => FilePrefix::Parent,
                            5 => FilePrefix::Home,
                            _ => {
                                return Err(DecodeError::WrongFormatError(
                                    "import/local/prefix".to_owned(),
                                ))
                            }
                        };
                        let file_path = rest
                            .map(|s| match s.as_string() {
                                Some(s) => Ok(s.clone()),
                                None => Err(DecodeError::WrongFormatError(
                                    "import/local/path".to_owned(),
                                )),
                            })
                            .collect::<Result<_, _>>()?;
                        let path = FilePath { file_path };
                        ImportTarget::Local(prefix, path)
                    }
                    6 => {
                        let env = match rest.next() {
                            Some(String(s)) => s.to_owned(),
                            _ => {
                                return Err(DecodeError::WrongFormatError(
                                    "import/env".to_owned(),
                                ))
                            }
                        };
                        ImportTarget::Env(env)
                    }
                    7 => ImportTarget::Missing,
                    _ => {
                        return Err(DecodeError::WrongFormatError(
                            "import/type".to_owned(),
                        ))
                    }
                };
                Import(syntax::Import {
                    mode,
                    hash,
                    location,
                })
            }
            [U64(25), bindings @ ..] => {
                let mut tuples = bindings.iter().tuples();
                let bindings = (&mut tuples)
                    .map(|(x, t, v)| {
                        let x = x.as_string().ok_or_else(|| {
                            DecodeError::WrongFormatError(
                                "let/label".to_owned(),
                            )
                        })?;
                        let x = Label::from(x.as_str());
                        let t = match t {
                            Null => None,
                            t => Some(cbor_value_to_dhall(&t)?),
                        };
                        let v = cbor_value_to_dhall(&v)?;
                        Ok((x, t, v))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let expr = tuples.into_buffer().next().ok_or_else(|| {
                    DecodeError::WrongFormatError("let/expr".to_owned())
                })?;
                let expr = cbor_value_to_dhall(expr)?;
                return Ok(bindings
                    .into_iter()
                    .rev()
                    .fold(expr, |acc, (x, t, v)| rc(Let(x, t, v, acc))));
            }
            [U64(26), x, y] => {
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                Annot(x, y)
            }
            [U64(27), x] => {
                let x = cbor_value_to_dhall(&x)?;
                Op(ToMap(x, None))
            }
            [U64(27), x, y] => {
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                Op(ToMap(x, Some(y)))
            }
            [U64(28), x] => {
                let x = cbor_value_to_dhall(&x)?;
                EmptyListLit(x)
            }
            [U64(29), x, labels, y] => {
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                let labels = match labels {
                    Array(labels) => labels
                        .iter()
                        .map(|s| match s {
                            String(s) => Ok(Label::from(s.as_str())),
                            _ => Err(DecodeError::WrongFormatError(
                                "with".to_owned(),
                            )),
                        })
                        .collect::<Result<_, _>>()?,
                    _ => {
                        return Err(DecodeError::WrongFormatError(
                            "with".to_owned(),
                        ))
                    }
                };
                Op(With(x, labels, y))
            }
            _ => {
                return Err(DecodeError::WrongFormatError(format!(
                    "{:?}",
                    data
                )))
            }
        },
        _ => return Err(DecodeError::WrongFormatError(format!("{:?}", data))),
    }))
}

fn cbor_map_to_dhall_map<'a, T>(
    map: impl IntoIterator<Item = (&'a String, &'a Value)>,
) -> Result<T, DecodeError>
where
    T: FromIterator<(Label, DecodedExpr)>,
{
    map.into_iter()
        .map(|(k, v)| -> Result<(_, _), _> {
            let v = cbor_value_to_dhall(v)?;
            Ok((Label::from(k.as_ref()), v))
        })
        .collect::<Result<_, _>>()
}

fn cbor_map_to_dhall_opt_map<'a, T>(
    map: impl IntoIterator<Item = (&'a String, &'a Value)>,
) -> Result<T, DecodeError>
where
    T: FromIterator<(Label, Option<DecodedExpr>)>,
{
    map.into_iter()
        .map(|(k, v)| -> Result<(_, _), _> {
            let v = match v {
                Value::Null => None,
                _ => Some(cbor_value_to_dhall(v)?),
            };
            Ok((Label::from(k.as_ref()), v))
        })
        .collect::<Result<_, _>>()
}

impl Value {
    pub fn as_string(&self) -> Option<&String> {
        if let Value::String(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

impl<'de> de::Deserialize<'de> for Value {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Value, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        struct ValueVisitor;

        impl<'de> de::Visitor<'de> for ValueVisitor {
            type Value = Value;

            fn expecting(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
                fmt.write_str("any valid CBOR value")
            }

            #[inline]
            fn visit_str<E>(self, value: &str) -> Result<Value, E>
            where
                E: de::Error,
            {
                self.visit_string(String::from(value))
            }

            #[inline]
            fn visit_string<E>(self, value: String) -> Result<Value, E>
            where
                E: de::Error,
            {
                Ok(Value::String(value))
            }
            #[inline]
            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                self.visit_byte_buf(v.to_owned())
            }

            #[inline]
            fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Value::Bytes(v))
            }

            #[inline]
            fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Value::U64(v))
            }

            #[inline]
            fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Value::I64(v))
            }

            #[inline]
            fn visit_bool<E>(self, v: bool) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Value::Bool(v))
            }

            #[inline]
            fn visit_none<E>(self) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                self.visit_unit()
            }

            #[inline]
            fn visit_unit<E>(self) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Value::Null)
            }

            #[inline]
            fn visit_seq<V>(
                self,
                mut visitor: V,
            ) -> Result<Self::Value, V::Error>
            where
                V: de::SeqAccess<'de>,
            {
                let mut vec = Vec::new();

                while let Some(elem) = visitor.next_element()? {
                    vec.push(elem);
                }

                Ok(Value::Array(vec))
            }

            #[inline]
            fn visit_map<V>(self, mut visitor: V) -> Result<Value, V::Error>
            where
                V: de::MapAccess<'de>,
            {
                let mut values = BTreeMap::new();

                while let Some((key, value)) = visitor.next_entry()? {
                    values.insert(key, value);
                }

                Ok(Value::Object(values))
            }

            #[inline]
            fn visit_f64<E>(self, v: f64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Value::F64(v))
            }
        }

        deserializer.deserialize_any(ValueVisitor)
    }
}
