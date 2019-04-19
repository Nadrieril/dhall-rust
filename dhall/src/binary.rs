use dhall_core::*;
use itertools::*;
use serde_cbor::value::value as cbor;

type ParsedExpr = SubExpr<X, Import>;

#[derive(Debug)]
pub enum DecodeError {
    CBORError(serde_cbor::error::Error),
    WrongFormatError(String),
}

pub fn decode(data: &[u8]) -> Result<ParsedExpr, DecodeError> {
    match serde_cbor::de::from_slice(data) {
        Ok(v) => cbor_value_to_dhall(&v),
        Err(e) => Err(DecodeError::CBORError(e)),
    }
}

fn cbor_value_to_dhall(data: &cbor::Value) -> Result<ParsedExpr, DecodeError> {
    use cbor::Value::*;
    use dhall_core::{BinOp, Builtin, Const};
    use ExprF::*;
    Ok(rc(match data {
        String(s) => match Builtin::parse(s) {
            Some(b) => ExprF::Builtin(b),
            None => match s.as_str() {
                "True" => BoolLit(true),
                "False" => BoolLit(false),
                "Type" => Const(Const::Type),
                "Kind" => Const(Const::Kind),
                "Sort" => Const(Const::Sort),
                s => Var(V(Label::from(s), 0)),
            },
        },
        U64(n) => Var(V(Label::from("_"), *n as usize)),
        F64(x) => DoubleLit((*x).into()),
        Bool(b) => BoolLit(*b),
        Array(vec) => match vec.as_slice() {
            [String(l), U64(n)] => {
                let l = Label::from(l.as_str());
                Var(V(l, *n as usize))
            }
            [U64(0), f, args..] => {
                let mut f = cbor_value_to_dhall(&f)?;
                for a in args {
                    let a = cbor_value_to_dhall(&a)?;
                    f = rc(App(f, a))
                }
                return Ok(f);
            }
            [U64(1), x, y] => {
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                Lam(Label::from("_"), x, y)
            }
            [U64(1), String(l), x, y] => {
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
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                let l = Label::from(l.as_str());
                Pi(l, x, y)
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
                    8 => Combine,
                    9 => Prefer,
                    10 => CombineTypes,
                    11 => ImportAlt,
                    _ => {
                        Err(DecodeError::WrongFormatError("binop".to_owned()))?
                    }
                };
                BinOp(op, x, y)
            }
            [U64(4), t] => {
                let t = cbor_value_to_dhall(&t)?;
                EmptyListLit(t)
            }
            [U64(4), Null, rest..] => {
                let rest = rest
                    .iter()
                    .map(cbor_value_to_dhall)
                    .collect::<Result<Vec<_>, _>>()?;
                NEListLit(rest)
            }
            [U64(5), t] => {
                let t = cbor_value_to_dhall(&t)?;
                OldOptionalLit(None, t)
            }
            [U64(5), Null, x] => {
                let x = cbor_value_to_dhall(&x)?;
                NEOptionalLit(x)
            }
            [U64(5), t, x] => {
                let x = cbor_value_to_dhall(&x)?;
                let t = cbor_value_to_dhall(&t)?;
                OldOptionalLit(Some(x), t)
            }
            [U64(6), x, y] => {
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                Merge(x, y, None)
            }
            [U64(6), x, y, z] => {
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                let z = cbor_value_to_dhall(&z)?;
                Merge(x, y, Some(z))
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
                Field(x, l)
            }
            [U64(11), Object(map)] => {
                let map = cbor_map_to_dhall_opt_map(map)?;
                UnionType(map)
            }
            [U64(12), String(l), x, Object(map)] => {
                let map = cbor_map_to_dhall_opt_map(map)?;
                let x = cbor_value_to_dhall(&x)?;
                let l = Label::from(l.as_str());
                UnionLit(l, x, map)
            }
            [U64(14), x, y, z] => {
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                let z = cbor_value_to_dhall(&z)?;
                BoolIf(x, y, z)
            }
            [U64(15), U64(x)] => NaturalLit(*x as Natural),
            [U64(16), U64(x)] => IntegerLit(*x as Integer),
            [U64(16), I64(x)] => IntegerLit(*x as Integer),
            [U64(18), String(first), rest..] => {
                TextLit(InterpolatedText::from((
                    first.clone(),
                    rest.iter()
                        .tuples()
                        .map(|(x, y)| {
                            let x = cbor_value_to_dhall(&x)?;
                            let y = match y {
                                String(s) => s.clone(),
                                _ => Err(DecodeError::WrongFormatError(
                                    "text".to_owned(),
                                ))?,
                            };
                            Ok((x, y))
                        })
                        .collect::<Result<_, _>>()?,
                )))
            }
            [U64(24), hash, U64(mode), U64(scheme), rest..] => {
                let mode = match mode {
                    1 => ImportMode::RawText,
                    _ => ImportMode::Code,
                };
                let hash = match hash {
                    Null => None,
                    Array(vec) => match vec.as_slice() {
                        [String(protocol), String(hash)] => Some(Hash {
                            protocol: protocol.clone(),
                            hash: hash.clone(),
                        }),
                        _ => Err(DecodeError::WrongFormatError(
                            "import/hash".to_owned(),
                        ))?,
                    },
                    _ => Err(DecodeError::WrongFormatError(
                        "import/hash".to_owned(),
                    ))?,
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
                                match cbor_value_to_dhall(&x)?.as_ref() {
                                    Embed(import) => Some(Box::new(
                                        import.location_hashed.clone(),
                                    )),
                                    _ => Err(DecodeError::WrongFormatError(
                                        "import/remote/headers".to_owned(),
                                    ))?,
                                }
                            }
                            _ => Err(DecodeError::WrongFormatError(
                                "import/remote/headers".to_owned(),
                            ))?,
                        };
                        let authority = match rest.next() {
                            Some(String(s)) => s.to_owned(),
                            _ => Err(DecodeError::WrongFormatError(
                                "import/remote/authority".to_owned(),
                            ))?,
                        };
                        let query = match rest.next_back() {
                            Some(Null) => None,
                            Some(String(s)) => Some(s.to_owned()),
                            _ => Err(DecodeError::WrongFormatError(
                                "import/remote/query".to_owned(),
                            ))?,
                        };
                        let path = rest
                            .map(|s| {
                                s.as_string().ok_or_else(|| {
                                    DecodeError::WrongFormatError(
                                        "import/remote/path".to_owned(),
                                    )
                                })
                            })
                            .collect::<Result<_, _>>()?;
                        ImportLocation::Remote(URL {
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
                            _ => Err(DecodeError::WrongFormatError(
                                "import/local/prefix".to_owned(),
                            ))?,
                        };
                        let path = rest
                            .map(|s| {
                                s.as_string().ok_or_else(|| {
                                    DecodeError::WrongFormatError(
                                        "import/local/path".to_owned(),
                                    )
                                })
                            })
                            .collect::<Result<_, _>>()?;
                        ImportLocation::Local(prefix, path)
                    }
                    6 => {
                        let env = match rest.next() {
                            Some(String(s)) => s.to_owned(),
                            _ => Err(DecodeError::WrongFormatError(
                                "import/env".to_owned(),
                            ))?,
                        };
                        ImportLocation::Env(env)
                    }
                    7 => ImportLocation::Missing,
                    _ => Err(DecodeError::WrongFormatError(
                        "import/type".to_owned(),
                    ))?,
                };
                Embed(Import {
                    mode,
                    location_hashed: ImportHashed { hash, location },
                })
            }
            [U64(25), bindings..] => {
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
            _ => Err(DecodeError::WrongFormatError(format!("{:?}", data)))?,
        },
        _ => Err(DecodeError::WrongFormatError(format!("{:?}", data)))?,
    }))
}

fn cbor_map_to_dhall_map(
    map: &std::collections::BTreeMap<cbor::ObjectKey, cbor::Value>,
) -> Result<std::collections::BTreeMap<Label, ParsedExpr>, DecodeError> {
    map.iter()
        .map(|(k, v)| -> Result<(_, _), _> {
            let k = k.as_string().ok_or_else(|| {
                DecodeError::WrongFormatError("map/key".to_owned())
            })?;
            let v = cbor_value_to_dhall(v)?;
            Ok((Label::from(k.as_ref()), v))
        })
        .collect::<Result<_, _>>()
}

fn cbor_map_to_dhall_opt_map(
    map: &std::collections::BTreeMap<cbor::ObjectKey, cbor::Value>,
) -> Result<std::collections::BTreeMap<Label, Option<ParsedExpr>>, DecodeError>
{
    map.iter()
        .map(|(k, v)| -> Result<(_, _), _> {
            let k = k.as_string().ok_or_else(|| {
                DecodeError::WrongFormatError("map/key".to_owned())
            })?;
            let v = match v {
                cbor::Value::Null => None,
                _ => Some(cbor_value_to_dhall(v)?),
            };
            Ok((Label::from(k.as_ref()), v))
        })
        .collect::<Result<_, _>>()
}
