use itertools::Itertools;
use serde_cbor::value::value as cbor;
use std::iter::FromIterator;

use crate::error::DecodeError;
use crate::syntax;
use crate::syntax::{
    Expr, ExprKind, FilePath, FilePrefix, Hash, ImportLocation, ImportMode,
    Integer, InterpolatedText, Label, Natural, Scheme, Span, UnspannedExpr,
    URL, V,
};
use crate::DecodedExpr;

pub(crate) fn decode(data: &[u8]) -> Result<DecodedExpr, DecodeError> {
    match serde_cbor::de::from_slice(data) {
        Ok(v) => cbor_value_to_dhall(&v),
        Err(e) => Err(DecodeError::CBORError(e)),
    }
}

// Should probably rename this
fn rc<E>(x: UnspannedExpr<E>) -> Expr<E> {
    Expr::new(x, Span::Decoded)
}

fn cbor_value_to_dhall(data: &cbor::Value) -> Result<DecodedExpr, DecodeError> {
    use cbor::Value::*;
    use syntax::{BinOp, Builtin, Const};
    use ExprKind::*;
    Ok(rc(match data {
        String(s) => match Builtin::parse(s) {
            Some(b) => ExprKind::Builtin(b),
            None => match s.as_str() {
                "True" => BoolLit(true),
                "False" => BoolLit(false),
                "Type" => Const(Const::Type),
                "Kind" => Const(Const::Kind),
                "Sort" => Const(Const::Sort),
                _ => Err(DecodeError::WrongFormatError("builtin".to_owned()))?,
            },
        },
        U64(n) => Var(V(Label::from("_"), *n as usize)),
        F64(x) => DoubleLit((*x).into()),
        Bool(b) => BoolLit(*b),
        Array(vec) => match vec.as_slice() {
            [String(l), U64(n)] => {
                if l.as_str() == "_" {
                    Err(DecodeError::WrongFormatError(
                        "`_` variable was encoded incorrectly".to_owned(),
                    ))?
                }
                let l = Label::from(l.as_str());
                Var(V(l, *n as usize))
            }
            [U64(0), f, args @ ..] => {
                if args.is_empty() {
                    Err(DecodeError::WrongFormatError(
                        "Function application must have at least one argument"
                            .to_owned(),
                    ))?
                }
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
                if l.as_str() == "_" {
                    Err(DecodeError::WrongFormatError(
                        "`_` variable was encoded incorrectly".to_owned(),
                    ))?
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
                    Err(DecodeError::WrongFormatError(
                        "`_` variable was encoded incorrectly".to_owned(),
                    ))?
                }
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                let l = Label::from(l.as_str());
                Pi(l, x, y)
            }
            [U64(3), U64(13), x, y] => {
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                Completion(x, y)
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
                        Err(DecodeError::WrongFormatError("binop".to_owned()))?
                    }
                };
                BinOp(op, x, y)
            }
            [U64(4), t] => {
                let t = cbor_value_to_dhall(&t)?;
                EmptyListLit(rc(App(rc(ExprKind::Builtin(Builtin::List)), t)))
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
                App(rc(ExprKind::Builtin(Builtin::OptionalNone)), t)
            }
            [U64(5), t, x] => {
                let x = cbor_value_to_dhall(&x)?;
                let t = cbor_value_to_dhall(&t)?;
                Annot(
                    rc(SomeLit(x)),
                    rc(App(rc(ExprKind::Builtin(Builtin::Optional)), t)),
                )
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
            [U64(10), x, Array(arr)] => {
                let x = cbor_value_to_dhall(&x)?;
                if let [y] = arr.as_slice() {
                    let y = cbor_value_to_dhall(&y)?;
                    ProjectionByExpr(x, y)
                } else {
                    Err(DecodeError::WrongFormatError(
                        "projection-by-expr".to_owned(),
                    ))?
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
                Projection(x, labels)
            }
            [U64(11), Object(map)] => {
                let map = cbor_map_to_dhall_opt_map(map)?;
                UnionType(map)
            }
            [U64(12), ..] => Err(DecodeError::WrongFormatError(
                "Union literals are not supported anymore".to_owned(),
            ))?,
            [U64(14), x, y, z] => {
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                let z = cbor_value_to_dhall(&z)?;
                BoolIf(x, y, z)
            }
            [U64(15), U64(x)] => NaturalLit(*x as Natural),
            [U64(16), U64(x)] => IntegerLit(*x as Integer),
            [U64(16), I64(x)] => IntegerLit(*x as Integer),
            [U64(18), String(first), rest @ ..] => {
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
            [U64(19), t] => {
                let t = cbor_value_to_dhall(&t)?;
                Assert(t)
            }
            [U64(24), hash, U64(mode), U64(scheme), rest @ ..] => {
                let mode = match mode {
                    0 => ImportMode::Code,
                    1 => ImportMode::RawText,
                    2 => ImportMode::Location,
                    _ => Err(DecodeError::WrongFormatError(format!(
                        "import/mode/unknown_mode: {:?}",
                        mode
                    )))?,
                };
                let hash = match hash {
                    Null => None,
                    Bytes(bytes) => match bytes.as_slice() {
                        [18, 32, rest @ ..] => {
                            Some(Hash::SHA256(rest.to_vec()))
                        }
                        _ => Err(DecodeError::WrongFormatError(format!(
                            "import/hash/unknown_multihash: {:?}",
                            bytes
                        )))?,
                    },
                    _ => Err(DecodeError::WrongFormatError(
                        "import/hash/should_be_bytes".to_owned(),
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
                                let x = cbor_value_to_dhall(&x)?;
                                Some(x)
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
                        let file_path = rest
                            .map(|s| match s.as_string() {
                                Some(s) => Ok(s.clone()),
                                None => Err(DecodeError::WrongFormatError(
                                    "import/remote/path".to_owned(),
                                )),
                            })
                            .collect::<Result<_, _>>()?;
                        let path = FilePath { file_path };
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
                        let file_path = rest
                            .map(|s| match s.as_string() {
                                Some(s) => Ok(s.clone()),
                                None => Err(DecodeError::WrongFormatError(
                                    "import/local/path".to_owned(),
                                )),
                            })
                            .collect::<Result<_, _>>()?;
                        let path = FilePath { file_path };
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
                ToMap(x, None)
            }
            [U64(27), x, y] => {
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                ToMap(x, Some(y))
            }
            [U64(28), x] => {
                let x = cbor_value_to_dhall(&x)?;
                EmptyListLit(x)
            }
            _ => Err(DecodeError::WrongFormatError(format!("{:?}", data)))?,
        },
        _ => Err(DecodeError::WrongFormatError(format!("{:?}", data)))?,
    }))
}

fn cbor_map_to_dhall_map<'a, T>(
    map: impl IntoIterator<Item = (&'a cbor::ObjectKey, &'a cbor::Value)>,
) -> Result<T, DecodeError>
where
    T: FromIterator<(Label, DecodedExpr)>,
{
    map.into_iter()
        .map(|(k, v)| -> Result<(_, _), _> {
            let k = k.as_string().ok_or_else(|| {
                DecodeError::WrongFormatError("map/key".to_owned())
            })?;
            let v = cbor_value_to_dhall(v)?;
            Ok((Label::from(k.as_ref()), v))
        })
        .collect::<Result<_, _>>()
}

fn cbor_map_to_dhall_opt_map<'a, T>(
    map: impl IntoIterator<Item = (&'a cbor::ObjectKey, &'a cbor::Value)>,
) -> Result<T, DecodeError>
where
    T: FromIterator<(Label, Option<DecodedExpr>)>,
{
    map.into_iter()
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
