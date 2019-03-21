use dhall_core::*;
use itertools::*;
use serde_cbor::value::value as cbor;
use std::path::PathBuf;
use std::rc::Rc;

type ParsedExpr = Rc<Expr<X, Import>>;

#[derive(Debug)]
pub enum DecodeError {
    CBORError(serde_cbor::error::Error),
    WrongFormatError,
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
    use Expr::*;
    Ok(rc(match data {
        String(s) => match Builtin::parse(s) {
            Some(b) => Expr::Builtin(b),
            None => match s.as_str() {
                "True" => BoolLit(true),
                "False" => BoolLit(false),
                "Type" => Const(Const::Type),
                "Kind" => Const(Const::Kind),
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
                let f = cbor_value_to_dhall(&f)?;
                let args = args
                    .iter()
                    .map(cbor_value_to_dhall)
                    .collect::<Result<Vec<_>, _>>()?;
                App(f, args)
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
                    _ => Err(DecodeError::WrongFormatError)?,
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
                EmptyOptionalLit(t)
            }
            [U64(5), Null, x] => {
                let x = cbor_value_to_dhall(&x)?;
                NEOptionalLit(x)
            }
            [U64(5), t, x] => {
                let x = cbor_value_to_dhall(&x)?;
                let t = cbor_value_to_dhall(&t)?;
                Annot(rc(NEOptionalLit(x)), t)
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
                let map = cbor_map_to_dhall_map(map)?;
                UnionType(map)
            }
            [U64(12), String(l), x, Object(map)] => {
                let map = cbor_map_to_dhall_map(map)?;
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
                                _ => Err(DecodeError::WrongFormatError)?,
                            };
                            Ok((x, y))
                        })
                        .collect::<Result<_, _>>()?,
                )))
            }
            [U64(24), Null, U64(0), U64(3), rest..] => {
                let mut path = PathBuf::new();
                for s in rest {
                    match s {
                        String(s) => path.push(s),
                        _ => Err(DecodeError::WrongFormatError)?,
                    }
                }
                Embed(Import {
                    mode: ImportMode::Code,
                    hash: None,
                    location: ImportLocation::Local(FilePrefix::Here, path),
                })
            }
            [U64(25), bindings..] => {
                let mut tuples = bindings.iter().tuples();
                let bindings = (&mut tuples)
                    .map(|(x, t, v)| {
                        let x = match x {
                            String(s) => Label::from(s.as_str()),
                            _ => Err(DecodeError::WrongFormatError)?,
                        };
                        let t = match t {
                            Null => None,
                            t => Some(cbor_value_to_dhall(&t)?),
                        };
                        let v = cbor_value_to_dhall(&v)?;
                        Ok((x, t, v))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let expr = tuples
                    .into_buffer()
                    .next()
                    .ok_or(DecodeError::WrongFormatError)?;
                let expr = cbor_value_to_dhall(expr)?;
                return Ok(bindings
                    .into_iter()
                    .fold(expr, |acc, (x, t, v)| rc(Let(x, t, v, acc))));
            }
            [U64(26), x, y] => {
                let x = cbor_value_to_dhall(&x)?;
                let y = cbor_value_to_dhall(&y)?;
                Annot(x, y)
            }
            _ => Err(DecodeError::WrongFormatError)?,
        },
        _ => Err(DecodeError::WrongFormatError)?,
    }))
}

fn cbor_map_to_dhall_map(
    map: &std::collections::BTreeMap<cbor::ObjectKey, cbor::Value>,
) -> Result<std::collections::BTreeMap<Label, ParsedExpr>, DecodeError> {
    map.iter()
        .map(|(k, v)| -> Result<(_, _), _> {
            let k = k.as_string().ok_or(DecodeError::WrongFormatError)?;
            let v = cbor_value_to_dhall(v)?;
            Ok((Label::from(k.as_ref()), v))
        })
        .collect::<Result<_, _>>()
}
