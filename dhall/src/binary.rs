use dhall_core::*;
use itertools::*;
use serde_cbor::value::value as cbor;

type ParsedExpr = Expr<X, Import>;

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
    match data {
        String(s) => match Builtin::parse(s) {
            Some(b) => Ok(Expr::Builtin(b)),
            None => match s.as_str() {
                "True" => Ok(Expr::BoolLit(true)),
                "False" => Ok(Expr::BoolLit(false)),
                "Type" => Ok(Expr::Const(Const::Type)),
                "Kind" => Ok(Expr::Const(Const::Kind)),
                s => Ok(Expr::Var(V(Label::from(s), 0))),
            },
        },
        U64(n) => Ok(Expr::Var(V(Label::from("_"), *n as usize))),
        F64(x) => Ok(DoubleLit(*x)),
        Bool(b) => Ok(BoolLit(*b)),
        Array(vec) => match vec.as_slice() {
            [String(l), U64(n)] => {
                let l = Label::from(l.as_str());
                Ok(Expr::Var(V(l, *n as usize)))
            }
            [U64(0), f, args..] => {
                let f = cbor_value_to_dhall(&f)?;
                let args = args
                    .iter()
                    .map(cbor_value_to_dhall)
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(args
                    .into_iter()
                    .fold(f, |acc, e| (Expr::App(bx(acc), bx(e)))))
            }
            [U64(1), x, y] => {
                let x = bx(cbor_value_to_dhall(&x)?);
                let y = bx(cbor_value_to_dhall(&y)?);
                Ok(Lam(Label::from("_"), x, y))
            }
            [U64(1), String(l), x, y] => {
                let x = bx(cbor_value_to_dhall(&x)?);
                let y = bx(cbor_value_to_dhall(&y)?);
                let l = Label::from(l.as_str());
                Ok(Lam(l, x, y))
            }
            [U64(2), x, y] => {
                let x = bx(cbor_value_to_dhall(&x)?);
                let y = bx(cbor_value_to_dhall(&y)?);
                Ok(Pi(Label::from("_"), x, y))
            }
            [U64(2), String(l), x, y] => {
                let x = bx(cbor_value_to_dhall(&x)?);
                let y = bx(cbor_value_to_dhall(&y)?);
                let l = Label::from(l.as_str());
                Ok(Pi(l, x, y))
            }
            [U64(3), U64(n), x, y] => {
                let x = bx(cbor_value_to_dhall(&x)?);
                let y = bx(cbor_value_to_dhall(&y)?);
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
                Ok(BinOp(op, x, y))
            }
            [U64(4), t] => {
                let t = bx(cbor_value_to_dhall(&t)?);
                Ok(ListLit(Some(t), vec![]))
            }
            [U64(4), Null, rest..] => {
                let rest = rest
                    .iter()
                    .map(cbor_value_to_dhall)
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(ListLit(None, rest))
            }
            [U64(5), t] => {
                let t = bx(cbor_value_to_dhall(&t)?);
                Ok(OptionalLit(Some(t), vec![]))
            }
            [U64(5), Null, x] => {
                let x = cbor_value_to_dhall(&x)?;
                Ok(OptionalLit(None, vec![x]))
            }
            [U64(5), t, x] => {
                let x = cbor_value_to_dhall(&x)?;
                let t = bx(cbor_value_to_dhall(&t)?);
                Ok(OptionalLit(Some(t), vec![x]))
            }
            [U64(6), x, y] => {
                let x = bx(cbor_value_to_dhall(&x)?);
                let y = bx(cbor_value_to_dhall(&y)?);
                Ok(Merge(x, y, None))
            }
            [U64(6), x, y, z] => {
                let x = bx(cbor_value_to_dhall(&x)?);
                let y = bx(cbor_value_to_dhall(&y)?);
                let z = bx(cbor_value_to_dhall(&z)?);
                Ok(Merge(x, y, Some(z)))
            }
            [U64(7), Object(map)] => {
                let map = cbor_map_to_dhall_map(map)?;
                Ok(Record(map))
            }
            [U64(8), Object(map)] => {
                let map = cbor_map_to_dhall_map(map)?;
                Ok(RecordLit(map))
            }
            [U64(9), x, String(l)] => {
                let x = bx(cbor_value_to_dhall(&x)?);
                let l = Label::from(l.as_str());
                Ok(Field(x, l))
            }
            [U64(11), Object(map)] => {
                let map = cbor_map_to_dhall_map(map)?;
                Ok(Union(map))
            }
            [U64(12), String(l), x, Object(map)] => {
                let map = cbor_map_to_dhall_map(map)?;
                let x = bx(cbor_value_to_dhall(&x)?);
                let l = Label::from(l.as_str());
                Ok(UnionLit(l, x, map))
            }
            [U64(14), x, y, z] => {
                let x = bx(cbor_value_to_dhall(&x)?);
                let y = bx(cbor_value_to_dhall(&y)?);
                let z = bx(cbor_value_to_dhall(&z)?);
                Ok(BoolIf(x, y, z))
            }
            [U64(15), U64(x)] => Ok(NaturalLit(*x as Natural)),
            [U64(16), U64(x)] => Ok(IntegerLit(*x as Integer)),
            [U64(16), I64(x)] => Ok(IntegerLit(*x as Integer)),
            [U64(18), String(first), _rest..] => {
                // TODO: interpolated string
                Ok(TextLit(first.clone()))
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
                            t => Some(bx(cbor_value_to_dhall(&t)?)),
                        };
                        let v = bx(cbor_value_to_dhall(&v)?);
                        Ok((x, t, v))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let expr = tuples
                    .into_buffer()
                    .next()
                    .ok_or(DecodeError::WrongFormatError)?;
                let expr = cbor_value_to_dhall(expr)?;
                Ok(bindings
                    .into_iter()
                    .fold(expr, |acc, (x, t, v)| Let(x, t, v, bx(acc))))
            }
            [U64(26), x, y] => {
                let x = bx(cbor_value_to_dhall(&x)?);
                let y = bx(cbor_value_to_dhall(&y)?);
                Ok(Annot(x, y))
            }
            _ => Err(DecodeError::WrongFormatError),
        },
        _ => Err(DecodeError::WrongFormatError),
    }
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
