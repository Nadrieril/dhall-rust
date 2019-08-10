use itertools::Itertools;
use serde_cbor::value::value as cbor;
use std::iter::FromIterator;

use dhall_syntax::map::DupTreeMap;
use dhall_syntax::{
    rc, ExprF, FilePrefix, Hash, Import, ImportHashed, ImportLocation,
    ImportMode, Integer, InterpolatedText, Label, Natural, Scheme, SubExpr,
    URL, V,
};

use crate::error::{DecodeError, EncodeError};
use crate::phase::{DecodedSubExpr, ParsedSubExpr};

pub fn decode(data: &[u8]) -> Result<DecodedSubExpr, DecodeError> {
    match serde_cbor::de::from_slice(data) {
        Ok(v) => cbor_value_to_dhall(&v),
        Err(e) => Err(DecodeError::CBORError(e)),
    }
}

//TODO: encode normalized expression too
pub fn encode(expr: &ParsedSubExpr) -> Result<Vec<u8>, EncodeError> {
    serde_cbor::ser::to_vec(&Serialize::Expr(expr))
        .map_err(|e| EncodeError::CBORError(e))
}

fn cbor_value_to_dhall(
    data: &cbor::Value,
) -> Result<DecodedSubExpr, DecodeError> {
    use cbor::Value::*;
    use dhall_syntax::{BinOp, Builtin, Const};
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
            [U64(0), f, args..] => {
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
                EmptyListLit(rc(App(rc(ExprF::Builtin(Builtin::List)), t)))
            }
            [U64(4), Null, rest..] => {
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
                App(rc(ExprF::Builtin(Builtin::OptionalNone)), t)
            }
            [U64(5), t, x] => {
                let x = cbor_value_to_dhall(&x)?;
                let t = cbor_value_to_dhall(&t)?;
                Annot(
                    rc(SomeLit(x)),
                    rc(App(rc(ExprF::Builtin(Builtin::Optional)), t)),
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
            [U64(10), x, rest..] => {
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
            [U64(19), t] => {
                let t = cbor_value_to_dhall(&t)?;
                Assert(t)
            }
            [U64(24), hash, U64(mode), U64(scheme), rest..] => {
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
                        [18, 32, rest..] => Some(Hash::SHA256(rest.to_vec())),
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
                            // TODO
                            // Some(x) => {
                            //     match cbor_value_to_dhall(&x)?.as_ref() {
                            //         Embed(import) => Some(Box::new(
                            //             import.location_hashed.clone(),
                            //         )),
                            //         _ => Err(DecodeError::WrongFormatError(
                            //             "import/remote/headers".to_owned(),
                            //         ))?,
                            //     }
                            // }
                            _ => Err(DecodeError::WrongFormatError(
                                "import/remote/headers is unimplemented"
                                    .to_owned(),
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
                            .map(|s| match s.as_string() {
                                Some(s) => Ok(s.clone()),
                                None => Err(DecodeError::WrongFormatError(
                                    "import/remote/path".to_owned(),
                                )),
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
                            .map(|s| match s.as_string() {
                                Some(s) => Ok(s.clone()),
                                None => Err(DecodeError::WrongFormatError(
                                    "import/local/path".to_owned(),
                                )),
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
    T: FromIterator<(Label, DecodedSubExpr)>,
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
    T: FromIterator<(Label, Option<DecodedSubExpr>)>,
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

enum Serialize<'a> {
    Expr(&'a ParsedSubExpr),
    CBOR(cbor::Value),
    RecordMap(&'a DupTreeMap<Label, ParsedSubExpr>),
    UnionMap(&'a DupTreeMap<Label, Option<ParsedSubExpr>>),
}

macro_rules! count {
    (@replace_with $_t:tt $sub:expr) => { $sub };
    ($($tts:tt)*) => {0usize $(+ count!(@replace_with $tts 1usize))*};
}

macro_rules! ser_seq {
    ($ser:expr; $($elt:expr),* $(,)?) => {{
        use serde::ser::SerializeSeq;
        let count = count!($($elt)*);
        let mut ser_seq = $ser.serialize_seq(Some(count))?;
        $(
            ser_seq.serialize_element(&$elt)?;
        )*
        ser_seq.end()
    }};
}

fn serialize_subexpr<S>(ser: S, e: &ParsedSubExpr) -> Result<S::Ok, S::Error>
where
    S: serde::ser::Serializer,
{
    use cbor::Value::{String, I64, U64};
    use dhall_syntax::Builtin;
    use dhall_syntax::ExprF::*;
    use std::iter::once;

    use self::Serialize::{RecordMap, UnionMap};
    fn expr(x: &ParsedSubExpr) -> self::Serialize<'_> {
        self::Serialize::Expr(x)
    }
    fn cbor<'a>(v: cbor::Value) -> self::Serialize<'a> {
        self::Serialize::CBOR(v)
    }
    fn tag<'a>(x: u64) -> self::Serialize<'a> {
        cbor(U64(x))
    }
    fn null<'a>() -> self::Serialize<'a> {
        cbor(cbor::Value::Null)
    }
    fn label<'a>(l: &Label) -> self::Serialize<'a> {
        cbor(cbor::Value::String(l.into()))
    }

    match e.as_ref() {
        Const(c) => ser.serialize_str(&c.to_string()),
        Builtin(b) => ser.serialize_str(&b.to_string()),
        BoolLit(b) => ser.serialize_bool(*b),
        NaturalLit(n) => ser_seq!(ser; tag(15), U64(*n as u64)),
        IntegerLit(n) => ser_seq!(ser; tag(16), I64(*n as i64)),
        DoubleLit(n) => {
            let n: f64 = (*n).into();
            ser.serialize_f64(n)
        }
        BoolIf(x, y, z) => ser_seq!(ser; tag(14), expr(x), expr(y), expr(z)),
        Var(V(l, n)) if l == &"_".into() => ser.serialize_u64(*n as u64),
        Var(V(l, n)) => ser_seq!(ser; label(l), U64(*n as u64)),
        Lam(l, x, y) if l == &"_".into() => {
            ser_seq!(ser; tag(1), expr(x), expr(y))
        }
        Lam(l, x, y) => ser_seq!(ser; tag(1), label(l), expr(x), expr(y)),
        Pi(l, x, y) if l == &"_".into() => {
            ser_seq!(ser; tag(2), expr(x), expr(y))
        }
        Pi(l, x, y) => ser_seq!(ser; tag(2), label(l), expr(x), expr(y)),
        Let(_, _, _, _) => {
            let (bound_e, bindings) = collect_nested_lets(e);
            let count = 1 + 3 * bindings.len() + 1;

            use serde::ser::SerializeSeq;
            let mut ser_seq = ser.serialize_seq(Some(count))?;
            ser_seq.serialize_element(&tag(25))?;
            for (l, t, v) in bindings {
                ser_seq.serialize_element(&label(l))?;
                match t {
                    Some(t) => ser_seq.serialize_element(&expr(t))?,
                    None => ser_seq.serialize_element(&null())?,
                }
                ser_seq.serialize_element(&expr(v))?;
            }
            ser_seq.serialize_element(&expr(bound_e))?;
            ser_seq.end()
        }
        App(_, _) => {
            let (f, args) = collect_nested_applications(e);
            ser.collect_seq(
                once(tag(0))
                    .chain(once(expr(f)))
                    .chain(args.into_iter().rev().map(expr)),
            )
        }
        Annot(x, y) => ser_seq!(ser; tag(26), expr(x), expr(y)),
        Assert(x) => ser_seq!(ser; tag(19), expr(x)),
        SomeLit(x) => ser_seq!(ser; tag(5), null(), expr(x)),
        EmptyListLit(x) => match x.as_ref() {
            App(f, a) => match f.as_ref() {
                ExprF::Builtin(Builtin::List) => ser_seq!(ser; tag(4), expr(a)),
                _ => ser_seq!(ser; tag(28), expr(x)),
            },
            _ => ser_seq!(ser; tag(28), expr(x)),
        },
        NEListLit(xs) => ser.collect_seq(
            once(tag(4)).chain(once(null())).chain(xs.iter().map(expr)),
        ),
        TextLit(xs) => {
            use dhall_syntax::InterpolatedTextContents::{Expr, Text};
            ser.collect_seq(once(tag(18)).chain(xs.iter().map(|x| match x {
                Expr(x) => expr(x),
                Text(x) => cbor(String(x.clone())),
            })))
        }
        RecordType(map) => ser_seq!(ser; tag(7), RecordMap(map)),
        RecordLit(map) => ser_seq!(ser; tag(8), RecordMap(map)),
        UnionType(map) => ser_seq!(ser; tag(11), UnionMap(map)),
        Field(x, l) => ser_seq!(ser; tag(9), expr(x), label(l)),
        BinOp(op, x, y) => {
            use dhall_syntax::BinOp::*;
            let op = match op {
                BoolOr => 0,
                BoolAnd => 1,
                BoolEQ => 2,
                BoolNE => 3,
                NaturalPlus => 4,
                NaturalTimes => 5,
                TextAppend => 6,
                ListAppend => 7,
                RecursiveRecordMerge => 8,
                RightBiasedRecordMerge => 9,
                RecursiveRecordTypeMerge => 10,
                ImportAlt => 11,
                Equivalence => 12,
            };
            ser_seq!(ser; tag(3), U64(op), expr(x), expr(y))
        }
        Merge(x, y, None) => ser_seq!(ser; tag(6), expr(x), expr(y)),
        Merge(x, y, Some(z)) => {
            ser_seq!(ser; tag(6), expr(x), expr(y), expr(z))
        }
        Projection(x, ls) => ser.collect_seq(
            once(tag(10))
                .chain(once(expr(x)))
                .chain(ls.iter().map(label)),
        ),
        Embed(import) => serialize_import(ser, import),
    }
}

fn serialize_import<S>(ser: S, import: &Import) -> Result<S::Ok, S::Error>
where
    S: serde::ser::Serializer,
{
    use cbor::Value::{Bytes, Null, U64};
    use serde::ser::SerializeSeq;

    let count = 4 + match &import.location_hashed.location {
        ImportLocation::Remote(url) => 3 + url.path.len(),
        ImportLocation::Local(_, path) => path.len(),
        ImportLocation::Env(_) => 1,
        ImportLocation::Missing => 0,
    };
    let mut ser_seq = ser.serialize_seq(Some(count))?;

    ser_seq.serialize_element(&U64(24))?;

    let hash = match &import.location_hashed.hash {
        None => Null,
        Some(Hash::SHA256(h)) => {
            let mut bytes = vec![18, 32];
            bytes.extend_from_slice(h);
            Bytes(bytes)
        }
    };
    ser_seq.serialize_element(&hash)?;

    let mode = match import.mode {
        ImportMode::Code => 0,
        ImportMode::RawText => 1,
        ImportMode::Location => 2,
    };
    ser_seq.serialize_element(&U64(mode))?;

    let scheme = match &import.location_hashed.location {
        ImportLocation::Remote(url) => match url.scheme {
            Scheme::HTTP => 0,
            Scheme::HTTPS => 1,
        },
        ImportLocation::Local(prefix, _) => match prefix {
            FilePrefix::Absolute => 2,
            FilePrefix::Here => 3,
            FilePrefix::Parent => 4,
            FilePrefix::Home => 5,
        },
        ImportLocation::Env(_) => 6,
        ImportLocation::Missing => 7,
    };
    ser_seq.serialize_element(&U64(scheme))?;

    match &import.location_hashed.location {
        ImportLocation::Remote(url) => {
            match &url.headers {
                None => ser_seq.serialize_element(&Null)?,
                Some(location_hashed) => {
                    ser_seq.serialize_element(&self::Serialize::Expr(
                        &SubExpr::from_expr_no_note(ExprF::Embed(Import {
                            mode: ImportMode::Code,
                            location_hashed: location_hashed.as_ref().clone(),
                        })),
                    ))?
                }
            };
            ser_seq.serialize_element(&url.authority)?;
            for p in &url.path {
                ser_seq.serialize_element(p)?;
            }
            match &url.query {
                None => ser_seq.serialize_element(&Null)?,
                Some(x) => ser_seq.serialize_element(x)?,
            };
        }
        ImportLocation::Local(_, path) => {
            for p in path {
                ser_seq.serialize_element(p)?;
            }
        }
        ImportLocation::Env(env) => {
            ser_seq.serialize_element(env)?;
        }
        ImportLocation::Missing => {}
    }

    ser_seq.end()
}

impl<'a> serde::ser::Serialize for Serialize<'a> {
    fn serialize<S>(&self, ser: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        match self {
            Serialize::Expr(e) => serialize_subexpr(ser, e),
            Serialize::CBOR(v) => v.serialize(ser),
            Serialize::RecordMap(map) => {
                ser.collect_map(map.iter().map(|(k, v)| {
                    (cbor::Value::String(k.into()), Serialize::Expr(v))
                }))
            }
            Serialize::UnionMap(map) => {
                ser.collect_map(map.iter().map(|(k, v)| {
                    let v = match v {
                        Some(x) => Serialize::Expr(x),
                        None => Serialize::CBOR(cbor::Value::Null),
                    };
                    (cbor::Value::String(k.into()), v)
                }))
            }
        }
    }
}

fn collect_nested_applications<'a, N, E>(
    e: &'a SubExpr<N, E>,
) -> (&'a SubExpr<N, E>, Vec<&'a SubExpr<N, E>>) {
    fn go<'a, N, E>(
        e: &'a SubExpr<N, E>,
        vec: &mut Vec<&'a SubExpr<N, E>>,
    ) -> &'a SubExpr<N, E> {
        match e.as_ref() {
            ExprF::App(f, a) => {
                vec.push(a);
                go(f, vec)
            }
            _ => e,
        }
    }
    let mut vec = vec![];
    let e = go(e, &mut vec);
    (e, vec)
}

type LetBinding<'a, N, E> =
    (&'a Label, &'a Option<SubExpr<N, E>>, &'a SubExpr<N, E>);

fn collect_nested_lets<'a, N, E>(
    e: &'a SubExpr<N, E>,
) -> (&'a SubExpr<N, E>, Vec<LetBinding<'a, N, E>>) {
    fn go<'a, N, E>(
        e: &'a SubExpr<N, E>,
        vec: &mut Vec<LetBinding<'a, N, E>>,
    ) -> &'a SubExpr<N, E> {
        match e.as_ref() {
            ExprF::Let(l, t, v, e) => {
                vec.push((l, t, v));
                go(e, vec)
            }
            _ => e,
        }
    }
    let mut vec = vec![];
    let e = go(e, &mut vec);
    (e, vec)
}
