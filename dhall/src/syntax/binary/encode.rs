use serde_cbor::value::value as cbor;
use std::vec;

use crate::error::EncodeError;
use crate::syntax;
use crate::syntax::map::DupTreeMap;
use crate::syntax::{
    Expr, ExprKind, FilePrefix, Hash, Import, ImportLocation, ImportMode,
    Label, Scheme, V,
};

/// Warning: will fail if `expr` contains an `Embed` node.
pub(crate) fn encode<E>(expr: &Expr<E>) -> Result<Vec<u8>, EncodeError> {
    serde_cbor::ser::to_vec(&Serialize::Expr(expr))
        .map_err(|e| EncodeError::CBORError(e))
}

enum Serialize<'a, E> {
    Expr(&'a Expr<E>),
    CBOR(cbor::Value),
    RecordMap(&'a DupTreeMap<Label, Expr<E>>),
    UnionMap(&'a DupTreeMap<Label, Option<Expr<E>>>),
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

fn serialize_subexpr<S, E>(ser: S, e: &Expr<E>) -> Result<S::Ok, S::Error>
where
    S: serde::ser::Serializer,
{
    use cbor::Value::{String, I64, U64};
    use std::iter::once;
    use syntax::Builtin;
    use syntax::ExprKind::*;

    use self::Serialize::{RecordMap, UnionMap};
    fn expr<E>(x: &Expr<E>) -> self::Serialize<'_, E> {
        self::Serialize::Expr(x)
    }
    let cbor =
        |v: cbor::Value| -> self::Serialize<'_, E> { self::Serialize::CBOR(v) };
    let tag = |x: u64| cbor(U64(x));
    let null = || cbor(cbor::Value::Null);
    let label = |l: &Label| cbor(cbor::Value::String(l.into()));

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
                ExprKind::Builtin(Builtin::List) => {
                    ser_seq!(ser; tag(4), expr(a))
                }
                _ => ser_seq!(ser; tag(28), expr(x)),
            },
            _ => ser_seq!(ser; tag(28), expr(x)),
        },
        NEListLit(xs) => ser.collect_seq(
            once(tag(4)).chain(once(null())).chain(xs.iter().map(expr)),
        ),
        TextLit(xs) => {
            use syntax::InterpolatedTextContents::{Expr, Text};
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
            use syntax::BinOp::*;
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
        ToMap(x, None) => ser_seq!(ser; tag(27), expr(x)),
        ToMap(x, Some(y)) => ser_seq!(ser; tag(27), expr(x), expr(y)),
        Projection(x, ls) => ser.collect_seq(
            once(tag(10))
                .chain(once(expr(x)))
                .chain(ls.iter().map(label)),
        ),
        ProjectionByExpr(x, y) => {
            ser_seq!(ser; tag(10), expr(x), vec![expr(y)])
        }
        Completion(x, y) => ser_seq!(ser; tag(3), tag(13), expr(x), expr(y)),
        Import(import) => serialize_import(ser, import),
        Embed(_) => unimplemented!(
            "An expression with resolved imports cannot be binary-encoded"
        ),
    }
}

fn serialize_import<S, E>(
    ser: S,
    import: &Import<Expr<E>>,
) -> Result<S::Ok, S::Error>
where
    S: serde::ser::Serializer,
{
    use cbor::Value::{Bytes, Null, U64};
    use serde::ser::SerializeSeq;

    let count = 4 + match &import.location {
        ImportLocation::Remote(url) => 3 + url.path.file_path.len(),
        ImportLocation::Local(_, path) => path.file_path.len(),
        ImportLocation::Env(_) => 1,
        ImportLocation::Missing => 0,
    };
    let mut ser_seq = ser.serialize_seq(Some(count))?;

    ser_seq.serialize_element(&U64(24))?;

    let hash = match &import.hash {
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

    let scheme = match &import.location {
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

    match &import.location {
        ImportLocation::Remote(url) => {
            match &url.headers {
                None => ser_seq.serialize_element(&Null)?,
                Some(e) => {
                    ser_seq.serialize_element(&self::Serialize::Expr(e))?
                }
            };
            ser_seq.serialize_element(&url.authority)?;
            for p in url.path.file_path.iter() {
                ser_seq.serialize_element(&p)?;
            }
            match &url.query {
                None => ser_seq.serialize_element(&Null)?,
                Some(x) => ser_seq.serialize_element(x)?,
            };
        }
        ImportLocation::Local(_, path) => {
            for p in path.file_path.iter() {
                ser_seq.serialize_element(&p)?;
            }
        }
        ImportLocation::Env(env) => {
            ser_seq.serialize_element(env)?;
        }
        ImportLocation::Missing => {}
    }

    ser_seq.end()
}

impl<'a, E> serde::ser::Serialize for Serialize<'a, E> {
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

fn collect_nested_applications<'a, E>(
    e: &'a Expr<E>,
) -> (&'a Expr<E>, Vec<&'a Expr<E>>) {
    fn go<'a, E>(e: &'a Expr<E>, vec: &mut Vec<&'a Expr<E>>) -> &'a Expr<E> {
        match e.as_ref() {
            ExprKind::App(f, a) => {
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

type LetBinding<'a, E> = (&'a Label, &'a Option<Expr<E>>, &'a Expr<E>);

fn collect_nested_lets<'a, E>(
    e: &'a Expr<E>,
) -> (&'a Expr<E>, Vec<LetBinding<'a, E>>) {
    fn go<'a, E>(
        e: &'a Expr<E>,
        vec: &mut Vec<LetBinding<'a, E>>,
    ) -> &'a Expr<E> {
        match e.as_ref() {
            ExprKind::Let(l, t, v, e) => {
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
