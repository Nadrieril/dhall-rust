use std::collections::BTreeMap;
use std::vec;

use crate::builtins::Builtin;
use crate::error::EncodeError;
use crate::operations::{BinOp, OpKind};
use crate::syntax;
use crate::syntax::{
    Expr, ExprKind, FilePrefix, Hash, Import, ImportMode, ImportTarget, Label,
    Scheme, V,
};

pub fn encode(expr: &Expr) -> Result<Vec<u8>, EncodeError> {
    serde_cbor::ser::to_vec(&Serialize::Expr(expr))
        .map_err(EncodeError::CBORError)
}

enum Serialize<'a> {
    Null,
    Tag(u64),
    Label(&'a Label),
    Text(String),
    Bytes(Vec<u8>),

    Expr(&'a Expr),
    RecordMap(&'a BTreeMap<Label, Expr>),
    UnionMap(&'a BTreeMap<Label, Option<Expr>>),
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

fn serialize_subexpr<S>(ser: S, e: &Expr) -> Result<S::Ok, S::Error>
where
    S: serde::ser::Serializer,
{
    use std::iter::once;
    use syntax::ExprKind::*;
    use syntax::NumKind::*;
    use OpKind::*;

    use self::Serialize::{RecordMap, UnionMap};
    fn expr(x: &Expr) -> self::Serialize<'_> {
        self::Serialize::Expr(x)
    }
    fn label(x: &Label) -> self::Serialize<'_> {
        self::Serialize::Label(x)
    }
    let tag = |x: u64| Serialize::Tag(x);
    let null = || Serialize::Null;

    match e.as_ref() {
        Const(c) => ser.serialize_str(&c.to_string()),
        Builtin(b) => ser.serialize_str(&b.to_string()),
        Num(Bool(b)) => ser.serialize_bool(*b),
        Num(Natural(n)) => ser_seq!(ser; tag(15), n),
        Num(Integer(n)) => ser_seq!(ser; tag(16), n),
        Num(Double(n)) => {
            let n: f64 = (*n).into();
            ser.serialize_f64(n)
        }
        Op(BoolIf(x, y, z)) => {
            ser_seq!(ser; tag(14), expr(x), expr(y), expr(z))
        }
        Var(V(l, n)) if l.as_ref() == "_" => ser.serialize_u64(*n as u64),
        Var(V(l, n)) => ser_seq!(ser; label(l), (*n as u64)),
        Lam(l, x, y) if l.as_ref() == "_" => {
            ser_seq!(ser; tag(1), expr(x), expr(y))
        }
        Lam(l, x, y) => ser_seq!(ser; tag(1), label(l), expr(x), expr(y)),
        Pi(l, x, y) if l.as_ref() == "_" => {
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
        Op(App(_, _)) => {
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
            Op(App(f, a)) => match f.as_ref() {
                ExprKind::Builtin(self::Builtin::List) => {
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
                Text(x) => Serialize::Text(x),
            })))
        }
        RecordType(map) => ser_seq!(ser; tag(7), RecordMap(map)),
        RecordLit(map) => ser_seq!(ser; tag(8), RecordMap(map)),
        UnionType(map) => ser_seq!(ser; tag(11), UnionMap(map)),
        Op(Field(x, l)) => ser_seq!(ser; tag(9), expr(x), label(l)),
        Op(BinOp(op, x, y)) => {
            use self::BinOp::*;
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
            ser_seq!(ser; tag(3), op, expr(x), expr(y))
        }
        Op(Merge(x, y, None)) => ser_seq!(ser; tag(6), expr(x), expr(y)),
        Op(Merge(x, y, Some(z))) => {
            ser_seq!(ser; tag(6), expr(x), expr(y), expr(z))
        }
        Op(ToMap(x, None)) => ser_seq!(ser; tag(27), expr(x)),
        Op(ToMap(x, Some(y))) => ser_seq!(ser; tag(27), expr(x), expr(y)),
        Op(Projection(x, ls)) => ser.collect_seq(
            once(tag(10))
                .chain(once(expr(x)))
                .chain(ls.iter().map(label)),
        ),
        Op(ProjectionByExpr(x, y)) => {
            ser_seq!(ser; tag(10), expr(x), vec![expr(y)])
        }
        Op(Completion(x, y)) => {
            ser_seq!(ser; tag(3), tag(13), expr(x), expr(y))
        }
        Op(With(x, ls, y)) => {
            let ls: Vec<_> = ls.iter().map(label).collect();
            ser_seq!(ser; tag(29), expr(x), ls, expr(y))
        }
        Import(import) => serialize_import(ser, import),
    }
}

fn serialize_import<S>(ser: S, import: &Import<Expr>) -> Result<S::Ok, S::Error>
where
    S: serde::ser::Serializer,
{
    use serde::ser::SerializeSeq;
    use Serialize::Null;

    let count = 4 + match &import.location {
        ImportTarget::Remote(url) => 3 + url.path.file_path.len(),
        ImportTarget::Local(_, path) => path.file_path.len(),
        ImportTarget::Env(_) => 1,
        ImportTarget::Missing => 0,
    };
    let mut ser_seq = ser.serialize_seq(Some(count))?;

    ser_seq.serialize_element(&24)?;

    match &import.hash {
        None => ser_seq.serialize_element(&Null)?,
        Some(Hash::SHA256(h)) => {
            let mut bytes = vec![18, 32];
            bytes.extend_from_slice(h);
            ser_seq.serialize_element(&Serialize::Bytes(bytes))?;
        }
    }

    let mode = match import.mode {
        ImportMode::Code => 0,
        ImportMode::RawText => 1,
        ImportMode::Location => 2,
    };
    ser_seq.serialize_element(&mode)?;

    let scheme = match &import.location {
        ImportTarget::Remote(url) => match url.scheme {
            Scheme::HTTP => 0,
            Scheme::HTTPS => 1,
        },
        ImportTarget::Local(prefix, _) => match prefix {
            FilePrefix::Absolute => 2,
            FilePrefix::Here => 3,
            FilePrefix::Parent => 4,
            FilePrefix::Home => 5,
        },
        ImportTarget::Env(_) => 6,
        ImportTarget::Missing => 7,
    };
    ser_seq.serialize_element(&scheme)?;

    match &import.location {
        ImportTarget::Remote(url) => {
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
        ImportTarget::Local(_, path) => {
            for p in path.file_path.iter() {
                ser_seq.serialize_element(&p)?;
            }
        }
        ImportTarget::Env(env) => {
            ser_seq.serialize_element(env)?;
        }
        ImportTarget::Missing => {}
    }

    ser_seq.end()
}

impl<'a> serde::ser::Serialize for Serialize<'a> {
    fn serialize<S>(&self, ser: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        use Serialize::*;
        match self {
            Null => ser.serialize_unit(),
            Tag(v) => ser.serialize_u64(*v),
            Label(v) => ser.serialize_str(v.as_ref()),
            Text(v) => ser.serialize_str(v),
            Bytes(v) => ser.serialize_bytes(v),

            Expr(e) => serialize_subexpr(ser, e),
            RecordMap(map) => {
                ser.collect_map(map.iter().map(|(k, v)| (Label(k), Expr(v))))
            }
            UnionMap(map) => ser.collect_map(
                map.iter().map(|(k, v)| (Label(k), v.as_ref().map(Expr))),
            ),
        }
    }
}

fn collect_nested_applications<'a>(e: &'a Expr) -> (&'a Expr, Vec<&'a Expr>) {
    fn go<'a>(e: &'a Expr, vec: &mut Vec<&'a Expr>) -> &'a Expr {
        match e.as_ref() {
            ExprKind::Op(OpKind::App(f, a)) => {
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

type LetBinding<'a> = (&'a Label, &'a Option<Expr>, &'a Expr);

fn collect_nested_lets<'a>(e: &'a Expr) -> (&'a Expr, Vec<LetBinding<'a>>) {
    fn go<'a>(e: &'a Expr, vec: &mut Vec<LetBinding<'a>>) -> &'a Expr {
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
