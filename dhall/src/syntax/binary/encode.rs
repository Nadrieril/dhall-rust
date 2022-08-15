use std::vec;

use crate::builtins::Builtin;
use crate::error::EncodeError;
use crate::operations::{BinOp, OpKind};
use crate::syntax::{
    self, Expr, ExprKind, FilePrefix, Hash, ImportMode, ImportTarget,
    InterpolatedTextContents, Label, NaiveDouble, Scheme, V,
};

pub fn encode(expr: &Expr) -> Result<Vec<u8>, EncodeError> {
    minicbor::to_vec(expr).map_err(EncodeError::CBORError)
}

impl minicbor::Encode<()> for Label {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut minicbor::Encoder<W>,
        ctx: &mut (),
    ) -> Result<(), minicbor::encode::Error<W::Error>> {
        self.as_ref().encode(e, ctx)
    }
}
impl minicbor::Encode<()> for InterpolatedTextContents<&Expr> {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut minicbor::Encoder<W>,
        ctx: &mut (),
    ) -> Result<(), minicbor::encode::Error<W::Error>> {
        match self {
            Self::Expr(x) => x.encode(e, ctx),
            Self::Text(x) => x.encode(e, ctx),
        }
    }
}

impl minicbor::Encode<()> for NaiveDouble {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut minicbor::Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), minicbor::encode::Error<W::Error>> {
        let d: f64 = (*self).into();
        if d.is_nan() || d == half::f16::from_f64(d).to_f64() {
            e.f16(d as f32)?;
        } else if d == d as f32 as f64 {
            e.f32(d as f32)?;
        } else {
            e.f64(d)?;
        }
        Ok(())
    }
}

impl minicbor::Encode<()> for BinOp {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut minicbor::Encoder<W>,
        ctx: &mut (),
    ) -> Result<(), minicbor::encode::Error<W::Error>> {
        use self::BinOp::*;
        let op: u64 = match self {
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
        op.encode(e, ctx)
    }
}

impl minicbor::Encode<()> for Hash {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut minicbor::Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), minicbor::encode::Error<W::Error>> {
        let Hash::SHA256(h) = self;
        let mut bytes = vec![18, 32];
        bytes.extend_from_slice(h);
        e.bytes(&bytes)?;
        Ok(())
    }
}

impl minicbor::Encode<()> for ImportMode {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut minicbor::Encoder<W>,
        ctx: &mut (),
    ) -> Result<(), minicbor::encode::Error<W::Error>> {
        let mode: u64 = match self {
            ImportMode::Code => 0,
            ImportMode::RawText => 1,
            ImportMode::Location => 2,
        };
        mode.encode(e, ctx)
    }
}

impl minicbor::Encode<()> for Expr {
    fn encode<W: minicbor::encode::Write>(
        &self,
        enc: &mut minicbor::Encoder<W>,
        ctx: &mut (),
    ) -> Result<(), minicbor::encode::Error<W::Error>> {
        use syntax::ExprKind::*;
        use syntax::NumKind::*;
        use OpKind::*;

        let null = None::<()>;

        match self.as_ref() {
            Const(c) => c.to_string().encode(enc, ctx)?,
            Builtin(b) => b.to_string().encode(enc, ctx)?,
            Num(Bool(b)) => b.encode(enc, ctx)?,
            Num(Natural(n)) => (15u64, n).encode(enc, ctx)?,
            Num(Integer(n)) => (16u64, n).encode(enc, ctx)?,
            Num(Double(n)) => n.encode(enc, ctx)?,
            Op(BoolIf(x, y, z)) => (14u64, x, y, z).encode(enc, ctx)?,
            Var(V(l, n)) if l.as_ref() == "_" => {
                (*n as u64).encode(enc, ctx)?
            }
            Var(V(l, n)) => {
                (l, *n as u64).encode(enc, ctx)?;
            }
            Lam(l, x, y) if l.as_ref() == "_" => {
                (1u64, x, y).encode(enc, ctx)?
            }
            Lam(l, x, y) => (1u64, l, x, y).encode(enc, ctx)?,
            Pi(l, x, y) if l.as_ref() == "_" => {
                (2u64, x, y).encode(enc, ctx)?
            }
            Pi(l, x, y) => (2u64, l, x, y).encode(enc, ctx)?,
            Let(_, _, _, _) => {
                let (bound_e, bindings) = collect_nested_lets(self);
                let len = 1 + 3 * bindings.len() as u64 + 1;
                enc.array(len)?;
                25u64.encode(enc, ctx)?;
                for (l, t, v) in bindings {
                    l.encode(enc, ctx)?;
                    t.encode(enc, ctx)?;
                    v.encode(enc, ctx)?;
                }
                bound_e.encode(enc, ctx)?;
            }
            Op(App(_, _)) => {
                let (f, args) = collect_nested_applications(self);
                enc.array(1 + 1 + args.len() as u64)?;
                0u64.encode(enc, ctx)?;
                f.encode(enc, ctx)?;
                for arg in args.into_iter().rev() {
                    arg.encode(enc, ctx)?;
                }
            }
            Annot(x, y) => (26u64, x, y).encode(enc, ctx)?,
            Assert(x) => (19u64, x).encode(enc, ctx)?,
            SomeLit(x) => (5u64, null, x).encode(enc, ctx)?,
            EmptyListLit(x) => match x.as_ref() {
                Op(App(f, a))
                    if matches!(
                        f.as_ref(),
                        ExprKind::Builtin(self::Builtin::List)
                    ) =>
                {
                    (4u64, a).encode(enc, ctx)?
                }
                _ => (28u64, x).encode(enc, ctx)?,
            },
            NEListLit(xs) => {
                enc.array(2 + xs.len() as u64)?;
                4u64.encode(enc, ctx)?;
                null.encode(enc, ctx)?;
                for x in xs {
                    x.encode(enc, ctx)?;
                }
            }
            TextLit(xs) => {
                enc.array(1 + xs.len() as u64)?;
                18u64.encode(enc, ctx)?;
                for x in xs.iter() {
                    x.encode(enc, ctx)?;
                }
            }
            RecordType(map) => (7u64, map).encode(enc, ctx)?,
            RecordLit(map) => (8u64, map).encode(enc, ctx)?,
            UnionType(map) => (11u64, map).encode(enc, ctx)?,
            Op(Field(x, l)) => (9u64, x, l).encode(enc, ctx)?,
            Op(BinOp(op, x, y)) => (3u64, op, x, y).encode(enc, ctx)?,
            Op(Merge(x, y, None)) => (6u64, x, y).encode(enc, ctx)?,
            Op(Merge(x, y, Some(z))) => (6u64, x, y, z).encode(enc, ctx)?,
            Op(ToMap(x, None)) => (27u64, x).encode(enc, ctx)?,
            Op(ToMap(x, Some(y))) => (27u64, x, y).encode(enc, ctx)?,
            Op(Projection(x, ls)) => {
                enc.array(2 + ls.len() as u64)?;
                10u64.encode(enc, ctx)?;
                x.encode(enc, ctx)?;
                for l in ls {
                    l.encode(enc, ctx)?;
                }
            }
            Op(ProjectionByExpr(x, y)) => (10u64, x, (y,)).encode(enc, ctx)?,
            Op(Completion(x, y)) => (3u64, 13u64, x, y).encode(enc, ctx)?,
            Op(With(x, ls, y)) => (29u64, x, ls, y).encode(enc, ctx)?,
            Import(import) => {
                let count = 4 + match &import.location {
                    ImportTarget::Remote(url) => 3 + url.path.file_path.len(),
                    ImportTarget::Local(_, path) => path.file_path.len(),
                    ImportTarget::Env(_) => 1,
                    ImportTarget::Missing => 0,
                };
                enc.array(count as u64)?;

                24u64.encode(enc, ctx)?;
                import.hash.encode(enc, ctx)?;
                import.mode.encode(enc, ctx)?;

                let scheme: u64 = match &import.location {
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
                scheme.encode(enc, ctx)?;

                match &import.location {
                    ImportTarget::Remote(url) => {
                        url.headers.encode(enc, ctx)?;
                        url.authority.encode(enc, ctx)?;
                        for p in url.path.file_path.iter() {
                            p.encode(enc, ctx)?;
                        }
                        url.query.encode(enc, ctx)?;
                    }
                    ImportTarget::Local(_, path) => {
                        for p in path.file_path.iter() {
                            p.encode(enc, ctx)?;
                        }
                    }
                    ImportTarget::Env(env) => {
                        env.encode(enc, ctx)?;
                    }
                    ImportTarget::Missing => {}
                }
            }
        };
        Ok(())
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
