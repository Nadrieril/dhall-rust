use std::iter::FromIterator;

use crate::syntax::*;

fn vec<'a, T, U, Err>(
    x: &'a [T],
    f: impl FnMut(&'a T) -> Result<U, Err>,
) -> Result<Vec<U>, Err> {
    x.iter().map(f).collect()
}

fn opt<'a, T, U, Err>(
    x: &'a Option<T>,
    f: impl FnOnce(&'a T) -> Result<U, Err>,
) -> Result<Option<U>, Err> {
    Ok(match x {
        Some(x) => Some(f(x)?),
        None => None,
    })
}

fn dupmap<'a, SE1, SE2, T, Err>(
    x: impl IntoIterator<Item = (&'a Label, &'a SE1)>,
    mut f: impl FnMut(&'a SE1) -> Result<SE2, Err>,
) -> Result<T, Err>
where
    SE1: 'a,
    T: FromIterator<(Label, SE2)>,
{
    x.into_iter().map(|(k, x)| Ok((k.clone(), f(x)?))).collect()
}

fn optdupmap<'a, SE1, SE2, T, Err>(
    x: impl IntoIterator<Item = (&'a Label, &'a Option<SE1>)>,
    mut f: impl FnMut(&'a SE1) -> Result<SE2, Err>,
) -> Result<T, Err>
where
    SE1: 'a,
    T: FromIterator<(Label, Option<SE2>)>,
{
    x.into_iter()
        .map(|(k, x)| {
            Ok((
                k.clone(),
                match x {
                    Some(x) => Some(f(x)?),
                    None => None,
                },
            ))
        })
        .collect()
}

pub fn visit_ref<'a, F, SE1, SE2, Err>(
    input: &'a ExprKind<SE1>,
    mut f: F,
) -> Result<ExprKind<SE2>, Err>
where
    F: FnMut(Option<&'a Label>, &'a SE1) -> Result<SE2, Err>,
{
    // Can't use closures because of borrowing rules
    macro_rules! expr {
        ($e:expr) => {
            f(None, $e)
        };
        ($l:expr, $e:expr) => {
            f(Some($l), $e)
        };
    }

    use crate::syntax::ExprKind::*;
    Ok(match input {
        Var(v) => Var(v.clone()),
        Lam(l, t, e) => {
            let t = expr!(t)?;
            let e = expr!(l, e)?;
            Lam(l.clone(), t, e)
        }
        Pi(l, t, e) => {
            let t = expr!(t)?;
            let e = expr!(l, e)?;
            Pi(l.clone(), t, e)
        }
        Let(l, t, a, e) => {
            let t = opt(t, &mut |e| expr!(e))?;
            let a = expr!(a)?;
            let e = expr!(l, e)?;
            Let(l.clone(), t, a, e)
        }
        App(f, a) => App(expr!(f)?, expr!(a)?),
        Annot(x, t) => Annot(expr!(x)?, expr!(t)?),
        Const(k) => Const(*k),
        Builtin(v) => Builtin(*v),
        Num(n) => Num(n.clone()),
        TextLit(t) => TextLit(t.traverse_ref(|e| expr!(e))?),
        BinOp(o, x, y) => BinOp(*o, expr!(x)?, expr!(y)?),
        BoolIf(b, t, f) => BoolIf(expr!(b)?, expr!(t)?, expr!(f)?),
        EmptyListLit(t) => EmptyListLit(expr!(t)?),
        NEListLit(es) => NEListLit(vec(es, |e| expr!(e))?),
        SomeLit(e) => SomeLit(expr!(e)?),
        RecordType(kts) => RecordType(dupmap(kts, |e| expr!(e))?),
        RecordLit(kvs) => RecordLit(dupmap(kvs, |e| expr!(e))?),
        UnionType(kts) => UnionType(optdupmap(kts, |e| expr!(e))?),
        Merge(x, y, t) => Merge(expr!(x)?, expr!(y)?, opt(t, |e| expr!(e))?),
        ToMap(x, t) => ToMap(expr!(x)?, opt(t, |e| expr!(e))?),
        Field(e, l) => Field(expr!(e)?, l.clone()),
        Projection(e, ls) => Projection(expr!(e)?, ls.clone()),
        ProjectionByExpr(e, x) => ProjectionByExpr(expr!(e)?, expr!(x)?),
        Completion(e, x) => Completion(expr!(e)?, expr!(x)?),
        Assert(e) => Assert(expr!(e)?),
        Import(i) => Import(i.traverse_ref(|e| expr!(e))?),
    })
}
