use itertools::Itertools;
use std::iter::FromIterator;

use crate::syntax::*;

fn opt<'a, T, U, Err>(
    x: &'a Option<T>,
    f: impl FnOnce(&'a T) -> Result<U, Err>,
) -> Result<Option<U>, Err> {
    x.as_ref().map(f).transpose()
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

pub fn visit_ref<'a, F, SE1, SE2, Err>(
    input: &'a ExprKind<SE1>,
    mut f: F,
) -> Result<ExprKind<SE2>, Err>
where
    F: FnMut(Option<&'a Label>, &'a SE1) -> Result<SE2, Err>,
{
    // Can't use closures because of borrowing rules
    macro_rules! expr {
        () => {
            |e| Ok(expr!(e))
        };
        ($e:expr) => {
            f(None, $e)?
        };
        ($l:expr, $e:expr) => {
            f(Some($l), $e)?
        };
    }
    macro_rules! opt {
        () => {
            |e| Ok(opt!(e))
        };
        ($e:expr) => {
            opt($e, |e| Ok(expr!(e)))?
        };
    }

    use crate::syntax::ExprKind::*;
    Ok(match input {
        Var(v) => Var(v.clone()),
        Lam(l, t, e) => Lam(l.clone(), expr!(t), expr!(l, e)),
        Pi(l, t, e) => Pi(l.clone(), expr!(t), expr!(l, e)),
        Let(l, t, a, e) => Let(l.clone(), opt!(t), expr!(a), expr!(l, e)),
        Const(k) => Const(*k),
        Num(n) => Num(n.clone()),
        Builtin(v) => Builtin(*v),
        TextLit(t) => TextLit(t.traverse_ref(expr!())?),
        SomeLit(e) => SomeLit(expr!(e)),
        EmptyListLit(t) => EmptyListLit(expr!(t)),
        NEListLit(es) => NEListLit(es.iter().map(expr!()).try_collect()?),
        RecordType(kts) => RecordType(dupmap(kts, expr!())?),
        RecordLit(kvs) => RecordLit(dupmap(kvs, expr!())?),
        UnionType(kts) => UnionType(dupmap(kts, opt!())?),
        Op(op) => Op(op.traverse_ref(expr!())?),
        Annot(x, t) => Annot(expr!(x), expr!(t)),
        Assert(e) => Assert(expr!(e)),
        Import(i) => Import(i.traverse_ref(expr!())?),
    })
}
