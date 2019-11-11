use crate::*;
use std::iter::FromIterator;

/// A visitor trait that can be used to traverse `ExprF`s. We need this pattern so that Rust lets
/// us have as much mutability as we can.
/// For example, `traverse_ref_with_special_handling_of_binders` cannot be made using only
/// `traverse_ref`, because `traverse_ref` takes a `FnMut` so we would need to pass multiple
/// mutable reverences to this argument to `traverse_ref`. But Rust's ownership system is all about
/// preventing exactly this ! So we have to be more clever. The visitor pattern allows us to have
/// only one mutable thing the whole time: the visitor itself. The visitor can then carry around
/// multiple closures or just one, and Rust is ok with either. See for example TraverseRefVisitor.
pub trait ExprFVisitor<'a, SE1, SE2, E1, E2>: Sized {
    type Error;

    fn visit_subexpr(&mut self, subexpr: &'a SE1) -> Result<SE2, Self::Error>;
    fn visit_embed(self, embed: &'a E1) -> Result<E2, Self::Error>;

    fn visit_subexpr_under_binder(
        mut self,
        _label: &'a Label,
        subexpr: &'a SE1,
    ) -> Result<SE2, Self::Error> {
        self.visit_subexpr(subexpr)
    }

    fn visit(
        self,
        input: &'a ExprF<SE1, E1>,
    ) -> Result<ExprF<SE2, E2>, Self::Error> {
        visit_ref(self, input)
    }
}

/// Like `ExprFVisitor`, but by mutable reference
pub trait ExprFMutVisitor<'a, SE, E>: Sized {
    type Error;

    fn visit_subexpr(&mut self, subexpr: &'a mut SE)
        -> Result<(), Self::Error>;
    fn visit_embed(self, _embed: &'a mut E) -> Result<(), Self::Error> {
        Ok(())
    }

    fn visit_subexpr_under_binder(
        mut self,
        _label: &'a mut Label,
        subexpr: &'a mut SE,
    ) -> Result<(), Self::Error> {
        self.visit_subexpr(subexpr)
    }

    fn visit(self, input: &'a mut ExprF<SE, E>) -> Result<(), Self::Error> {
        visit_mut(self, input)
    }
}

fn visit_ref<'a, V, SE1, SE2, E1, E2>(
    mut v: V,
    input: &'a ExprF<SE1, E1>,
) -> Result<ExprF<SE2, E2>, V::Error>
where
    V: ExprFVisitor<'a, SE1, SE2, E1, E2>,
{
    fn vec<'a, T, U, Err, F: FnMut(&'a T) -> Result<U, Err>>(
        x: &'a [T],
        f: F,
    ) -> Result<Vec<U>, Err> {
        x.iter().map(f).collect()
    }
    fn opt<'a, T, U, Err, F: FnOnce(&'a T) -> Result<U, Err>>(
        x: &'a Option<T>,
        f: F,
    ) -> Result<Option<U>, Err> {
        Ok(match x {
            Some(x) => Some(f(x)?),
            None => None,
        })
    }
    fn dupmap<'a, V, SE1, SE2, E1, E2, T>(
        x: impl IntoIterator<Item = (&'a Label, &'a SE1)>,
        mut v: V,
    ) -> Result<T, V::Error>
    where
        SE1: 'a,
        T: FromIterator<(Label, SE2)>,
        V: ExprFVisitor<'a, SE1, SE2, E1, E2>,
    {
        x.into_iter()
            .map(|(k, x)| Ok((k.clone(), v.visit_subexpr(x)?)))
            .collect()
    }
    fn optdupmap<'a, V, SE1, SE2, E1, E2, T>(
        x: impl IntoIterator<Item = (&'a Label, &'a Option<SE1>)>,
        mut v: V,
    ) -> Result<T, V::Error>
    where
        SE1: 'a,
        T: FromIterator<(Label, Option<SE2>)>,
        V: ExprFVisitor<'a, SE1, SE2, E1, E2>,
    {
        x.into_iter()
            .map(|(k, x)| {
                Ok((
                    k.clone(),
                    match x {
                        Some(x) => Some(v.visit_subexpr(x)?),
                        None => None,
                    },
                ))
            })
            .collect()
    }

    use crate::ExprF::*;
    Ok(match input {
        Var(v) => Var(v.clone()),
        Lam(l, t, e) => {
            let t = v.visit_subexpr(t)?;
            let e = v.visit_subexpr_under_binder(l, e)?;
            Lam(l.clone(), t, e)
        }
        Pi(l, t, e) => {
            let t = v.visit_subexpr(t)?;
            let e = v.visit_subexpr_under_binder(l, e)?;
            Pi(l.clone(), t, e)
        }
        Let(l, t, a, e) => {
            let t = opt(t, &mut |e| v.visit_subexpr(e))?;
            let a = v.visit_subexpr(a)?;
            let e = v.visit_subexpr_under_binder(l, e)?;
            Let(l.clone(), t, a, e)
        }
        App(f, a) => App(v.visit_subexpr(f)?, v.visit_subexpr(a)?),
        Annot(x, t) => Annot(v.visit_subexpr(x)?, v.visit_subexpr(t)?),
        Const(k) => Const(*k),
        Builtin(v) => Builtin(*v),
        BoolLit(b) => BoolLit(*b),
        NaturalLit(n) => NaturalLit(*n),
        IntegerLit(n) => IntegerLit(*n),
        DoubleLit(n) => DoubleLit(*n),
        TextLit(t) => TextLit(t.traverse_ref(|e| v.visit_subexpr(e))?),
        BinOp(o, x, y) => BinOp(*o, v.visit_subexpr(x)?, v.visit_subexpr(y)?),
        BoolIf(b, t, f) => BoolIf(
            v.visit_subexpr(b)?,
            v.visit_subexpr(t)?,
            v.visit_subexpr(f)?,
        ),
        EmptyListLit(t) => EmptyListLit(v.visit_subexpr(t)?),
        NEListLit(es) => NEListLit(vec(es, |e| v.visit_subexpr(e))?),
        SomeLit(e) => SomeLit(v.visit_subexpr(e)?),
        RecordType(kts) => RecordType(dupmap(kts, v)?),
        RecordLit(kvs) => RecordLit(dupmap(kvs, v)?),
        UnionType(kts) => UnionType(optdupmap(kts, v)?),
        Merge(x, y, t) => Merge(
            v.visit_subexpr(x)?,
            v.visit_subexpr(y)?,
            opt(t, |e| v.visit_subexpr(e))?,
        ),
        ToMap(x, t) => {
            ToMap(v.visit_subexpr(x)?, opt(t, |e| v.visit_subexpr(e))?)
        }
        Field(e, l) => Field(v.visit_subexpr(e)?, l.clone()),
        Projection(e, ls) => Projection(v.visit_subexpr(e)?, ls.clone()),
        ProjectionByExpr(e, x) => {
            ProjectionByExpr(v.visit_subexpr(e)?, v.visit_subexpr(x)?)
        }
        Assert(e) => Assert(v.visit_subexpr(e)?),
        Import(i) => Import(i.traverse_ref(|e| v.visit_subexpr(e))?),
        Embed(a) => Embed(v.visit_embed(a)?),
    })
}

fn visit_mut<'a, V, SE, E>(
    mut v: V,
    input: &'a mut ExprF<SE, E>,
) -> Result<(), V::Error>
where
    V: ExprFMutVisitor<'a, SE, E>,
{
    fn vec<'a, V, SE, E>(v: &mut V, x: &'a mut Vec<SE>) -> Result<(), V::Error>
    where
        V: ExprFMutVisitor<'a, SE, E>,
    {
        for x in x {
            v.visit_subexpr(x)?;
        }
        Ok(())
    }
    fn opt<'a, V, SE, E>(
        v: &mut V,
        x: &'a mut Option<SE>,
    ) -> Result<(), V::Error>
    where
        V: ExprFMutVisitor<'a, SE, E>,
    {
        if let Some(x) = x {
            v.visit_subexpr(x)?;
        }
        Ok(())
    }
    fn dupmap<'a, V, SE, E>(
        mut v: V,
        x: impl IntoIterator<Item = (&'a Label, &'a mut SE)>,
    ) -> Result<(), V::Error>
    where
        SE: 'a,
        V: ExprFMutVisitor<'a, SE, E>,
    {
        for (_, x) in x {
            v.visit_subexpr(x)?;
        }
        Ok(())
    }
    fn optdupmap<'a, V, SE, E>(
        mut v: V,
        x: impl IntoIterator<Item = (&'a Label, &'a mut Option<SE>)>,
    ) -> Result<(), V::Error>
    where
        SE: 'a,
        V: ExprFMutVisitor<'a, SE, E>,
    {
        for (_, x) in x {
            opt(&mut v, x)?;
        }
        Ok(())
    }

    use crate::ExprF::*;
    match input {
        Var(_) | Const(_) | Builtin(_) | BoolLit(_) | NaturalLit(_)
        | IntegerLit(_) | DoubleLit(_) => {}
        Lam(l, t, e) => {
            v.visit_subexpr(t)?;
            v.visit_subexpr_under_binder(l, e)?;
        }
        Pi(l, t, e) => {
            v.visit_subexpr(t)?;
            v.visit_subexpr_under_binder(l, e)?;
        }
        Let(l, t, a, e) => {
            opt(&mut v, t)?;
            v.visit_subexpr(a)?;
            v.visit_subexpr_under_binder(l, e)?;
        }
        App(f, a) => {
            v.visit_subexpr(f)?;
            v.visit_subexpr(a)?;
        }
        Annot(x, t) => {
            v.visit_subexpr(x)?;
            v.visit_subexpr(t)?;
        }
        TextLit(t) => t.traverse_mut(|e| v.visit_subexpr(e))?,
        BinOp(_, x, y) => {
            v.visit_subexpr(x)?;
            v.visit_subexpr(y)?;
        }
        BoolIf(b, t, f) => {
            v.visit_subexpr(b)?;
            v.visit_subexpr(t)?;
            v.visit_subexpr(f)?;
        }
        EmptyListLit(t) => v.visit_subexpr(t)?,
        NEListLit(es) => vec(&mut v, es)?,
        SomeLit(e) => v.visit_subexpr(e)?,
        RecordType(kts) => dupmap(v, kts)?,
        RecordLit(kvs) => dupmap(v, kvs)?,
        UnionType(kts) => optdupmap(v, kts)?,
        Merge(x, y, t) => {
            v.visit_subexpr(x)?;
            v.visit_subexpr(y)?;
            opt(&mut v, t)?;
        }
        ToMap(x, t) => {
            v.visit_subexpr(x)?;
            opt(&mut v, t)?;
        }
        Field(e, _) => v.visit_subexpr(e)?,
        Projection(e, _) => v.visit_subexpr(e)?,
        ProjectionByExpr(e, x) => {
            v.visit_subexpr(e)?;
            v.visit_subexpr(x)?;
        }
        Assert(e) => v.visit_subexpr(e)?,
        Import(i) => i.traverse_mut(|e| v.visit_subexpr(e))?,
        Embed(a) => v.visit_embed(a)?,
    }
    Ok(())
}

pub struct TraverseRefWithBindersVisitor<F1, F2> {
    pub visit_subexpr: F1,
    pub visit_under_binder: F2,
}

impl<'a, SE, E, SE2, Err, F1, F2> ExprFVisitor<'a, SE, SE2, E, E>
    for TraverseRefWithBindersVisitor<F1, F2>
where
    SE: 'a,
    E: 'a + Clone,
    F1: FnMut(&'a SE) -> Result<SE2, Err>,
    F2: FnOnce(&'a Label, &'a SE) -> Result<SE2, Err>,
{
    type Error = Err;

    fn visit_subexpr(&mut self, subexpr: &'a SE) -> Result<SE2, Self::Error> {
        (self.visit_subexpr)(subexpr)
    }
    fn visit_subexpr_under_binder(
        self,
        label: &'a Label,
        subexpr: &'a SE,
    ) -> Result<SE2, Self::Error> {
        (self.visit_under_binder)(label, subexpr)
    }
    fn visit_embed(self, embed: &'a E) -> Result<E, Self::Error> {
        Ok(embed.clone())
    }
}

pub struct TraverseRefVisitor<F1> {
    pub visit_subexpr: F1,
}

impl<'a, SE, E, SE2, Err, F1> ExprFVisitor<'a, SE, SE2, E, E>
    for TraverseRefVisitor<F1>
where
    SE: 'a,
    E: 'a + Clone,
    F1: FnMut(&'a SE) -> Result<SE2, Err>,
{
    type Error = Err;

    fn visit_subexpr(&mut self, subexpr: &'a SE) -> Result<SE2, Self::Error> {
        (self.visit_subexpr)(subexpr)
    }
    fn visit_embed(self, embed: &'a E) -> Result<E, Self::Error> {
        Ok(embed.clone())
    }
}

pub struct TraverseMutVisitor<F1> {
    pub visit_subexpr: F1,
}

impl<'a, SE, E, Err, F1> ExprFMutVisitor<'a, SE, E> for TraverseMutVisitor<F1>
where
    SE: 'a,
    E: 'a,
    F1: FnMut(&'a mut SE) -> Result<(), Err>,
{
    type Error = Err;

    fn visit_subexpr(
        &mut self,
        subexpr: &'a mut SE,
    ) -> Result<(), Self::Error> {
        (self.visit_subexpr)(subexpr)
    }
}
