use crate::*;
use std::iter::FromIterator;

/// A way too generic Visitor trait.
pub trait GenericVisitor<Input, Output>: Sized {
    fn visit(self, input: Input) -> Output;
}

/// A visitor trait that can be used to traverse `ExprF`s. We need this pattern so that Rust lets
/// us have as much mutability as we can.
/// For example, `traverse_ref_with_special_handling_of_binders` cannot be made using only
/// `traverse_ref`, because `traverse_ref` takes a `FnMut` so we would need to pass multiple
/// mutable reverences to this argument to `traverse_ref`. But Rust's ownership system is all about
/// preventing exactly this ! So we have to be more clever. The visitor pattern allows us to have
/// only one mutable thing the whole time: the visitor itself. The visitor can then carry around
/// multiple closures or just one, and Rust is ok with either. See for example TraverseRefVisitor.
pub trait ExprFFallibleVisitor<'a, SE1, SE2, E1, E2>: Sized {
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
}

/// Like ExprFFallibleVisitor, but without the error handling.
pub trait ExprFInFallibleVisitor<'a, SE1, SE2, E1, E2>: Sized {
    fn visit_subexpr(&mut self, subexpr: &'a SE1) -> SE2;
    fn visit_embed(self, embed: &'a E1) -> E2;

    fn visit_subexpr_under_binder(
        mut self,
        _label: &'a Label,
        subexpr: &'a SE1,
    ) -> SE2 {
        self.visit_subexpr(subexpr)
    }
}

impl<'a, T, SE1, SE2, E1, E2>
    GenericVisitor<&'a ExprF<SE1, E1>, Result<ExprF<SE2, E2>, T::Error>> for T
where
    T: ExprFFallibleVisitor<'a, SE1, SE2, E1, E2>,
{
    fn visit(
        self,
        input: &'a ExprF<SE1, E1>,
    ) -> Result<ExprF<SE2, E2>, T::Error> {
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
            V: ExprFFallibleVisitor<'a, SE1, SE2, E1, E2>,
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
            V: ExprFFallibleVisitor<'a, SE1, SE2, E1, E2>,
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

        let mut v = self;
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
            BinOp(o, x, y) => {
                BinOp(*o, v.visit_subexpr(x)?, v.visit_subexpr(y)?)
            }
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
            Field(e, l) => Field(v.visit_subexpr(e)?, l.clone()),
            Projection(e, ls) => Projection(v.visit_subexpr(e)?, ls.clone()),
            Assert(e) => Assert(v.visit_subexpr(e)?),
            Import(i) => Import(i.visit_subexpr(|e| v.visit_subexpr(e))?),
            Embed(a) => Embed(v.visit_embed(a)?),
        })
    }
}

impl<'a, T, SE1, SE2, E1, E2> GenericVisitor<&'a ExprF<SE1, E1>, ExprF<SE2, E2>>
    for T
where
    T: ExprFInFallibleVisitor<'a, SE1, SE2, E1, E2>,
{
    fn visit(self, input: &'a ExprF<SE1, E1>) -> ExprF<SE2, E2> {
        trivial_result(InfallibleWrapper(self).visit(input))
    }
}

struct InfallibleWrapper<T>(T);

impl<'a, T, SE1, SE2, E1, E2> ExprFFallibleVisitor<'a, SE1, SE2, E1, E2>
    for InfallibleWrapper<T>
where
    T: ExprFInFallibleVisitor<'a, SE1, SE2, E1, E2>,
{
    type Error = Void;

    fn visit_subexpr(&mut self, subexpr: &'a SE1) -> Result<SE2, Self::Error> {
        Ok(self.0.visit_subexpr(subexpr))
    }
    fn visit_embed(self, embed: &'a E1) -> Result<E2, Self::Error> {
        Ok(self.0.visit_embed(embed))
    }

    fn visit_subexpr_under_binder(
        self,
        label: &'a Label,
        subexpr: &'a SE1,
    ) -> Result<SE2, Self::Error> {
        Ok(self.0.visit_subexpr_under_binder(label, subexpr))
    }
}

pub struct TraverseRefWithBindersVisitor<F1, F2> {
    pub visit_subexpr: F1,
    pub visit_under_binder: F2,
}

impl<'a, SE, E, SE2, Err, F1, F2> ExprFFallibleVisitor<'a, SE, SE2, E, E>
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

impl<'a, SE, E, SE2, Err, F1> ExprFFallibleVisitor<'a, SE, SE2, E, E>
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

pub struct ResolveVisitor<F1>(pub F1);

impl<'a, 'b, E, E2, Err, F1>
    ExprFFallibleVisitor<'a, SubExpr<E>, SubExpr<E2>, E, E2>
    for &'b mut ResolveVisitor<F1>
where
    F1: FnMut(&Import<SubExpr<E2>>) -> Result<E2, Err>,
{
    type Error = Err;

    fn visit_subexpr(
        &mut self,
        subexpr: &'a SubExpr<E>,
    ) -> Result<SubExpr<E2>, Self::Error> {
        Ok(subexpr.rewrap(
            subexpr
                .as_ref()
                .traverse_resolve_with_visitor(&mut **self)?,
        ))
    }
    fn visit_embed(self, _embed: &'a E) -> Result<E2, Self::Error> {
        unimplemented!()
    }
}
