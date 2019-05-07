use std::collections::BTreeMap;

use crate::*;

/// A way too generic Visitor trait.
pub trait GenericVisitor<Input, Return>: Sized {
    fn visit(self, input: Input) -> Return;
}

/// A visitor trait that can be used to traverse `ExprF`s. We need this pattern
/// so that Rust lets us have as much mutability as we can.
/// For example, `traverse_embed` cannot be made using only `traverse_ref`, because
/// `traverse_ref` takes a `FnMut` so we would need to pass multiple mutable
/// reverences to this argument to `traverse_ref`. But Rust's ownership system
/// is all about preventing exactly this ! So we have to be more clever.
/// The visitor pattern allows us to have only one mutable thing the whole
/// time: the visitor itself. The visitor can then carry around multiple closures
/// or just one, and Rust is ok with either. See for example TraverseRefVisitor
/// and TraverseEmbedVisitor.
/// This is very generic. For a more legible trait, see ExprFInFallibleVisitor
pub trait ExprFVeryGenericVisitor<'a, Ret, SE1, L1, E1>: Sized {
    type Error;
    type SE2;
    type L2;
    type E2;

    fn visit_subexpr(
        &mut self,
        subexpr: &'a SE1,
    ) -> Result<Self::SE2, Self::Error>;
    fn visit_label(&mut self, label: &'a L1) -> Result<Self::L2, Self::Error>;

    fn visit_binder(
        self,
        label: &'a L1,
        subexpr: &'a SE1,
    ) -> Result<(Self::L2, Self::SE2), Self::Error>;

    fn visit_embed_squash(self, embed: &'a E1) -> Result<Ret, Self::Error>;

    // Called with the result of the map, in the non-embed case.
    // Useful to change the result type, and/or avoid some loss of info
    fn visit_resulting_exprf(
        result: ExprF<Self::SE2, Self::L2, Self::E2>,
    ) -> Result<Ret, Self::Error>;
}

impl<'a, T, Ret, SE1, L1, E1>
    GenericVisitor<&'a ExprF<SE1, L1, E1>, Result<Ret, T::Error>> for T
where
    L1: Ord,
    T::L2: Ord,
    T: ExprFVeryGenericVisitor<'a, Ret, SE1, L1, E1>,
{
    fn visit(self, input: &'a ExprF<SE1, L1, E1>) -> Result<Ret, T::Error> {
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
        fn btmap<'a, V, Ret, SE, L, E>(
            x: &'a BTreeMap<L, SE>,
            mut v: V,
        ) -> Result<BTreeMap<V::L2, V::SE2>, V::Error>
        where
            L: Ord,
            V::L2: Ord,
            V: ExprFVeryGenericVisitor<'a, Ret, SE, L, E>,
        {
            x.iter()
                .map(|(k, x)| Ok((v.visit_label(k)?, v.visit_subexpr(x)?)))
                .collect()
        }
        fn btoptmap<'a, V, Ret, SE, L, E>(
            x: &'a BTreeMap<L, Option<SE>>,
            mut v: V,
        ) -> Result<BTreeMap<V::L2, Option<V::SE2>>, V::Error>
        where
            L: Ord,
            V::L2: Ord,
            V: ExprFVeryGenericVisitor<'a, Ret, SE, L, E>,
        {
            x.iter()
                .map(|(k, x)| {
                    Ok((
                        v.visit_label(k)?,
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
        T::visit_resulting_exprf(match input {
            Var(V(l, n)) => Var(V(v.visit_label(l)?, *n)),
            Lam(l, t, e) => {
                let t = v.visit_subexpr(t)?;
                let (l, e) = v.visit_binder(l, e)?;
                Lam(l, t, e)
            }
            Pi(l, t, e) => {
                let t = v.visit_subexpr(t)?;
                let (l, e) = v.visit_binder(l, e)?;
                Pi(l, t, e)
            }
            Let(l, t, a, e) => {
                let t = opt(t, &mut |e| v.visit_subexpr(e))?;
                let a = v.visit_subexpr(a)?;
                let (l, e) = v.visit_binder(l, e)?;
                Let(l, t, a, e)
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
            OldOptionalLit(x, t) => OldOptionalLit(
                opt(x, |e| v.visit_subexpr(e))?,
                v.visit_subexpr(t)?,
            ),
            SomeLit(e) => SomeLit(v.visit_subexpr(e)?),
            RecordType(kts) => RecordType(btmap(kts, v)?),
            RecordLit(kvs) => RecordLit(btmap(kvs, v)?),
            UnionType(kts) => UnionType(btoptmap(kts, v)?),
            UnionLit(k, x, kts) => UnionLit(
                v.visit_label(k)?,
                v.visit_subexpr(x)?,
                btoptmap(kts, v)?,
            ),
            Merge(x, y, t) => Merge(
                v.visit_subexpr(x)?,
                v.visit_subexpr(y)?,
                opt(t, |e| v.visit_subexpr(e))?,
            ),
            Field(e, l) => Field(v.visit_subexpr(e)?, v.visit_label(l)?),
            Projection(e, ls) => {
                Projection(v.visit_subexpr(e)?, vec(ls, |l| v.visit_label(l))?)
            }
            Embed(a) => return v.visit_embed_squash(a),
        })
    }
}

/// Like ExprFVeryGenericVisitor, but sets the return
/// type to ExprF<_>
pub trait ExprFFallibleVisitor<'a, SE1, SE2, L1, L2, E1, E2>: Sized {
    type Error;

    fn visit_subexpr(&mut self, subexpr: &'a SE1) -> Result<SE2, Self::Error>;
    fn visit_label(&mut self, label: &'a L1) -> Result<L2, Self::Error>;
    fn visit_embed(self, embed: &'a E1) -> Result<E2, Self::Error>;

    fn visit_subexpr_under_binder(
        mut self,
        _label: &'a L1,
        subexpr: &'a SE1,
    ) -> Result<SE2, Self::Error> {
        self.visit_subexpr(subexpr)
    }

    fn visit_binder(
        mut self,
        label: &'a L1,
        subexpr: &'a SE1,
    ) -> Result<(L2, SE2), Self::Error> {
        Ok((
            self.visit_label(label)?,
            self.visit_subexpr_under_binder(label, subexpr)?,
        ))
    }

    fn visit_embed_squash(
        self,
        embed: &'a E1,
    ) -> Result<ExprF<SE2, L2, E2>, Self::Error> {
        Ok(ExprF::Embed(self.visit_embed(embed)?))
    }
}

impl<'a, T, SE1, SE2, L1, L2, E1, E2>
    ExprFVeryGenericVisitor<'a, ExprF<SE2, L2, E2>, SE1, L1, E1> for T
where
    T: ExprFFallibleVisitor<'a, SE1, SE2, L1, L2, E1, E2>,
{
    type Error = T::Error;
    type SE2 = SE2;
    type L2 = L2;
    type E2 = E2;

    fn visit_subexpr(
        &mut self,
        subexpr: &'a SE1,
    ) -> Result<Self::SE2, Self::Error> {
        self.visit_subexpr(subexpr)
    }

    fn visit_label(&mut self, label: &'a L1) -> Result<Self::L2, Self::Error> {
        self.visit_label(label)
    }

    fn visit_binder(
        self,
        label: &'a L1,
        subexpr: &'a SE1,
    ) -> Result<(Self::L2, Self::SE2), Self::Error> {
        self.visit_binder(label, subexpr)
    }

    fn visit_embed_squash(
        self,
        embed: &'a E1,
    ) -> Result<ExprF<SE2, L2, E2>, Self::Error> {
        self.visit_embed_squash(embed)
    }

    // Called with the result of the map, in the non-embed case.
    // Useful to change the result type, and/or avoid some loss of info
    fn visit_resulting_exprf(
        result: ExprF<Self::SE2, Self::L2, Self::E2>,
    ) -> Result<ExprF<SE2, L2, E2>, Self::Error> {
        Ok(result)
    }
}

/// Like ExprFFallibleVisitor, but without the error handling.
pub trait ExprFInFallibleVisitor<'a, SE1, SE2, L1, L2, E1, E2>: Sized {
    fn visit_subexpr(&mut self, subexpr: &'a SE1) -> SE2;
    fn visit_label(&mut self, label: &'a L1) -> L2;
    fn visit_embed(self, embed: &'a E1) -> E2;

    fn visit_subexpr_under_binder(
        mut self,
        _label: &'a L1,
        subexpr: &'a SE1,
    ) -> SE2 {
        self.visit_subexpr(subexpr)
    }

    fn visit_binder(mut self, label: &'a L1, subexpr: &'a SE1) -> (L2, SE2) {
        (
            self.visit_label(label),
            self.visit_subexpr_under_binder(label, subexpr),
        )
    }

    fn visit_embed_squash(self, embed: &'a E1) -> ExprF<SE2, L2, E2> {
        ExprF::Embed(self.visit_embed(embed))
    }
}

struct InfallibleWrapper<T>(T);

impl<'a, T, SE1, SE2, L1, L2, E1, E2>
    ExprFFallibleVisitor<'a, SE1, SE2, L1, L2, E1, E2> for InfallibleWrapper<T>
where
    T: ExprFInFallibleVisitor<'a, SE1, SE2, L1, L2, E1, E2>,
{
    type Error = X;

    fn visit_subexpr(&mut self, subexpr: &'a SE1) -> Result<SE2, Self::Error> {
        Ok(self.0.visit_subexpr(subexpr))
    }
    fn visit_label(&mut self, label: &'a L1) -> Result<L2, Self::Error> {
        Ok(self.0.visit_label(label))
    }
    fn visit_embed(self, embed: &'a E1) -> Result<E2, Self::Error> {
        Ok(self.0.visit_embed(embed))
    }

    fn visit_binder(
        self,
        label: &'a L1,
        subexpr: &'a SE1,
    ) -> Result<(L2, SE2), Self::Error> {
        Ok(self.0.visit_binder(label, subexpr))
    }

    fn visit_embed_squash(
        self,
        embed: &'a E1,
    ) -> Result<ExprF<SE2, L2, E2>, Self::Error> {
        Ok(self.0.visit_embed_squash(embed))
    }
}

impl<'a, T, SE1, SE2, L1, L2, E1, E2>
    GenericVisitor<&'a ExprF<SE1, L1, E1>, ExprF<SE2, L2, E2>> for T
where
    L1: Ord,
    L2: Ord,
    T: ExprFInFallibleVisitor<'a, SE1, SE2, L1, L2, E1, E2>,
{
    fn visit(self, input: &'a ExprF<SE1, L1, E1>) -> ExprF<SE2, L2, E2> {
        trivial_result(InfallibleWrapper(self).visit(input))
    }
}

pub struct TraverseRefWithBindersVisitor<F1, F2, F4, F5> {
    pub visit_subexpr: F1,
    pub visit_under_binder: F2,
    pub visit_embed: F4,
    pub visit_label: F5,
}

impl<'a, SE, L, E, SE2, L2, E2, Err, F1, F2, F4, F5>
    ExprFFallibleVisitor<'a, SE, SE2, L, L2, E, E2>
    for TraverseRefWithBindersVisitor<F1, F2, F4, F5>
where
    SE: 'a,
    L: 'a,
    E: 'a,
    L: Ord,
    L2: Ord,
    F1: FnMut(&'a SE) -> Result<SE2, Err>,
    F2: FnOnce(&'a L, &'a SE) -> Result<SE2, Err>,
    F4: FnOnce(&'a E) -> Result<E2, Err>,
    F5: FnMut(&'a L) -> Result<L2, Err>,
{
    type Error = Err;

    fn visit_subexpr(&mut self, subexpr: &'a SE) -> Result<SE2, Self::Error> {
        (self.visit_subexpr)(subexpr)
    }
    fn visit_subexpr_under_binder(
        self,
        label: &'a L,
        subexpr: &'a SE,
    ) -> Result<SE2, Self::Error> {
        (self.visit_under_binder)(label, subexpr)
    }
    fn visit_embed(self, embed: &'a E) -> Result<E2, Self::Error> {
        (self.visit_embed)(embed)
    }
    fn visit_label(&mut self, label: &'a L) -> Result<L2, Self::Error> {
        (self.visit_label)(label)
    }
}

pub struct TraverseRefVisitor<F1, F3, F4> {
    pub visit_subexpr: F1,
    pub visit_embed: F3,
    pub visit_label: F4,
}

impl<'a, SE, L, E, SE2, L2, E2, Err, F1, F3, F4>
    ExprFFallibleVisitor<'a, SE, SE2, L, L2, E, E2>
    for TraverseRefVisitor<F1, F3, F4>
where
    SE: 'a,
    L: 'a,
    E: 'a,
    L: Ord,
    L2: Ord,
    F1: FnMut(&'a SE) -> Result<SE2, Err>,
    F3: FnOnce(&'a E) -> Result<E2, Err>,
    F4: FnMut(&'a L) -> Result<L2, Err>,
{
    type Error = Err;

    fn visit_subexpr(&mut self, subexpr: &'a SE) -> Result<SE2, Self::Error> {
        (self.visit_subexpr)(subexpr)
    }
    fn visit_embed(self, embed: &'a E) -> Result<E2, Self::Error> {
        (self.visit_embed)(embed)
    }
    fn visit_label(&mut self, label: &'a L) -> Result<L2, Self::Error> {
        (self.visit_label)(label)
    }
}

pub struct TraverseEmbedVisitor<F1>(pub F1);

impl<'a, 'b, N, E, E2, Err, F1>
    ExprFFallibleVisitor<'a, SubExpr<N, E>, SubExpr<N, E2>, Label, Label, E, E2>
    for &'b mut TraverseEmbedVisitor<F1>
where
    N: Clone + 'a,
    F1: FnMut(&E) -> Result<E2, Err>,
{
    type Error = Err;

    fn visit_subexpr(
        &mut self,
        subexpr: &'a SubExpr<N, E>,
    ) -> Result<SubExpr<N, E2>, Self::Error> {
        Ok(subexpr.rewrap(subexpr.as_ref().visit(&mut **self)?))
    }
    fn visit_embed(self, embed: &'a E) -> Result<E2, Self::Error> {
        (self.0)(embed)
    }
    fn visit_label(&mut self, label: &'a Label) -> Result<Label, Self::Error> {
        Ok(Label::clone(label))
    }
}

pub struct NoteAbsurdVisitor;

impl<'a, 'b, N, E>
    ExprFInFallibleVisitor<'a, SubExpr<X, E>, SubExpr<N, E>, Label, Label, E, E>
    for &'b mut NoteAbsurdVisitor
where
    E: Clone + 'a,
{
    fn visit_subexpr(&mut self, subexpr: &'a SubExpr<X, E>) -> SubExpr<N, E> {
        SubExpr::from_expr_no_note(subexpr.as_ref().visit(&mut **self))
    }
    fn visit_embed(self, embed: &'a E) -> E {
        E::clone(embed)
    }
    fn visit_label(&mut self, label: &'a Label) -> Label {
        Label::clone(label)
    }
}

pub struct AbsurdVisitor;

impl<'a, 'b, N, E>
    ExprFInFallibleVisitor<'a, SubExpr<X, X>, SubExpr<N, E>, Label, Label, X, E>
    for &'b mut AbsurdVisitor
{
    fn visit_subexpr(&mut self, subexpr: &'a SubExpr<X, X>) -> SubExpr<N, E> {
        SubExpr::from_expr_no_note(subexpr.as_ref().visit(&mut **self))
    }
    fn visit_embed(self, embed: &'a X) -> E {
        match *embed {}
    }
    fn visit_label(&mut self, label: &'a Label) -> Label {
        Label::clone(label)
    }
}
