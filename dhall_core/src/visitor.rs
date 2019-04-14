use std::collections::BTreeMap;

use crate::*;

pub trait ExprVisitor<'a, SE1, SE2, L1, L2, N1, N2, E1, E2>: Sized {
    type Error;

    fn visit_subexpr(&mut self, subexpr: &'a SE1) -> Result<SE2, Self::Error>;
    fn visit_label(&mut self, label: &'a L1) -> Result<L2, Self::Error>;
    fn visit_note(self, note: &'a N1) -> Result<N2, Self::Error>;
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
    ) -> Result<ExprF<SE2, L2, N2, E2>, Self::Error> {
        Ok(ExprF::Embed(self.visit_embed(embed)?))
    }

    fn visit_note_squash(
        mut self,
        note: &'a N1,
        subexpr: &'a SE1,
    ) -> Result<ExprF<SE2, L2, N2, E2>, Self::Error> {
        let subexpr = self.visit_subexpr(subexpr)?;
        let note = self.visit_note(note)?;
        Ok(ExprF::Note(note, subexpr))
    }
}

impl<SE, L, N, E> ExprF<SE, L, N, E> {
    pub fn visit<'a, V, SE2, L2, N2, E2>(
        &'a self,
        mut v: V,
    ) -> Result<ExprF<SE2, L2, N2, E2>, V::Error>
    where
        L: Ord,
        L2: Ord,
        V: ExprVisitor<'a, SE, SE2, L, L2, N, N2, E, E2>,
    {
        fn vec<'a, T, U, Err, F: FnMut(&'a T) -> Result<U, Err>>(
            x: &'a Vec<T>,
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
        fn btmap<'a, V, SE, L, N, E, SE2, L2, N2, E2>(
            x: &'a BTreeMap<L, SE>,
            mut v: V,
        ) -> Result<BTreeMap<L2, SE2>, V::Error>
        where
            L: Ord,
            L2: Ord,
            V: ExprVisitor<'a, SE, SE2, L, L2, N, N2, E, E2>,
        {
            x.into_iter()
                .map(|(k, x)| Ok((v.visit_label(k)?, v.visit_subexpr(x)?)))
                .collect()
        }

        use crate::ExprF::*;
        Ok(match self {
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
            App(f, args) => {
                App(v.visit_subexpr(f)?, vec(args, |e| v.visit_subexpr(e))?)
            }
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
            EmptyOptionalLit(t) => EmptyOptionalLit(v.visit_subexpr(t)?),
            NEOptionalLit(e) => NEOptionalLit(v.visit_subexpr(e)?),
            RecordType(kts) => RecordType(btmap(kts, v)?),
            RecordLit(kvs) => RecordLit(btmap(kvs, v)?),
            UnionType(kts) => UnionType(btmap(kts, v)?),
            UnionLit(k, x, kvs) => {
                UnionLit(v.visit_label(k)?, v.visit_subexpr(x)?, btmap(kvs, v)?)
            }
            Merge(x, y, t) => Merge(
                v.visit_subexpr(x)?,
                v.visit_subexpr(y)?,
                opt(t, |e| v.visit_subexpr(e))?,
            ),
            Field(e, l) => Field(v.visit_subexpr(e)?, v.visit_label(l)?),
            Projection(e, ls) => {
                Projection(v.visit_subexpr(e)?, vec(ls, |l| v.visit_label(l))?)
            }
            Note(n, e) => v.visit_note_squash(n, e)?,
            Embed(a) => v.visit_embed_squash(a)?,
        })
    }
}

pub struct TraverseRefVisitor<F1, F2, F3, F4, F5> {
    pub visit_subexpr: F1,
    pub visit_under_binder: F2,
    pub visit_note: F3,
    pub visit_embed: F4,
    pub visit_label: F5,
}

impl<'a, SE, L, N, E, SE2, L2, N2, E2, Err, F1, F2, F3, F4, F5>
    ExprVisitor<'a, SE, SE2, L, L2, N, N2, E, E2>
    for TraverseRefVisitor<F1, F2, F3, F4, F5>
where
    SE: 'a,
    L: 'a,
    N: 'a,
    E: 'a,
    L: Ord,
    L2: Ord,
    F1: FnMut(&'a SE) -> Result<SE2, Err>,
    F2: FnOnce(&'a L, &'a SE) -> Result<SE2, Err>,
    F3: FnOnce(&'a N) -> Result<N2, Err>,
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
    fn visit_note(self, note: &'a N) -> Result<N2, Self::Error> {
        (self.visit_note)(note)
    }
    fn visit_embed(self, embed: &'a E) -> Result<E2, Self::Error> {
        (self.visit_embed)(embed)
    }
    fn visit_label(&mut self, label: &'a L) -> Result<L2, Self::Error> {
        (self.visit_label)(label)
    }
}

pub struct TraverseRefSimpleVisitor<F1> {
    pub visit_subexpr: F1,
}

impl<'a, SE, L, N, E, SE2, Err, F1> ExprVisitor<'a, SE, SE2, L, L, N, N, E, E>
    for TraverseRefSimpleVisitor<F1>
where
    SE: 'a,
    L: Ord + Clone + 'a,
    N: Clone + 'a,
    E: Clone + 'a,
    F1: FnMut(&'a SE) -> Result<SE2, Err>,
{
    type Error = Err;

    fn visit_subexpr(&mut self, subexpr: &'a SE) -> Result<SE2, Self::Error> {
        (self.visit_subexpr)(subexpr)
    }
    fn visit_note(self, note: &'a N) -> Result<N, Self::Error> {
        Ok(N::clone(note))
    }
    fn visit_embed(self, embed: &'a E) -> Result<E, Self::Error> {
        Ok(E::clone(embed))
    }
    fn visit_label(&mut self, label: &'a L) -> Result<L, Self::Error> {
        Ok(L::clone(label))
    }
}

pub struct TraverseEmbedVisitor<F1>(pub F1);

impl<'a, 'b, N, E, E2, Err, F1>
    ExprVisitor<'a, SubExpr<N, E>, SubExpr<N, E2>, Label, Label, N, N, E, E2>
    for &'b mut TraverseEmbedVisitor<F1>
where
    N: Clone + 'a,
    E2: Clone,
    F1: FnMut(&E) -> Result<E2, Err>,
{
    type Error = Err;

    fn visit_subexpr(
        &mut self,
        subexpr: &'a SubExpr<N, E>,
    ) -> Result<SubExpr<N, E2>, Self::Error> {
        Ok(rc(subexpr.as_ref().visit(&mut **self)?))
    }
    fn visit_note(self, note: &'a N) -> Result<N, Self::Error> {
        Ok(N::clone(note))
    }
    fn visit_embed(self, embed: &'a E) -> Result<E2, Self::Error> {
        (self.0)(embed)
    }
    fn visit_label(&mut self, label: &'a Label) -> Result<Label, Self::Error> {
        Ok(Label::clone(label))
    }
}

pub struct SquashEmbedVisitor<F1>(pub F1);

impl<'a, 'b, N, E, E2, F1>
    ExprVisitor<'a, SubExpr<N, E>, SubExpr<N, E2>, Label, Label, N, N, E, E2>
    for &'b mut SquashEmbedVisitor<F1>
where
    N: Clone + 'a,
    E2: Clone,
    F1: FnMut(&E) -> SubExpr<N, E2>,
{
    type Error = X;

    fn visit_subexpr(
        &mut self,
        subexpr: &'a SubExpr<N, E>,
    ) -> Result<SubExpr<N, E2>, Self::Error> {
        Ok(rc(subexpr.as_ref().visit(&mut **self)?))
    }
    fn visit_note(self, note: &'a N) -> Result<N, Self::Error> {
        Ok(N::clone(note))
    }
    fn visit_embed(self, _: &'a E) -> Result<E2, Self::Error> {
        unreachable!()
    }
    fn visit_embed_squash(
        self,
        embed: &'a E,
    ) -> Result<Expr<N, E2>, Self::Error> {
        Ok((self.0)(embed).unroll())
    }
    fn visit_label(&mut self, label: &'a Label) -> Result<Label, Self::Error> {
        Ok(Label::clone(label))
    }
}

pub struct UnNoteVisitor;

impl<'a, 'b, N, E>
    ExprVisitor<'a, SubExpr<N, E>, SubExpr<X, E>, Label, Label, N, X, E, E>
    for &'b mut UnNoteVisitor
where
    E: Clone + 'a,
{
    type Error = X;

    fn visit_subexpr(
        &mut self,
        subexpr: &'a SubExpr<N, E>,
    ) -> Result<SubExpr<X, E>, Self::Error> {
        Ok(rc(subexpr.as_ref().visit(&mut **self)?))
    }
    fn visit_note(self, _: &'a N) -> Result<X, Self::Error> {
        unreachable!()
    }
    fn visit_note_squash(
        self,
        _: &'a N,
        subexpr: &'a SubExpr<N, E>,
    ) -> Result<Expr<X, E>, Self::Error> {
        subexpr.as_ref().visit(self)
    }
    fn visit_embed(self, embed: &'a E) -> Result<E, Self::Error> {
        Ok(E::clone(embed))
    }
    fn visit_label(&mut self, label: &'a Label) -> Result<Label, Self::Error> {
        Ok(Label::clone(label))
    }
}

pub struct NoteAbsurdVisitor;

impl<'a, 'b, N, E>
    ExprVisitor<'a, SubExpr<X, E>, SubExpr<N, E>, Label, Label, X, N, E, E>
    for &'b mut NoteAbsurdVisitor
where
    E: Clone + 'a,
{
    type Error = X;

    fn visit_subexpr(
        &mut self,
        subexpr: &'a SubExpr<X, E>,
    ) -> Result<SubExpr<N, E>, Self::Error> {
        Ok(rc(subexpr.as_ref().visit(&mut **self)?))
    }
    fn visit_note(self, note: &'a X) -> Result<N, Self::Error> {
        match *note {}
    }
    fn visit_embed(self, embed: &'a E) -> Result<E, Self::Error> {
        Ok(E::clone(embed))
    }
    fn visit_label(&mut self, label: &'a Label) -> Result<Label, Self::Error> {
        Ok(Label::clone(label))
    }
}

pub struct EmbedAbsurdVisitor;

impl<'a, 'b, N, E>
    ExprVisitor<'a, SubExpr<N, X>, SubExpr<N, E>, Label, Label, N, N, X, E>
    for &'b mut EmbedAbsurdVisitor
where
    N: Clone + 'a,
{
    type Error = X;

    fn visit_subexpr(
        &mut self,
        subexpr: &'a SubExpr<N, X>,
    ) -> Result<SubExpr<N, E>, Self::Error> {
        Ok(rc(subexpr.as_ref().visit(&mut **self)?))
    }
    fn visit_note(self, note: &'a N) -> Result<N, Self::Error> {
        Ok(N::clone(note))
    }
    fn visit_embed(self, embed: &'a X) -> Result<E, Self::Error> {
        match *embed {}
    }
    fn visit_label(&mut self, label: &'a Label) -> Result<Label, Self::Error> {
        Ok(Label::clone(label))
    }
}
