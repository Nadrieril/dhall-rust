use std::iter::FromIterator;

use crate::semantics::{Binder, ValueKind};
use crate::syntax::Label;

/// A visitor trait that can be used to traverse `ValueKind`s. We need this pattern so that Rust lets
/// us have as much mutability as we can. See the equivalent file in `crate::syntax` for more
/// details.
pub(crate) trait ValueKindVisitor<'a, V1, V2>: Sized {
    type Error;

    fn visit_val(&mut self, val: &'a V1) -> Result<V2, Self::Error>;
    fn visit_binder(
        mut self,
        _label: &'a Binder,
        ty: &'a V1,
        val: &'a V1,
    ) -> Result<(V2, V2), Self::Error> {
        Ok((self.visit_val(ty)?, self.visit_val(val)?))
    }
    fn visit_vec(&mut self, x: &'a [V1]) -> Result<Vec<V2>, Self::Error> {
        x.iter().map(|e| self.visit_val(e)).collect()
    }
    fn visit_opt(
        &mut self,
        x: &'a Option<V1>,
    ) -> Result<Option<V2>, Self::Error> {
        Ok(match x {
            Some(x) => Some(self.visit_val(x)?),
            None => None,
        })
    }
    fn visit_map<T>(
        &mut self,
        x: impl IntoIterator<Item = (&'a Label, &'a V1)>,
    ) -> Result<T, Self::Error>
    where
        V1: 'a,
        T: FromIterator<(Label, V2)>,
    {
        x.into_iter()
            .map(|(k, x)| Ok((k.clone(), self.visit_val(x)?)))
            .collect()
    }
    fn visit_optmap<T>(
        &mut self,
        x: impl IntoIterator<Item = (&'a Label, &'a Option<V1>)>,
    ) -> Result<T, Self::Error>
    where
        V1: 'a,
        T: FromIterator<(Label, Option<V2>)>,
    {
        x.into_iter()
            .map(|(k, x)| Ok((k.clone(), self.visit_opt(x)?)))
            .collect()
    }

    fn visit(
        self,
        input: &'a ValueKind<V1>,
    ) -> Result<ValueKind<V2>, Self::Error> {
        visit_ref(self, input)
    }
}

fn visit_ref<'a, Visitor, V1, V2>(
    mut v: Visitor,
    input: &'a ValueKind<V1>,
) -> Result<ValueKind<V2>, Visitor::Error>
where
    Visitor: ValueKindVisitor<'a, V1, V2>,
{
    use ValueKind::*;
    Ok(match input {
        Lam(l, t, e) => {
            let (t, e) = v.visit_binder(l, t, e)?;
            Lam(l.clone(), t, e)
        }
        Pi(l, t, e) => {
            let (t, e) = v.visit_binder(l, t, e)?;
            Pi(l.clone(), t, e)
        }
        AppliedBuiltin(b, xs) => AppliedBuiltin(*b, v.visit_vec(xs)?),
        Var(v) => Var(v.clone()),
        Const(k) => Const(*k),
        BoolLit(b) => BoolLit(*b),
        NaturalLit(n) => NaturalLit(*n),
        IntegerLit(n) => IntegerLit(*n),
        DoubleLit(n) => DoubleLit(*n),
        EmptyOptionalLit(t) => EmptyOptionalLit(v.visit_val(t)?),
        NEOptionalLit(x) => NEOptionalLit(v.visit_val(x)?),
        EmptyListLit(t) => EmptyListLit(v.visit_val(t)?),
        NEListLit(xs) => NEListLit(v.visit_vec(xs)?),
        RecordType(kts) => RecordType(v.visit_map(kts)?),
        RecordLit(kvs) => RecordLit(v.visit_map(kvs)?),
        UnionType(kts) => UnionType(v.visit_optmap(kts)?),
        UnionConstructor(l, kts) => {
            UnionConstructor(l.clone(), v.visit_optmap(kts)?)
        }
        UnionLit(l, t, kts) => {
            UnionLit(l.clone(), v.visit_val(t)?, v.visit_optmap(kts)?)
        }
        TextLit(ts) => TextLit(
            ts.iter()
                .map(|t| t.traverse_ref(|e| v.visit_val(e)))
                .collect::<Result<_, _>>()?,
        ),
        Equivalence(x, y) => Equivalence(v.visit_val(x)?, v.visit_val(y)?),
        PartialExpr(e) => PartialExpr(e.traverse_ref(|e| v.visit_val(e))?),
    })
}

pub struct TraverseRefWithBindersVisitor<F1, F2> {
    pub visit_val: F1,
    pub visit_under_binder: F2,
}

impl<'a, V1, V2, Err, F1, F2> ValueKindVisitor<'a, V1, V2>
    for TraverseRefWithBindersVisitor<F1, F2>
where
    V1: 'a,
    F1: FnMut(&'a V1) -> Result<V2, Err>,
    F2: for<'b> FnOnce(&'a Binder, &'b V1, &'a V1) -> Result<V2, Err>,
{
    type Error = Err;

    fn visit_val(&mut self, val: &'a V1) -> Result<V2, Self::Error> {
        (self.visit_val)(val)
    }
    fn visit_binder<'b>(
        mut self,
        label: &'a Binder,
        ty: &'a V1,
        val: &'a V1,
    ) -> Result<(V2, V2), Self::Error> {
        let val = (self.visit_under_binder)(label, ty, val)?;
        let ty = (self.visit_val)(ty)?;
        Ok((ty, val))
    }
}
