#![allow(non_snake_case)]
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::rc::Rc;

use crate::context::Context;
use crate::visitor;
use crate::*;

pub type Integer = isize;
pub type Natural = usize;
pub type Double = NaiveDouble;

/// An empty type
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum X {}

pub fn trivial_result<T>(x: Result<T, X>) -> T {
    match x {
        Ok(x) => x,
        Err(e) => match e {},
    }
}

/// Double with bitwise equality
#[derive(Debug, Copy, Clone)]
pub struct NaiveDouble(f64);

impl PartialEq for NaiveDouble {
    fn eq(&self, other: &Self) -> bool {
        self.0.to_bits() == other.0.to_bits()
    }
}

impl Eq for NaiveDouble {}

impl From<f64> for NaiveDouble {
    fn from(x: f64) -> Self {
        NaiveDouble(x)
    }
}

impl From<NaiveDouble> for f64 {
    fn from(x: NaiveDouble) -> f64 {
        x.0
    }
}

/// Constants for a pure type system
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Const {
    Type,
    Kind,
    Sort,
}

/// Bound variable
///
/// The `Label` field is the variable's name (i.e. \"`x`\").
/// The `Int` field is a DeBruijn index.
/// See dhall-lang/standard/semantics.md for details
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Var<Label>(pub Label, pub usize);

// Definition order must match precedence order for
// pretty-printing to work correctly
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum BinOp {
    /// x ? y
    ImportAlt,
    /// x || y`
    BoolOr,
    /// x + y`
    NaturalPlus,
    /// x ++ y`
    TextAppend,
    /// x # y
    ListAppend,
    /// x && y`
    BoolAnd,
    /// x ∧ y`
    Combine,
    /// x // y
    Prefer,
    /// x //\\ y
    CombineTypes,
    /// x * y`
    NaturalTimes,
    /// x == y`
    BoolEQ,
    /// x != y`
    BoolNE,
}

/// Built-ins
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Builtin {
    Bool,
    Natural,
    Integer,
    Double,
    Text,
    List,
    Optional,
    OptionalNone,
    NaturalBuild,
    NaturalFold,
    NaturalIsZero,
    NaturalEven,
    NaturalOdd,
    NaturalToInteger,
    NaturalShow,
    IntegerToDouble,
    IntegerShow,
    DoubleShow,
    ListBuild,
    ListFold,
    ListLength,
    ListHead,
    ListLast,
    ListIndexed,
    ListReverse,
    OptionalFold,
    OptionalBuild,
    TextShow,
}

pub type ParsedExpr = SubExpr<Label, X, Import>;
pub type ResolvedExpr = SubExpr<Label, X, X>;
pub type DhallExpr = ResolvedExpr;

// Each node carries an annotation. In practice it's either X (no annotation) or a Span.
#[derive(Debug)]
pub struct SubExpr<VarLabel, Note, Embed>(
    Rc<(Expr<VarLabel, Note, Embed>, Option<Note>)>,
);

impl<VarLabel: PartialEq, Note, Embed: PartialEq> std::cmp::PartialEq
    for SubExpr<VarLabel, Note, Embed>
{
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ref().0 == other.0.as_ref().0
    }
}

impl<VarLabel: Eq, Note, Embed: Eq> std::cmp::Eq
    for SubExpr<VarLabel, Note, Embed>
{
}

pub type Expr<VarLabel, Note, Embed> =
    ExprF<SubExpr<VarLabel, Note, Embed>, VarLabel, Embed>;

/// Syntax tree for expressions
// Having the recursion out of the enum definition enables writing
// much more generic code and improves pattern-matching behind
// smart pointers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprF<SubExpr, VarLabel, Embed> {
    Const(Const),
    ///  `x`
    ///  `x@n`
    Var(Var<VarLabel>),
    ///  `λ(x : A) -> b`
    Lam(VarLabel, SubExpr, SubExpr),
    ///  `A -> B`
    ///  `∀(x : A) -> B`
    Pi(VarLabel, SubExpr, SubExpr),
    ///  `f a`
    App(SubExpr, SubExpr),
    ///  `let x     = r in e`
    ///  `let x : t = r in e`
    Let(VarLabel, Option<SubExpr>, SubExpr, SubExpr),
    ///  `x : t`
    Annot(SubExpr, SubExpr),
    /// Built-in values
    Builtin(Builtin),
    // Binary operations
    BinOp(BinOp, SubExpr, SubExpr),
    ///  `True`
    BoolLit(bool),
    ///  `if x then y else z`
    BoolIf(SubExpr, SubExpr, SubExpr),
    ///  `1`
    NaturalLit(Natural),
    ///  `+2`
    IntegerLit(Integer),
    ///  `3.24`
    DoubleLit(Double),
    ///  `"Some ${interpolated} text"`
    TextLit(InterpolatedText<SubExpr>),
    ///  `[] : List t`
    EmptyListLit(SubExpr),
    ///  `[x, y, z]`
    NEListLit(Vec<SubExpr>),
    /// Deprecated Optional literal form
    ///  `[] : Optional a`
    ///  `[x] : Optional a`
    OldOptionalLit(Option<SubExpr>, SubExpr),
    ///  `Some e`
    SomeLit(SubExpr),
    ///  `{ k1 : t1, k2 : t1 }`
    RecordType(BTreeMap<Label, SubExpr>),
    ///  `{ k1 = v1, k2 = v2 }`
    RecordLit(BTreeMap<Label, SubExpr>),
    ///  `< k1 : t1, k2 >`
    UnionType(BTreeMap<Label, Option<SubExpr>>),
    ///  `< k1 = t1, k2 : t2, k3 >`
    UnionLit(Label, SubExpr, BTreeMap<Label, Option<SubExpr>>),
    ///  `merge x y : t`
    Merge(SubExpr, SubExpr, Option<SubExpr>),
    ///  `e.x`
    Field(SubExpr, Label),
    ///  `e.{ x, y, z }`
    Projection(SubExpr, Vec<Label>),
    /// Embeds an import or the result of resolving the import
    Embed(Embed),
}

impl<SE, L, E> ExprF<SE, L, E> {
    pub(crate) fn visit<'a, V, Return>(&'a self, v: V) -> Return
    where
        V: visitor::GenericVisitor<&'a ExprF<SE, L, E>, Return>,
    {
        v.visit(self)
    }

    fn traverse_ref_with_special_handling_of_binders<'a, SE2, L2, E2, Err>(
        &'a self,
        visit_subexpr: impl FnMut(&'a SE) -> Result<SE2, Err>,
        visit_under_binder: impl FnOnce(&'a L, &'a SE) -> Result<SE2, Err>,
        visit_embed: impl FnOnce(&'a E) -> Result<E2, Err>,
        visit_label: impl FnMut(&'a L) -> Result<L2, Err>,
    ) -> Result<ExprF<SE2, L2, E2>, Err> {
        self.visit(visitor::TraverseRefWithBindersVisitor {
            visit_subexpr,
            visit_under_binder,
            visit_embed,
            visit_label,
        })
    }

    fn traverse_ref<'a, SE2, L2, E2, Err>(
        &'a self,
        visit_subexpr: impl FnMut(&'a SE) -> Result<SE2, Err>,
        visit_embed: impl FnOnce(&'a E) -> Result<E2, Err>,
        visit_label: impl FnMut(&'a L) -> Result<L2, Err>,
    ) -> Result<ExprF<SE2, L2, E2>, Err> {
        self.visit(visitor::TraverseRefVisitor {
            visit_subexpr,
            visit_embed,
            visit_label,
        })
    }

    pub fn map_ref_with_special_handling_of_binders<'a, SE2, L2, E2>(
        &'a self,
        mut map_subexpr: impl FnMut(&'a SE) -> SE2,
        mut map_under_binder: impl FnMut(&'a L, &'a SE) -> SE2,
        map_embed: impl FnOnce(&'a E) -> E2,
        mut map_label: impl FnMut(&'a L) -> L2,
    ) -> ExprF<SE2, L2, E2> {
        trivial_result(self.traverse_ref_with_special_handling_of_binders(
            |x| Ok(map_subexpr(x)),
            |l, x| Ok(map_under_binder(l, x)),
            |x| Ok(map_embed(x)),
            |x| Ok(map_label(x)),
        ))
    }

    pub fn map_ref<'a, SE2, L2, E2>(
        &'a self,
        mut map_subexpr: impl FnMut(&'a SE) -> SE2,
        map_embed: impl FnOnce(&'a E) -> E2,
        mut map_label: impl FnMut(&'a L) -> L2,
    ) -> ExprF<SE2, L2, E2> {
        trivial_result(self.traverse_ref(
            |x| Ok(map_subexpr(x)),
            |x| Ok(map_embed(x)),
            |x| Ok(map_label(x)),
        ))
    }

    pub fn traverse_ref_simple<'a, SE2, Err>(
        &'a self,
        visit_subexpr: impl FnMut(&'a SE) -> Result<SE2, Err>,
    ) -> Result<ExprF<SE2, L, E>, Err>
    where
        L: Clone,
        E: Clone,
    {
        self.traverse_ref(
            visit_subexpr,
            |x| Ok(E::clone(x)),
            |x| Ok(L::clone(x)),
        )
    }

    pub fn map_ref_simple<'a, SE2>(
        &'a self,
        map_subexpr: impl Fn(&'a SE) -> SE2,
    ) -> ExprF<SE2, L, E>
    where
        L: Clone,
        E: Clone,
    {
        self.map_ref(map_subexpr, E::clone, L::clone)
    }
}

impl<L, N, E> Expr<L, N, E> {
    fn traverse_embed<E2, Err>(
        &self,
        visit_embed: impl FnMut(&E) -> Result<E2, Err>,
    ) -> Result<Expr<L, N, E2>, Err>
    where
        L: Clone,
        N: Clone,
    {
        self.visit(&mut visitor::TraverseEmbedVisitor(visit_embed))
    }

    fn map_embed<E2>(
        &self,
        mut map_embed: impl FnMut(&E) -> E2,
    ) -> Expr<L, N, E2>
    where
        L: Clone,
        N: Clone,
    {
        trivial_result(self.traverse_embed(|x| Ok(map_embed(x))))
    }

    pub fn squash_embed<E2>(
        &self,
        f: impl FnMut(&E) -> SubExpr<L, N, E2>,
    ) -> SubExpr<L, N, E2>
    where
        L: Clone,
        N: Clone,
    {
        trivial_result(self.visit(&mut visitor::SquashEmbedVisitor(f)))
    }
}

impl<L: Clone, E: Clone> Expr<L, X, E> {
    pub fn note_absurd<N>(&self) -> Expr<L, N, E> {
        self.visit(&mut visitor::NoteAbsurdVisitor)
    }
}

impl<L: Clone, N: Clone> Expr<L, N, X> {
    pub fn embed_absurd<E>(&self) -> Expr<L, N, E> {
        self.visit(&mut visitor::EmbedAbsurdVisitor)
    }
}

impl<V, N, E> SubExpr<V, N, E> {
    pub fn as_ref(&self) -> &Expr<V, N, E> {
        &self.0.as_ref().0
    }

    pub fn new(x: Expr<V, N, E>, n: N) -> Self {
        SubExpr(Rc::new((x, Some(n))))
    }

    pub fn from_expr_no_note(x: Expr<V, N, E>) -> Self {
        SubExpr(Rc::new((x, None)))
    }

    pub fn unnote(&self) -> SubExpr<V, X, E>
    where
        V: Clone,
        E: Clone,
    {
        SubExpr::from_expr_no_note(
            self.as_ref().visit(&mut visitor::UnNoteVisitor),
        )
    }

    pub fn rewrap<E2>(&self, x: Expr<V, N, E2>) -> SubExpr<V, N, E2>
    where
        N: Clone,
    {
        SubExpr(Rc::new((x, (self.0).1.clone())))
    }

    pub fn traverse_embed<E2, Err>(
        &self,
        visit_embed: impl FnMut(&E) -> Result<E2, Err>,
    ) -> Result<SubExpr<V, N, E2>, Err>
    where
        V: Clone,
        N: Clone,
    {
        Ok(self.rewrap(self.as_ref().traverse_embed(visit_embed)?))
    }

    pub fn map_embed<E2>(
        &self,
        map_embed: impl FnMut(&E) -> E2,
    ) -> SubExpr<V, N, E2>
    where
        V: Clone,
        N: Clone,
    {
        self.rewrap(self.as_ref().map_embed(map_embed))
    }

    pub fn map_subexprs_with_special_handling_of_binders<'a>(
        &'a self,
        map_expr: impl FnMut(&'a Self) -> Self,
        map_under_binder: impl FnMut(&'a V, &'a Self) -> Self,
    ) -> Self
    where
        V: Clone,
        N: Clone,
    {
        match self.as_ref() {
            ExprF::Embed(_) => SubExpr::clone(self),
            // This calls ExprF::map_ref
            e => self.rewrap(e.map_ref_with_special_handling_of_binders(
                map_expr,
                map_under_binder,
                |_| unreachable!(),
                V::clone,
            )),
        }
    }

    /// `shift` is used by both normalization and type-checking to avoid variable
    /// capture by shifting variable indices
    /// See https://github.com/dhall-lang/dhall-lang/blob/master/standard/semantics.md#shift
    /// for details
    pub fn shift(&self, delta: isize, var: &Var<V>) -> Self
    where
        V: Clone + PartialEq,
        N: Clone,
    {
        match self.as_ref() {
            ExprF::Var(v) => self.rewrap(ExprF::Var(v.shift(delta, var))),
            _ => self.map_subexprs_with_special_handling_of_binders(
                |e| e.shift(delta, var),
                |x: &V, e| e.shift(delta, &var.shift(1, &Var::new(x.clone()))),
            ),
        }
    }

    pub fn subst_shift(&self, var: &Var<V>, val: &Self) -> Self
    where
        V: Clone + PartialEq,
        N: Clone,
    {
        match self.as_ref() {
            ExprF::Var(v) if v == var => val.clone(),
            ExprF::Var(v) => self.rewrap(ExprF::Var(v.shift(-1, var))),
            _ => self.map_subexprs_with_special_handling_of_binders(
                |e| e.subst_shift(var, val),
                |x: &V, e| {
                    e.subst_shift(
                        &var.shift(1, &Var::new(x.clone())),
                        &val.shift(1, &Var::new(x.clone())),
                    )
                },
            ),
        }
    }
}

impl<L: Clone, N: Clone> SubExpr<L, N, X> {
    pub fn embed_absurd<T>(&self) -> SubExpr<L, N, T> {
        self.rewrap(self.as_ref().embed_absurd())
    }
}

impl<L: Clone, E: Clone> SubExpr<L, X, E> {
    pub fn note_absurd<N>(&self) -> SubExpr<L, N, E> {
        SubExpr::from_expr_no_note(self.as_ref().note_absurd())
    }
}

impl<L, N, E> Clone for SubExpr<L, N, E> {
    fn clone(&self) -> Self {
        SubExpr(Rc::clone(&self.0))
    }
}

// Should probably rename this
pub fn rc<L, E>(x: Expr<L, X, E>) -> SubExpr<L, X, E> {
    SubExpr::from_expr_no_note(x)
}

/// Add an isize to an usize
/// Panics on over/underflow
fn add_ui(u: usize, i: isize) -> usize {
    if i < 0 {
        u.checked_sub(i.checked_neg().unwrap() as usize).unwrap()
    } else {
        u.checked_add(i as usize).unwrap()
    }
}

impl<L> Var<L> {
    fn new(x: L) -> Self {
        Var(x, 0)
    }
}
impl<L: PartialEq + Clone> Var<L> {
    pub fn shift(&self, delta: isize, var: &Var<L>) -> Self {
        let Var(x, n) = var;
        let Var(y, m) = self;
        if x == y && n <= m {
            Var(y.clone(), add_ui(*m, delta))
        } else {
            Var(y.clone(), *m)
        }
    }
}

// This is only for the specific `Label` type, not generic
impl From<Label> for Var<Label> {
    fn from(x: Label) -> Var<Label> {
        Var(x, 0)
    }
}
impl<'a> From<&'a Label> for Var<Label> {
    fn from(x: &'a Label) -> Var<Label> {
        Var(x.clone(), 0)
    }
}

/// `shift` is used by both normalization and type-checking to avoid variable
/// capture by shifting variable indices
/// See https://github.com/dhall-lang/dhall-lang/blob/master/standard/semantics.md#shift
/// for details
///
pub fn shift<N, E>(
    delta: isize,
    var: &Var<Label>,
    in_expr: &SubExpr<Label, N, E>,
) -> SubExpr<Label, N, E>
where
    N: Clone,
{
    in_expr.shift(delta, var)
}

pub fn shift0_multiple<N, E>(
    deltas: &HashMap<Label, isize>,
    in_expr: &SubExpr<Label, N, E>,
) -> SubExpr<Label, N, E>
where
    N: Clone,
{
    shift0_multiple_inner(&Context::new(), deltas, in_expr)
}

fn shift0_multiple_inner<N, E>(
    ctx: &Context<Label, ()>,
    deltas: &HashMap<Label, isize>,
    in_expr: &SubExpr<Label, N, E>,
) -> SubExpr<Label, N, E>
where
    N: Clone,
{
    match in_expr.as_ref() {
        ExprF::Var(Var(y, m)) if ctx.lookup(y, *m).is_none() => {
            let delta = deltas.get(y).unwrap_or(&0);
            in_expr.rewrap(ExprF::Var(Var(y.clone(), add_ui(*m, *delta))))
        }
        _ => in_expr.map_subexprs_with_special_handling_of_binders(
            |e| shift0_multiple_inner(ctx, deltas, e),
            |x: &Label, e| {
                shift0_multiple_inner(&ctx.insert(x.clone(), ()), deltas, e)
            },
        ),
    }
}
