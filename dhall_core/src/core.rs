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
pub struct V<Label>(pub Label, pub usize);

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

pub type ParsedExpr = SubExpr<X, Import>;
pub type ResolvedExpr = SubExpr<X, X>;
pub type DhallExpr = ResolvedExpr;

#[derive(Debug, PartialEq, Eq)]
pub struct SubExpr<Note, Embed>(pub Rc<Expr<Note, Embed>>);

pub type Expr<Note, Embed> = ExprF<SubExpr<Note, Embed>, Label, Note, Embed>;

/// Syntax tree for expressions
// Having the recursion out of the enum definition enables writing
// much more generic code and improves pattern-matching behind
// smart pointers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprF<SubExpr, Label, Note, Embed> {
    Const(Const),
    ///  `x`
    ///  `x@n`
    Var(V<Label>),
    ///  `λ(x : A) -> b`
    Lam(Label, SubExpr, SubExpr),
    ///  `A -> B`
    ///  `∀(x : A) -> B`
    Pi(Label, SubExpr, SubExpr),
    ///  `f a`
    App(SubExpr, SubExpr),
    ///  `let x     = r in e`
    ///  `let x : t = r in e`
    Let(Label, Option<SubExpr>, SubExpr, SubExpr),
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
    /// Annotation on the AST. Unused for now but could hold e.g. file location information
    Note(Note, SubExpr),
    /// Embeds an import or the result of resolving the import
    Embed(Embed),
}

impl<SE, L, N, E> ExprF<SE, L, N, E> {
    pub(crate) fn visit<'a, V, Return>(&'a self, v: V) -> Return
    where
        V: visitor::GenericVisitor<&'a ExprF<SE, L, N, E>, Return>,
    {
        v.visit(self)
    }

    fn traverse_ref_with_special_handling_of_binders<'a, SE2, L2, N2, E2, Err>(
        &'a self,
        visit_subexpr: impl FnMut(&'a SE) -> Result<SE2, Err>,
        visit_under_binder: impl FnOnce(&'a L, &'a SE) -> Result<SE2, Err>,
        visit_note: impl FnOnce(&'a N) -> Result<N2, Err>,
        visit_embed: impl FnOnce(&'a E) -> Result<E2, Err>,
        visit_label: impl FnMut(&'a L) -> Result<L2, Err>,
    ) -> Result<ExprF<SE2, L2, N2, E2>, Err>
    where
        L: Ord,
        L2: Ord,
    {
        self.visit(visitor::TraverseRefWithBindersVisitor {
            visit_subexpr,
            visit_under_binder,
            visit_note,
            visit_embed,
            visit_label,
        })
    }

    fn traverse_ref<'a, SE2, L2, N2, E2, Err>(
        &'a self,
        visit_subexpr: impl FnMut(&'a SE) -> Result<SE2, Err>,
        visit_note: impl FnOnce(&'a N) -> Result<N2, Err>,
        visit_embed: impl FnOnce(&'a E) -> Result<E2, Err>,
        visit_label: impl FnMut(&'a L) -> Result<L2, Err>,
    ) -> Result<ExprF<SE2, L2, N2, E2>, Err>
    where
        L: Ord,
        L2: Ord,
    {
        self.visit(visitor::TraverseRefVisitor {
            visit_subexpr,
            visit_note,
            visit_embed,
            visit_label,
        })
    }

    pub fn map_ref_with_special_handling_of_binders<'a, SE2, L2, N2, E2>(
        &'a self,
        mut map_subexpr: impl FnMut(&'a SE) -> SE2,
        mut map_under_binder: impl FnMut(&'a L, &'a SE) -> SE2,
        map_note: impl FnOnce(&'a N) -> N2,
        map_embed: impl FnOnce(&'a E) -> E2,
        mut map_label: impl FnMut(&'a L) -> L2,
    ) -> ExprF<SE2, L2, N2, E2>
    where
        L: Ord,
        L2: Ord,
    {
        trivial_result(self.traverse_ref_with_special_handling_of_binders(
            |x| Ok(map_subexpr(x)),
            |l, x| Ok(map_under_binder(l, x)),
            |x| Ok(map_note(x)),
            |x| Ok(map_embed(x)),
            |x| Ok(map_label(x)),
        ))
    }

    pub fn map_ref<'a, SE2, L2, N2, E2>(
        &'a self,
        mut map_subexpr: impl FnMut(&'a SE) -> SE2,
        map_note: impl FnOnce(&'a N) -> N2,
        map_embed: impl FnOnce(&'a E) -> E2,
        mut map_label: impl FnMut(&'a L) -> L2,
    ) -> ExprF<SE2, L2, N2, E2>
    where
        L: Ord,
        L2: Ord,
    {
        trivial_result(self.traverse_ref(
            |x| Ok(map_subexpr(x)),
            |x| Ok(map_note(x)),
            |x| Ok(map_embed(x)),
            |x| Ok(map_label(x)),
        ))
    }

    pub fn traverse_ref_simple<'a, SE2, Err>(
        &'a self,
        visit_subexpr: impl FnMut(&'a SE) -> Result<SE2, Err>,
    ) -> Result<ExprF<SE2, L, N, E>, Err>
    where
        L: Ord + Clone,
        N: Clone,
        E: Clone,
    {
        self.traverse_ref(
            visit_subexpr,
            |x| Ok(N::clone(x)),
            |x| Ok(E::clone(x)),
            |x| Ok(L::clone(x)),
        )
    }

    pub fn map_ref_simple<'a, SE2>(
        &'a self,
        map_subexpr: impl Fn(&'a SE) -> SE2,
    ) -> ExprF<SE2, L, N, E>
    where
        L: Ord + Clone,
        N: Clone,
        E: Clone,
    {
        self.map_ref(map_subexpr, N::clone, E::clone, L::clone)
    }
}

impl<N, E> Expr<N, E> {
    fn traverse_embed<E2, Err>(
        &self,
        visit_embed: impl FnMut(&E) -> Result<E2, Err>,
    ) -> Result<Expr<N, E2>, Err>
    where
        N: Clone,
    {
        self.visit(&mut visitor::TraverseEmbedVisitor(visit_embed))
    }

    fn map_embed<E2>(&self, mut map_embed: impl FnMut(&E) -> E2) -> Expr<N, E2>
    where
        N: Clone,
    {
        trivial_result(self.traverse_embed(|x| Ok(map_embed(x))))
    }

    pub fn roll(&self) -> SubExpr<N, E>
    where
        N: Clone,
        E: Clone,
    {
        rc(ExprF::clone(self))
    }

    pub fn squash_embed<E2>(
        &self,
        f: impl FnMut(&E) -> SubExpr<N, E2>,
    ) -> SubExpr<N, E2>
    where
        N: Clone,
    {
        trivial_result(self.visit(&mut visitor::SquashEmbedVisitor(f)))
    }
}

impl<E: Clone> Expr<X, E> {
    pub fn note_absurd<N>(&self) -> Expr<N, E> {
        self.visit(&mut visitor::NoteAbsurdVisitor)
    }
}

impl<N: Clone> Expr<N, X> {
    pub fn embed_absurd<E>(&self) -> Expr<N, E> {
        self.visit(&mut visitor::EmbedAbsurdVisitor)
    }
}

impl<N, E> SubExpr<N, E> {
    pub fn as_ref(&self) -> &Expr<N, E> {
        self.0.as_ref()
    }

    pub fn traverse_embed<E2, Err>(
        &self,
        visit_embed: impl FnMut(&E) -> Result<E2, Err>,
    ) -> Result<SubExpr<N, E2>, Err>
    where
        N: Clone,
    {
        Ok(rc(self.as_ref().traverse_embed(visit_embed)?))
    }

    pub fn map_embed<E2>(
        &self,
        map_embed: impl FnMut(&E) -> E2,
    ) -> SubExpr<N, E2>
    where
        N: Clone,
    {
        rc(self.as_ref().map_embed(map_embed))
    }

    pub fn map_subexprs_with_special_handling_of_binders<'a>(
        &'a self,
        map_expr: impl FnMut(&'a Self) -> Self,
        map_under_binder: impl FnMut(&'a Label, &'a Self) -> Self,
    ) -> Self {
        match self.as_ref() {
            ExprF::Embed(_) => SubExpr::clone(self),
            // Recursive call
            // TODO: don't discard the note !
            ExprF::Note(_, e) => e
                .map_subexprs_with_special_handling_of_binders(
                    map_expr,
                    map_under_binder,
                ),
            // Call ExprF::map_ref
            e => rc(e.map_ref_with_special_handling_of_binders(
                map_expr,
                map_under_binder,
                |_| unreachable!(),
                |_| unreachable!(),
                Label::clone,
            )),
        }
    }

    pub fn unroll(&self) -> Expr<N, E>
    where
        N: Clone,
        E: Clone,
    {
        ExprF::clone(self.as_ref())
    }

    pub fn unnote(&self) -> SubExpr<X, E>
    where
        E: Clone,
    {
        rc(self.as_ref().visit(&mut visitor::UnNoteVisitor))
    }

    /// `shift` is used by both normalization and type-checking to avoid variable
    /// capture by shifting variable indices
    /// See https://github.com/dhall-lang/dhall-lang/blob/master/standard/semantics.md#shift
    /// for details
    pub fn shift(&self, delta: isize, var: &V<Label>) -> Self {
        match self.as_ref() {
            ExprF::Var(v) => rc(ExprF::Var(v.shift(delta, var))),
            _ => self.map_subexprs_with_special_handling_of_binders(
                |e| e.shift(delta, var),
                |x: &Label, e| e.shift(delta, &var.shift0(1, x)),
            ),
        }
    }

    pub fn shift0(&self, delta: isize, label: &Label) -> Self {
        self.shift(delta, &V(label.clone(), 0))
    }

    pub fn subst_shift(&self, var: &V<Label>, val: &Self) -> Self {
        match self.as_ref() {
            ExprF::Var(v) if v == var => val.clone(),
            ExprF::Var(v) => rc(ExprF::Var(v.shift(-1, var))),
            _ => self.map_subexprs_with_special_handling_of_binders(
                |e| e.subst_shift(var, val),
                |x: &Label, e| {
                    e.subst_shift(&var.shift0(1, x), &val.shift0(1, x))
                },
            ),
        }
    }
}

impl<N: Clone> SubExpr<N, X> {
    pub fn embed_absurd<T>(&self) -> SubExpr<N, T> {
        rc(self.as_ref().embed_absurd())
    }
}

impl<E: Clone> SubExpr<X, E> {
    pub fn note_absurd<N>(&self) -> SubExpr<N, E> {
        rc(self.as_ref().note_absurd())
    }
}

impl<N, E> Clone for SubExpr<N, E> {
    fn clone(&self) -> Self {
        SubExpr(Rc::clone(&self.0))
    }
}

// Should probably rename this
pub fn rc<N, E>(x: Expr<N, E>) -> SubExpr<N, E> {
    SubExpr(Rc::new(x))
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

impl<Label: PartialEq + Clone> V<Label> {
    pub fn shift(&self, delta: isize, var: &V<Label>) -> Self {
        let V(x, n) = var;
        let V(y, m) = self;
        if x == y && n <= m {
            V(y.clone(), add_ui(*m, delta))
        } else {
            V(y.clone(), *m)
        }
    }

    pub fn shift0(&self, delta: isize, x: &Label) -> Self {
        let V(y, m) = self;
        if x == y {
            V(y.clone(), add_ui(*m, delta))
        } else {
            V(y.clone(), *m)
        }
    }
}

/// `shift` is used by both normalization and type-checking to avoid variable
/// capture by shifting variable indices
/// See https://github.com/dhall-lang/dhall-lang/blob/master/standard/semantics.md#shift
/// for details
///
pub fn shift<N, E>(
    delta: isize,
    var: &V<Label>,
    in_expr: &SubExpr<N, E>,
) -> SubExpr<N, E> {
    in_expr.shift(delta, var)
}

pub fn shift0<N, E>(
    delta: isize,
    label: &Label,
    in_expr: &SubExpr<N, E>,
) -> SubExpr<N, E> {
    shift(delta, &V(label.clone(), 0), in_expr)
}

pub fn shift0_multiple<N, E>(
    deltas: &HashMap<Label, isize>,
    in_expr: &SubExpr<N, E>,
) -> SubExpr<N, E> {
    shift0_multiple_inner(&Context::new(), deltas, in_expr)
}

fn shift0_multiple_inner<N, E>(
    ctx: &Context<Label, ()>,
    deltas: &HashMap<Label, isize>,
    in_expr: &SubExpr<N, E>,
) -> SubExpr<N, E> {
    use crate::ExprF::*;
    match in_expr.as_ref() {
        Var(V(y, m)) if ctx.lookup(y, *m).is_none() => {
            let delta = deltas.get(y).unwrap_or(&0);
            rc(Var(V(y.clone(), add_ui(*m, *delta))))
        }
        _ => in_expr.map_subexprs_with_special_handling_of_binders(
            |e| shift0_multiple_inner(ctx, deltas, e),
            |x: &Label, e| {
                shift0_multiple_inner(&ctx.insert(x.clone(), ()), deltas, e)
            },
        ),
    }
}
