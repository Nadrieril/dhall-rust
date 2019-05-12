use std::rc::Rc;

use crate::map::DupTreeMap;
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

// This is only for the specific `Label` type, not generic
impl From<Label> for V<Label> {
    fn from(x: Label) -> V<Label> {
        V(x, 0)
    }
}
impl<'a> From<&'a Label> for V<Label> {
    fn from(x: &'a Label) -> V<Label> {
        V(x.clone(), 0)
    }
}

// Definition order must match precedence order for
// pretty-printing to work correctly
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum BinOp {
    /// `x ? y`
    ImportAlt,
    /// `x || y`
    BoolOr,
    /// `x + y`
    NaturalPlus,
    /// `x ++ y`
    TextAppend,
    /// `x # y`
    ListAppend,
    /// `x && y`
    BoolAnd,
    /// `x ∧ y`
    RecursiveRecordMerge,
    /// `x ⫽ y`
    RightBiasedRecordMerge,
    /// `x ⩓ y`
    RecursiveRecordTypeMerge,
    /// `x * y`
    NaturalTimes,
    /// `x == y`
    BoolEQ,
    /// `x != y`
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

// Each node carries an annotation. In practice it's either X (no annotation) or a Span.
#[derive(Debug)]
pub struct SubExpr<Note, Embed>(Rc<(Expr<Note, Embed>, Option<Note>)>);

impl<Note, Embed: PartialEq> std::cmp::PartialEq for SubExpr<Note, Embed> {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ref().0 == other.0.as_ref().0
    }
}

impl<Note, Embed: Eq> std::cmp::Eq for SubExpr<Note, Embed> {}

pub type Expr<Note, Embed> = ExprF<SubExpr<Note, Embed>, Embed>;

/// Syntax tree for expressions
// Having the recursion out of the enum definition enables writing
// much more generic code and improves pattern-matching behind
// smart pointers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprF<SubExpr, Embed> {
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
    RecordType(DupTreeMap<Label, SubExpr>),
    ///  `{ k1 = v1, k2 = v2 }`
    RecordLit(DupTreeMap<Label, SubExpr>),
    ///  `< k1 : t1, k2 >`
    UnionType(DupTreeMap<Label, Option<SubExpr>>),
    ///  `< k1 = t1, k2 : t2, k3 >`
    UnionLit(Label, SubExpr, DupTreeMap<Label, Option<SubExpr>>),
    ///  `merge x y : t`
    Merge(SubExpr, SubExpr, Option<SubExpr>),
    ///  `e.x`
    Field(SubExpr, Label),
    ///  `e.{ x, y, z }`
    Projection(SubExpr, Vec<Label>),
    /// Embeds an import or the result of resolving the import
    Embed(Embed),
}

impl<SE, E> ExprF<SE, E> {
    pub(crate) fn visit<'a, V, Return>(&'a self, v: V) -> Return
    where
        V: visitor::GenericVisitor<&'a ExprF<SE, E>, Return>,
    {
        v.visit(self)
    }

    pub fn traverse_ref_with_special_handling_of_binders<'a, SE2, E2, Err>(
        &'a self,
        visit_subexpr: impl FnMut(&'a SE) -> Result<SE2, Err>,
        visit_under_binder: impl FnOnce(&'a Label, &'a SE) -> Result<SE2, Err>,
        visit_embed: impl FnOnce(&'a E) -> Result<E2, Err>,
    ) -> Result<ExprF<SE2, E2>, Err> {
        self.visit(visitor::TraverseRefWithBindersVisitor {
            visit_subexpr,
            visit_under_binder,
            visit_embed,
        })
    }

    fn traverse_ref<'a, SE2, E2, Err>(
        &'a self,
        visit_subexpr: impl FnMut(&'a SE) -> Result<SE2, Err>,
        visit_embed: impl FnOnce(&'a E) -> Result<E2, Err>,
    ) -> Result<ExprF<SE2, E2>, Err> {
        self.visit(visitor::TraverseRefVisitor {
            visit_subexpr,
            visit_embed,
        })
    }

    pub fn map_ref_with_special_handling_of_binders<'a, SE2, E2>(
        &'a self,
        mut map_subexpr: impl FnMut(&'a SE) -> SE2,
        mut map_under_binder: impl FnMut(&'a Label, &'a SE) -> SE2,
        map_embed: impl FnOnce(&'a E) -> E2,
    ) -> ExprF<SE2, E2> {
        trivial_result(self.traverse_ref_with_special_handling_of_binders(
            |x| Ok(map_subexpr(x)),
            |l, x| Ok(map_under_binder(l, x)),
            |x| Ok(map_embed(x)),
        ))
    }

    pub fn map_ref<'a, SE2, E2>(
        &'a self,
        mut map_subexpr: impl FnMut(&'a SE) -> SE2,
        map_embed: impl FnOnce(&'a E) -> E2,
    ) -> ExprF<SE2, E2> {
        trivial_result(
            self.traverse_ref(|x| Ok(map_subexpr(x)), |x| Ok(map_embed(x))),
        )
    }

    pub fn traverse_ref_simple<'a, SE2, Err>(
        &'a self,
        visit_subexpr: impl FnMut(&'a SE) -> Result<SE2, Err>,
    ) -> Result<ExprF<SE2, E>, Err>
    where
        E: Clone,
    {
        self.traverse_ref(visit_subexpr, |x| Ok(E::clone(x)))
    }

    pub fn map_ref_simple<'a, SE2>(
        &'a self,
        map_subexpr: impl Fn(&'a SE) -> SE2,
    ) -> ExprF<SE2, E>
    where
        E: Clone,
    {
        self.map_ref(map_subexpr, E::clone)
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
}

impl Expr<X, X> {
    pub fn absurd<N, E>(&self) -> Expr<N, E> {
        self.visit(&mut visitor::AbsurdVisitor)
    }
}

impl<E: Clone> Expr<X, E> {
    pub fn note_absurd<N>(&self) -> Expr<N, E> {
        self.visit(&mut visitor::NoteAbsurdVisitor)
    }
}

impl<N, E> SubExpr<N, E> {
    pub fn as_ref(&self) -> &Expr<N, E> {
        &self.0.as_ref().0
    }

    pub fn new(x: Expr<N, E>, n: N) -> Self {
        SubExpr(Rc::new((x, Some(n))))
    }

    pub fn from_expr_no_note(x: Expr<N, E>) -> Self {
        SubExpr(Rc::new((x, None)))
    }

    pub fn from_builtin(b: Builtin) -> Self {
        SubExpr::from_expr_no_note(ExprF::Builtin(b))
    }

    pub fn rewrap<E2>(&self, x: Expr<N, E2>) -> SubExpr<N, E2>
    where
        N: Clone,
    {
        SubExpr(Rc::new((x, (self.0).1.clone())))
    }

    pub fn traverse_embed<E2, Err>(
        &self,
        visit_embed: impl FnMut(&E) -> Result<E2, Err>,
    ) -> Result<SubExpr<N, E2>, Err>
    where
        N: Clone,
    {
        Ok(self.rewrap(self.as_ref().traverse_embed(visit_embed)?))
    }

    pub fn map_embed<E2>(
        &self,
        map_embed: impl FnMut(&E) -> E2,
    ) -> SubExpr<N, E2>
    where
        N: Clone,
    {
        self.rewrap(self.as_ref().map_embed(map_embed))
    }

    pub fn map_subexprs_with_special_handling_of_binders<'a>(
        &'a self,
        map_expr: impl FnMut(&'a Self) -> Self,
        map_under_binder: impl FnMut(&'a Label, &'a Self) -> Self,
    ) -> Self
    where
        N: Clone,
    {
        match self.as_ref() {
            ExprF::Embed(_) => SubExpr::clone(self),
            // This calls ExprF::map_ref
            e => self.rewrap(e.map_ref_with_special_handling_of_binders(
                map_expr,
                map_under_binder,
                |_| unreachable!(),
            )),
        }
    }
}

impl SubExpr<X, X> {
    pub fn absurd<N: Clone, T>(&self) -> SubExpr<N, T> {
        SubExpr::from_expr_no_note(self.as_ref().absurd())
    }
}

impl<E: Clone> SubExpr<X, E> {
    pub fn note_absurd<N>(&self) -> SubExpr<N, E> {
        SubExpr::from_expr_no_note(self.as_ref().note_absurd())
    }
}

impl<N, E> Clone for SubExpr<N, E> {
    fn clone(&self) -> Self {
        SubExpr(Rc::clone(&self.0))
    }
}

// Should probably rename this
pub fn rc<E>(x: Expr<X, E>) -> SubExpr<X, E> {
    SubExpr::from_expr_no_note(x)
}

/// Add an isize to an usize
/// Panics on over/underflow
fn add_ui(u: usize, i: isize) -> Option<usize> {
    Some(if i < 0 {
        u.checked_sub(i.checked_neg()? as usize)?
    } else {
        u.checked_add(i as usize)?
    })
}

impl<Label: PartialEq + Clone> V<Label> {
    pub fn shift(&self, delta: isize, var: &V<Label>) -> Option<Self> {
        let V(x, n) = var;
        let V(y, m) = self;
        Some(if x == y && n <= m {
            V(y.clone(), add_ui(*m, delta)?)
        } else {
            V(y.clone(), *m)
        })
    }

    pub fn over_binder(&self, x: &Label) -> Option<Self> {
        self.shift(-1, &V(x.clone(), 0))
    }
}
