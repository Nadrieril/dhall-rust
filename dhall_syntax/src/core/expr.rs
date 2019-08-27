use std::rc::Rc;

use crate::map::{DupTreeMap, DupTreeSet};
use crate::visitor;
use crate::*;

pub type Integer = isize;
pub type Natural = usize;
pub type Double = NaiveDouble;

pub fn trivial_result<T>(x: Result<T, !>) -> T {
    match x {
        Ok(x) => x,
        Err(e) => e,
    }
}

/// A location in the source text
#[derive(Debug, Clone)]
pub struct Span {
    input: Rc<str>,
    /// # Safety
    ///
    /// Must be a valid character boundary index into `input`.
    start: usize,
    /// # Safety
    ///
    /// Must be a valid character boundary index into `input`.
    end: usize,
}

impl Span {
    pub(crate) fn make(input: Rc<str>, sp: pest::Span) -> Self {
        Span {
            input,
            start: sp.start(),
            end: sp.end(),
        }
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

impl std::hash::Hash for NaiveDouble {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        self.0.to_bits().hash(state)
    }
}

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
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    /// x === y
    Equivalence,
}

/// Built-ins
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
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
    NaturalSubtract,
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

// Each node carries an annotation.
#[derive(Debug, Clone)]
pub struct Expr<Embed>(Box<(RawExpr<Embed>, Option<Span>)>);

pub type RawExpr<Embed> = ExprF<Expr<Embed>, Embed>;

impl<Embed: PartialEq> std::cmp::PartialEq for Expr<Embed> {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ref().0 == other.0.as_ref().0
    }
}

impl<Embed: Eq> std::cmp::Eq for Expr<Embed> {}

impl<Embed: std::hash::Hash> std::hash::Hash for Expr<Embed> {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        (self.0).0.hash(state)
    }
}

/// Syntax tree for expressions
// Having the recursion out of the enum definition enables writing
// much more generic code and improves pattern-matching behind
// smart pointers.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    ///  `assert : t`
    Assert(SubExpr),
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
    ///  `[] : t`
    EmptyListLit(SubExpr),
    ///  `[x, y, z]`
    NEListLit(Vec<SubExpr>),
    ///  `Some e`
    SomeLit(SubExpr),
    ///  `{ k1 : t1, k2 : t1 }`
    RecordType(DupTreeMap<Label, SubExpr>),
    ///  `{ k1 = v1, k2 = v2 }`
    RecordLit(DupTreeMap<Label, SubExpr>),
    ///  `< k1 : t1, k2 >`
    UnionType(DupTreeMap<Label, Option<SubExpr>>),
    ///  `merge x y : t`
    Merge(SubExpr, SubExpr, Option<SubExpr>),
    ///  `e.x`
    Field(SubExpr, Label),
    ///  `e.{ x, y, z }`
    Projection(SubExpr, DupTreeSet<Label>),
    /// `./some/path`
    Import(Import<SubExpr>),
    /// Embeds the result of resolving an import
    Embed(Embed),
}

impl<SE, E> ExprF<SE, E> {
    pub(crate) fn visit<'a, V, Return>(&'a self, v: V) -> Return
    where
        V: visitor::GenericVisitor<&'a ExprF<SE, E>, Return>,
    {
        v.visit(self)
    }

    pub fn traverse_ref_with_special_handling_of_binders<'a, SE2, Err>(
        &'a self,
        visit_subexpr: impl FnMut(&'a SE) -> Result<SE2, Err>,
        visit_under_binder: impl FnOnce(&'a Label, &'a SE) -> Result<SE2, Err>,
    ) -> Result<ExprF<SE2, E>, Err>
    where
        E: Clone,
    {
        self.visit(visitor::TraverseRefWithBindersVisitor {
            visit_subexpr,
            visit_under_binder,
        })
    }

    fn traverse_ref<'a, SE2, Err>(
        &'a self,
        visit_subexpr: impl FnMut(&'a SE) -> Result<SE2, Err>,
    ) -> Result<ExprF<SE2, E>, Err>
    where
        E: Clone,
    {
        self.visit(visitor::TraverseRefVisitor { visit_subexpr })
    }

    pub fn map_ref_with_special_handling_of_binders<'a, SE2>(
        &'a self,
        mut map_subexpr: impl FnMut(&'a SE) -> SE2,
        mut map_under_binder: impl FnMut(&'a Label, &'a SE) -> SE2,
    ) -> ExprF<SE2, E>
    where
        E: Clone,
    {
        trivial_result(self.traverse_ref_with_special_handling_of_binders(
            |x| Ok(map_subexpr(x)),
            |l, x| Ok(map_under_binder(l, x)),
        ))
    }

    pub fn map_ref<'a, SE2>(
        &'a self,
        mut map_subexpr: impl FnMut(&'a SE) -> SE2,
    ) -> ExprF<SE2, E>
    where
        E: Clone,
    {
        trivial_result(self.traverse_ref(|x| Ok(map_subexpr(x))))
    }
}

impl<E> RawExpr<E> {
    pub fn traverse_resolve<E2, Err>(
        &self,
        visit_import: impl FnMut(&Import<Expr<E2>>) -> Result<E2, Err>,
    ) -> Result<RawExpr<E2>, Err> {
        self.traverse_resolve_with_visitor(&mut visitor::ResolveVisitor(
            visit_import,
        ))
    }

    pub(crate) fn traverse_resolve_with_visitor<E2, Err, F1>(
        &self,
        visitor: &mut visitor::ResolveVisitor<F1>,
    ) -> Result<RawExpr<E2>, Err>
    where
        F1: FnMut(&Import<Expr<E2>>) -> Result<E2, Err>,
    {
        match self {
            ExprF::BinOp(BinOp::ImportAlt, l, r) => l
                .as_ref()
                .traverse_resolve_with_visitor(visitor)
                .or_else(|_| r.as_ref().traverse_resolve_with_visitor(visitor)),
            _ => {
                let e = self.visit(&mut *visitor)?;
                Ok(match &e {
                    ExprF::Import(import) => ExprF::Embed((visitor.0)(import)?),
                    _ => e,
                })
            }
        }
    }
}

impl<E> Expr<E> {
    pub fn as_ref(&self) -> &RawExpr<E> {
        &self.0.as_ref().0
    }

    pub fn new(x: RawExpr<E>, n: Span) -> Self {
        Expr(Box::new((x, Some(n))))
    }

    pub fn from_expr_no_span(x: RawExpr<E>) -> Self {
        Expr(Box::new((x, None)))
    }

    pub fn from_builtin(b: Builtin) -> Self {
        Expr::from_expr_no_span(ExprF::Builtin(b))
    }

    pub fn rewrap<E2>(&self, x: RawExpr<E2>) -> Expr<E2> {
        Expr(Box::new((x, (self.0).1.clone())))
    }
}

impl<E> Expr<E> {
    pub fn traverse_resolve<E2, Err>(
        &self,
        visit_import: impl FnMut(&Import<Expr<E2>>) -> Result<E2, Err>,
    ) -> Result<Expr<E2>, Err> {
        Ok(self.rewrap(self.as_ref().traverse_resolve(visit_import)?))
    }
}

// Should probably rename this
pub fn rc<E>(x: RawExpr<E>) -> Expr<E> {
    Expr::from_expr_no_span(x)
}

pub(crate) fn spanned(
    span: Span,
    x: crate::parser::ParsedRawExpr,
) -> crate::parser::ParsedExpr {
    Expr::new(x, span)
}
pub(crate) fn unspanned(
    x: crate::parser::ParsedRawExpr,
) -> crate::parser::ParsedExpr {
    Expr::from_expr_no_span(x)
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
