use std::collections::BTreeMap;

use crate::builtins::Builtin;
use crate::error::Error;
use crate::operations::OpKind;
use crate::semantics::Universe;
use crate::syntax::visitor;
use crate::syntax::*;

pub type Integer = i64;
pub type Natural = u64;
pub type Double = NaiveDouble;

/// Double with bitwise equality
#[derive(Debug, Copy, Clone)]
pub struct NaiveDouble(f64);

/// Constants for a pure type system
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Const {
    Type,
    Kind,
    Sort,
}

impl Const {
    pub fn to_universe(self) -> Universe {
        Universe::from_const(self)
    }
}

/// Bound variable
///
/// The `Label` field is the variable's name (i.e. \"`x`\").
/// The `Int` field is a DeBruijn index.
/// See dhall-lang/standard/semantics.md for details
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct V(pub Label, pub usize);

// Each node carries an annotation.
#[derive(Debug, Clone)]
pub struct Expr {
    kind: Box<ExprKind<Expr>>,
    span: Span,
}

pub type UnspannedExpr = ExprKind<Expr>;

/// Numeric literals
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NumKind {
    ///  `True`
    Bool(bool),
    ///  `1`
    Natural(Natural),
    ///  `+2`
    Integer(Integer),
    ///  `3.24`
    Double(Double),
}

/// Syntax tree for expressions
// Having the recursion out of the enum definition enables writing
// much more generic code and improves pattern-matching behind
// smart pointers.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprKind<SubExpr> {
    /// `Type`, `Kind` and `Sort`
    Const(Const),
    /// Numbers and booleans
    Num(NumKind),
    /// Built-in functions and types
    Builtin(Builtin),
    ///  `"Some ${interpolated} text"`
    TextLit(InterpolatedText<SubExpr>),
    ///  `Some e`
    SomeLit(SubExpr),
    ///  `[] : t`
    EmptyListLit(SubExpr),
    ///  `[x, y, z]`
    NEListLit(Vec<SubExpr>),
    ///  `{ k1 : t1, k2 : t1 }`
    RecordType(BTreeMap<Label, SubExpr>),
    ///  `{ k1 = v1, k2 = v2 }`
    RecordLit(BTreeMap<Label, SubExpr>),
    ///  `< k1 : t1, k2 >`
    UnionType(BTreeMap<Label, Option<SubExpr>>),

    ///  `x`, `x@n`
    Var(V),
    ///  `λ(x : A) -> b`
    Lam(Label, SubExpr, SubExpr),
    ///  `A -> B`, `∀(x : A) -> B`
    Pi(Label, SubExpr, SubExpr),
    ///  `let x : t = r in e`
    Let(Label, Option<SubExpr>, SubExpr, SubExpr),

    /// Operations
    Op(OpKind<SubExpr>),

    ///  `x : t`
    Annot(SubExpr, SubExpr),
    ///  `assert : t`
    Assert(SubExpr),

    /// `./some/path`
    Import(Import<SubExpr>),
}

impl<SE> ExprKind<SE> {
    pub fn traverse_ref_maybe_binder<'a, SE2, Err>(
        &'a self,
        visit: impl FnMut(Option<&'a Label>, &'a SE) -> Result<SE2, Err>,
    ) -> Result<ExprKind<SE2>, Err> {
        visitor::visit_ref(self, visit)
    }

    pub fn traverse_ref_with_special_handling_of_binders<'a, SE2, Err>(
        &'a self,
        mut visit_subexpr: impl FnMut(&'a SE) -> Result<SE2, Err>,
        mut visit_under_binder: impl FnMut(&'a Label, &'a SE) -> Result<SE2, Err>,
    ) -> Result<ExprKind<SE2>, Err> {
        self.traverse_ref_maybe_binder(|l, x| match l {
            None => visit_subexpr(x),
            Some(l) => visit_under_binder(l, x),
        })
    }

    pub fn traverse_ref<'a, SE2, Err>(
        &'a self,
        mut visit_subexpr: impl FnMut(&'a SE) -> Result<SE2, Err>,
    ) -> Result<ExprKind<SE2>, Err> {
        self.traverse_ref_maybe_binder(|_, e| visit_subexpr(e))
    }

    pub fn map_ref_maybe_binder<'a, SE2>(
        &'a self,
        mut map: impl FnMut(Option<&'a Label>, &'a SE) -> SE2,
    ) -> ExprKind<SE2> {
        trivial_result(self.traverse_ref_maybe_binder(|l, x| Ok(map(l, x))))
    }

    pub fn map_ref_with_special_handling_of_binders<'a, SE2>(
        &'a self,
        mut map_subexpr: impl FnMut(&'a SE) -> SE2,
        mut map_under_binder: impl FnMut(&'a Label, &'a SE) -> SE2,
    ) -> ExprKind<SE2> {
        self.map_ref_maybe_binder(|l, x| match l {
            None => map_subexpr(x),
            Some(l) => map_under_binder(l, x),
        })
    }

    pub fn map_ref<'a, SE2>(
        &'a self,
        mut map_subexpr: impl FnMut(&'a SE) -> SE2,
    ) -> ExprKind<SE2> {
        self.map_ref_maybe_binder(|_, e| map_subexpr(e))
    }
}

impl Expr {
    pub fn as_ref(&self) -> &UnspannedExpr {
        &self.kind
    }
    pub fn kind(&self) -> &UnspannedExpr {
        &self.kind
    }
    pub fn span(&self) -> Span {
        self.span.clone()
    }

    pub fn new(kind: UnspannedExpr, span: Span) -> Self {
        Expr {
            kind: Box::new(kind),
            span,
        }
    }

    // Compute the sha256 hash of the binary form of the expression.
    pub fn sha256_hash(&self) -> Result<Box<[u8]>, Error> {
        let data = binary::encode(self)?;
        Ok(crate::utils::sha256_hash(&data))
    }

    /// Wrap the expression into an additional let-binding
    pub fn add_let_binding(self, label: Label, value: Expr) -> Expr {
        Expr::new(ExprKind::Let(label, None, value, self), Span::Artificial)
    }
}

// Empty enum to indicate that no error can occur
pub(crate) enum X {}
pub(crate) fn trivial_result<T>(x: Result<T, X>) -> T {
    match x {
        Ok(x) => x,
        Err(e) => match e {},
    }
}

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

impl From<Label> for V {
    fn from(x: Label) -> V {
        V(x, 0)
    }
}

impl std::cmp::PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl std::cmp::Eq for Expr {}

impl std::hash::Hash for Expr {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        self.kind.hash(state)
    }
}
