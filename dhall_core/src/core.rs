#![allow(non_snake_case)]
use std::collections::BTreeMap;
use std::rc::Rc;

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
    App(SubExpr, Vec<SubExpr>),
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
    ///  `None t`
    EmptyOptionalLit(SubExpr),
    ///  `Some e`
    NEOptionalLit(SubExpr),
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
    pub fn visit<'a, V, Return>(&'a self, v: V) -> Return
    where
        V: visitor::GenericVisitor<&'a ExprF<SE, L, N, E>, Return>,
    {
        v.visit(self)
    }
}

impl<S, A> Expr<S, A> {
    pub fn map_shallow<T, B, F1, F2, F3, F4>(
        &self,
        map_expr: F1,
        map_note: F2,
        map_embed: F3,
        map_label: F4,
    ) -> Expr<T, B>
    where
        A: Clone,
        T: Clone,
        S: Clone,
        F1: Fn(&Self) -> Expr<T, B>,
        F2: Fn(&S) -> T,
        F3: Fn(&A) -> B,
        F4: Fn(&Label) -> Label,
    {
        self.map_ref(
            |x| rc(map_expr(x.as_ref())),
            |_, x| rc(map_expr(x.as_ref())),
            map_note,
            map_embed,
            map_label,
        )
    }

    pub fn map_embed<B, F>(&self, map_embed: &F) -> Expr<S, B>
    where
        A: Clone,
        S: Clone,
        F: Fn(&A) -> B,
    {
        let recurse = |e: &Expr<S, A>| -> Expr<S, B> { e.map_embed(map_embed) };
        self.map_shallow(recurse, S::clone, map_embed, Label::clone)
    }

    pub fn traverse_embed<B, Err, F>(
        &self,
        map_embed: F,
    ) -> Result<Expr<S, B>, Err>
    where
        S: Clone,
        B: Clone,
        F: FnMut(&A) -> Result<B, Err>,
    {
        self.visit(&mut visitor::TraverseEmbedVisitor(map_embed))
    }

    pub fn map_label<F>(&self, map_label: &F) -> Self
    where
        A: Clone,
        S: Clone,
        F: Fn(&Label) -> Label,
    {
        let recurse = |e: &Self| -> Self { e.map_label(map_label) };
        self.map_shallow(recurse, S::clone, A::clone, map_label)
    }

    pub fn roll(&self) -> SubExpr<S, A>
    where
        S: Clone,
        A: Clone,
    {
        rc(ExprF::clone(self))
    }
}

impl<N: Clone, E> Expr<N, E> {
    pub fn squash_embed<E2: Clone>(
        &self,
        f: impl FnMut(&E) -> SubExpr<N, E2>,
    ) -> SubExpr<N, E2> {
        rc(self.visit(&mut visitor::SquashEmbedVisitor(f)))
    }
}

impl<SE, L, N, E> ExprF<SE, L, N, E> {
    pub fn traverse_ref<'a, SE2, L2, N2, E2, Err, F1, F2, F3, F4, F5>(
        &'a self,
        visit_subexpr: F1,
        visit_under_binder: F2,
        visit_note: F3,
        visit_embed: F4,
        visit_label: F5,
    ) -> Result<ExprF<SE2, L2, N2, E2>, Err>
    where
        L: Ord,
        L2: Ord,
        F1: FnMut(&'a SE) -> Result<SE2, Err>,
        F2: FnOnce(&'a L, &'a SE) -> Result<SE2, Err>,
        F3: FnOnce(&'a N) -> Result<N2, Err>,
        F4: FnOnce(&'a E) -> Result<E2, Err>,
        F5: FnMut(&'a L) -> Result<L2, Err>,
    {
        self.visit(visitor::TraverseRefVisitor {
            visit_subexpr,
            visit_under_binder,
            visit_note,
            visit_embed,
            visit_label,
        })
    }

    pub fn map_ref<'a, SE2, L2, N2, E2, F1, F2, F3, F4, F5>(
        &'a self,
        mut map_subexpr: F1,
        mut map_under_binder: F2,
        mut map_note: F3,
        mut map_embed: F4,
        mut map_label: F5,
    ) -> ExprF<SE2, L2, N2, E2>
    where
        L: Ord,
        L2: Ord,
        F1: FnMut(&'a SE) -> SE2,
        F2: FnMut(&'a L, &'a SE) -> SE2,
        F3: FnMut(&'a N) -> N2,
        F4: FnMut(&'a E) -> E2,
        F5: FnMut(&'a L) -> L2,
    {
        trivial_result(self.traverse_ref(
            |x| Ok(map_subexpr(x)),
            |l, x| Ok(map_under_binder(l, x)),
            |x| Ok(map_note(x)),
            |x| Ok(map_embed(x)),
            |x| Ok(map_label(x)),
        ))
    }

    pub fn traverse_ref_simple<'a, SE2, Err, F1>(
        &'a self,
        visit_subexpr: F1,
    ) -> Result<ExprF<SE2, L, N, E>, Err>
    where
        L: Ord + Clone,
        N: Clone,
        E: Clone,
        F1: FnMut(&'a SE) -> Result<SE2, Err>,
    {
        self.visit(visitor::TraverseRefSimpleVisitor { visit_subexpr })
    }

    pub fn map_ref_simple<'a, SE2, F1>(
        &'a self,
        map_subexpr: F1,
    ) -> ExprF<SE2, L, N, E>
    where
        L: Ord,
        L: Clone,
        N: Clone,
        E: Clone,
        F1: Fn(&'a SE) -> SE2,
    {
        trivial_result(self.traverse_ref_simple(|x| Ok(map_subexpr(x))))
    }
}

impl<N, E> SubExpr<N, E> {
    pub fn as_ref(&self) -> &Expr<N, E> {
        self.0.as_ref()
    }

    pub fn map_ref<'a, F1, F2>(
        &'a self,
        map_expr: F1,
        map_under_binder: F2,
    ) -> Self
    where
        F1: FnMut(&'a Self) -> Self,
        F2: FnMut(&'a Label, &'a Self) -> Self,
    {
        match self.as_ref() {
            ExprF::Embed(_) => SubExpr::clone(self),
            // Recursive call
            ExprF::Note(_, e) => e.map_ref(map_expr, map_under_binder),
            // Call ExprF::map_ref
            e => rc(e.map_ref(
                map_expr,
                map_under_binder,
                |_| unreachable!(),
                |_| unreachable!(),
                Label::clone,
            )),
        }
    }

    pub fn map_ref_simple<F1>(&self, map_expr: F1) -> Self
    where
        F1: Fn(&Self) -> Self,
    {
        self.map_ref(&map_expr, |_, e| map_expr(e))
    }

    pub fn unroll(&self) -> Expr<N, E>
    where
        N: Clone,
        E: Clone,
    {
        ExprF::clone(self.as_ref())
    }
}

impl<N: Clone> SubExpr<N, X> {
    pub fn absurd<T>(&self) -> SubExpr<N, T> {
        rc(self.as_ref().absurd_rec())
    }
}

impl<E: Clone> SubExpr<X, E> {
    pub fn note_absurd<N>(&self) -> SubExpr<N, E> {
        rc(self.as_ref().note_absurd())
    }
}

impl<E: Clone> Expr<X, E> {
    pub fn note_absurd<N>(&self) -> Expr<N, E> {
        self.visit(&mut visitor::NoteAbsurdVisitor)
    }
}

impl<N, E: Clone> SubExpr<N, E> {
    pub fn unnote(&self) -> SubExpr<X, E> {
        rc(self.as_ref().visit(&mut visitor::UnNoteVisitor))
    }
}

impl<N: Clone> Expr<N, X> {
    // Deprecated, use embed_absurd instead
    pub fn absurd_rec<T>(&self) -> Expr<N, T> {
        self.embed_absurd()
    }
    pub fn embed_absurd<T>(&self) -> Expr<N, T> {
        self.visit(&mut visitor::EmbedAbsurdVisitor)
    }
}

impl<N: Clone> SubExpr<N, X> {
    pub fn embed_absurd<T>(&self) -> SubExpr<N, T> {
        rc(self.as_ref().embed_absurd())
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

pub fn app<N, E>(f: Expr<N, E>, args: Vec<SubExpr<N, E>>) -> Expr<N, E> {
    if args.is_empty() {
        f
    } else {
        ExprF::App(rc(f), args)
    }
}

pub fn app_rc<N, E>(
    f: SubExpr<N, E>,
    args: Vec<SubExpr<N, E>>,
) -> SubExpr<N, E> {
    if args.is_empty() {
        f
    } else {
        rc(ExprF::App(f, args))
    }
}

fn add_ui(u: usize, i: isize) -> usize {
    if i < 0 {
        u.checked_sub(i.checked_neg().unwrap() as usize).unwrap()
    } else {
        u.checked_add(i as usize).unwrap()
    }
}

/// `shift` is used by both normalization and type-checking to avoid variable
/// capture by shifting variable indices
/// See https://github.com/dhall-lang/dhall-lang/blob/master/standard/semantics.md#shift
/// for details
pub fn shift<S, A>(
    delta: isize,
    var: &V<Label>,
    in_expr: &SubExpr<S, A>,
) -> SubExpr<S, A> {
    use crate::ExprF::*;
    let V(x, n) = var;
    let under_binder = |y: &Label, e: &SubExpr<_, _>| {
        let n = if x == y { n + 1 } else { *n };
        let newvar = &V(x.clone(), n);
        shift(delta, newvar, e)
    };
    match in_expr.as_ref() {
        Var(V(y, m)) if x == y && n <= m => {
            rc(Var(V(y.clone(), add_ui(*m, delta))))
        }
        _ => in_expr.map_ref(|e| shift(delta, var, e), under_binder),
    }
}

/// Substitute all occurrences of a variable with an expression, and
/// removes the variable from the environment by shifting the indices
/// of other variables appropriately.
///
/// ```text
/// subst_shift(x, v, e) = ↑(-1, x, e[x := ↑(1, x, v)])
/// ```
///
pub fn subst_shift<S, A>(
    var: &V<Label>,
    value: &SubExpr<S, A>,
    in_expr: &SubExpr<S, A>,
) -> SubExpr<S, A> {
    use crate::ExprF::*;
    let V(x, n) = var;
    let under_binder = |y: &Label, e: &SubExpr<_, _>| {
        let n = if x == y { n + 1 } else { *n };
        let newvar = &V(x.clone(), n);
        subst_shift(newvar, &shift(1, &V(y.clone(), 0), value), e)
    };
    match in_expr.as_ref() {
        Var(V(y, m)) if x == y && m == n => SubExpr::clone(value),
        Var(V(y, m)) if x == y && m > n => {
            let m = add_ui(*m, -1);
            rc(Var(V(x.clone(), m)))
        }
        _ => in_expr.map_ref(|e| subst_shift(var, &value, e), under_binder),
    }
}
