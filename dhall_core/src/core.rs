#![allow(non_snake_case)]
use crate::*;
use std::collections::BTreeMap;
use std::rc::Rc;

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
    ///  [] : List t`
    EmptyListLit(SubExpr),
    ///  [x, y, z]
    NEListLit(Vec<SubExpr>),
    ///  None t
    EmptyOptionalLit(SubExpr),
    ///  Some e
    NEOptionalLit(SubExpr),
    ///  `{ k1 : t1, k2 : t1 }`
    RecordType(BTreeMap<Label, SubExpr>),
    ///  `{ k1 = v1, k2 = v2 }`
    RecordLit(BTreeMap<Label, SubExpr>),
    ///  `< k1 : t1, k2 : t2 >`
    UnionType(BTreeMap<Label, SubExpr>),
    ///  `< k1 = t1, k2 : t2, k3 : t3 >`
    UnionLit(Label, SubExpr, BTreeMap<Label, SubExpr>),
    ///  `merge x y : t`
    Merge(SubExpr, SubExpr, Option<SubExpr>),
    ///  e.x
    Field(SubExpr, Label),
    ///  e.{ x, y, z }
    Projection(SubExpr, Vec<Label>),
    /// Annotation on the AST. Unused for now but could hold e.g. file location information
    Note(Note, SubExpr),
    /// Embeds an import or the result of resolving the import
    Embed(Embed),
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
        F2: FnOnce(&S) -> T,
        F3: FnOnce(&A) -> B,
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
        map_embed: &F,
    ) -> Result<Expr<S, B>, Err>
    where
        S: Clone,
        B: Clone,
        F: Fn(&A) -> Result<B, Err>,
    {
        let recurse = |e: &SubExpr<S, A>| -> Result<SubExpr<S, B>, Err> {
            Ok(e.as_ref().traverse_embed(map_embed)?.roll())
        };
        self.traverse_ref(
            |e| recurse(e),
            |_, e| recurse(e),
            |x| Ok(S::clone(x)),
            map_embed,
            |x| Ok(Label::clone(x)),
        )
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
        f: &impl Fn(&E) -> SubExpr<N, E2>,
    ) -> SubExpr<N, E2> {
        match self.as_ref() {
            ExprF::Embed(e) => f(e),
            _ => self
                .map_ref(
                    |e| e.as_ref().squash_embed(f),
                    |_, e| e.as_ref().squash_embed(f),
                    N::clone,
                    |_| unreachable!(),
                    Label::clone,
                )
                .roll(),
        }
    }
}

impl<SE, L, N, E> ExprF<SE, L, N, E> {
    pub fn as_ref(&self) -> ExprF<&SE, &L, &N, &E>
    where
        L: Ord,
    {
        fn opt<T>(x: &Option<T>) -> Option<&T> {
            x.as_ref()
        }
        fn vec<T>(x: &[T]) -> Vec<&T> {
            x.iter().collect()
        }
        fn btmap<L: Ord, SE>(x: &BTreeMap<L, SE>) -> BTreeMap<&L, &SE> {
            x.iter().collect()
        }

        use crate::ExprF::*;
        match self {
            Var(V(l, n)) => Var(V(l, *n)),
            Lam(l, t, b) => Lam(l, t, b),
            Pi(l, t, b) => Pi(l, t, b),
            Let(l, t, a, b) => Let(l, opt(t), a, b),
            App(f, args) => App(f, vec(args)),
            Annot(x, t) => Annot(x, t),
            Const(k) => Const(*k),
            Builtin(v) => Builtin(*v),
            BoolLit(b) => BoolLit(*b),
            NaturalLit(n) => NaturalLit(*n),
            IntegerLit(n) => IntegerLit(*n),
            DoubleLit(n) => DoubleLit(*n),
            TextLit(t) => TextLit(t.as_ref()),
            BinOp(o, x, y) => BinOp(*o, x, y),
            BoolIf(b, t, f) => BoolIf(b, t, f),
            EmptyListLit(t) => EmptyListLit(t),
            NEListLit(es) => NEListLit(vec(es)),
            EmptyOptionalLit(t) => EmptyOptionalLit(t),
            NEOptionalLit(e) => NEOptionalLit(e),
            RecordType(kts) => RecordType(btmap(kts)),
            RecordLit(kvs) => RecordLit(btmap(kvs)),
            UnionType(kts) => UnionType(btmap(kts)),
            UnionLit(k, v, kvs) => UnionLit(k, v, btmap(kvs)),
            Merge(x, y, t) => Merge(x, y, opt(t)),
            Field(e, l) => Field(e, l),
            Projection(e, ls) => Projection(e, vec(ls)),
            Note(n, e) => Note(n, e),
            Embed(a) => Embed(a),
        }
    }

    fn traverse_ref<'a, SE2, L2, N2, E2, Err, F1, F2, F3, F4, F5>(
        &'a self,
        map_subexpr: F1,
        map_under_binder: F2,
        map_note: F3,
        map_embed: F4,
        mut map_label: F5,
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
        let mut map = map_subexpr;
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
        fn btmap<'a, K, L, T, U, Err, FK, FV>(
            x: &'a BTreeMap<K, T>,
            mut fk: FK,
            mut fv: FV,
        ) -> Result<BTreeMap<L, U>, Err>
        where
            K: Ord,
            L: Ord,
            FK: FnMut(&'a K) -> Result<L, Err>,
            FV: FnMut(&'a T) -> Result<U, Err>,
        {
            x.into_iter().map(|(k, v)| Ok((fk(k)?, fv(v)?))).collect()
        }

        use crate::ExprF::*;
        Ok(match self {
            Var(V(l, n)) => Var(V(map_label(l)?, *n)),
            Lam(l, t, b) => {
                let b = map_under_binder(&l, b)?;
                Lam(map_label(l)?, map(t)?, b)
            }
            Pi(l, t, b) => {
                let b = map_under_binder(&l, b)?;
                Pi(map_label(l)?, map(t)?, b)
            }
            Let(l, t, a, b) => {
                let b = map_under_binder(&l, b)?;
                Let(map_label(l)?, opt(t, &mut map)?, map(a)?, b)
            }
            App(f, args) => App(map(f)?, vec(args, map)?),
            Annot(x, t) => Annot(map(x)?, map(t)?),
            Const(k) => Const(*k),
            Builtin(v) => Builtin(*v),
            BoolLit(b) => BoolLit(*b),
            NaturalLit(n) => NaturalLit(*n),
            IntegerLit(n) => IntegerLit(*n),
            DoubleLit(n) => DoubleLit(*n),
            TextLit(t) => TextLit(t.traverse_ref(map)?),
            BinOp(o, x, y) => BinOp(*o, map(x)?, map(y)?),
            BoolIf(b, t, f) => BoolIf(map(b)?, map(t)?, map(f)?),
            EmptyListLit(t) => EmptyListLit(map(t)?),
            NEListLit(es) => NEListLit(vec(es, map)?),
            EmptyOptionalLit(t) => EmptyOptionalLit(map(t)?),
            NEOptionalLit(e) => NEOptionalLit(map(e)?),
            RecordType(kts) => RecordType(btmap(kts, map_label, map)?),
            RecordLit(kvs) => RecordLit(btmap(kvs, map_label, map)?),
            UnionType(kts) => UnionType(btmap(kts, map_label, map)?),
            UnionLit(k, v, kvs) => {
                UnionLit(map_label(k)?, map(v)?, btmap(kvs, map_label, map)?)
            }
            Merge(x, y, t) => Merge(map(x)?, map(y)?, opt(t, map)?),
            Field(e, l) => Field(map(e)?, map_label(l)?),
            Projection(e, ls) => Projection(map(e)?, vec(ls, map_label)?),
            Note(n, e) => Note(map_note(n)?, map(e)?),
            Embed(a) => Embed(map_embed(a)?),
        })
    }

    pub fn map_ref<'a, SE2, L2, N2, E2, F1, F2, F3, F4, F5>(
        &'a self,
        mut map_subexpr: F1,
        map_under_binder: F2,
        map_note: F3,
        map_embed: F4,
        mut map_label: F5,
    ) -> ExprF<SE2, L2, N2, E2>
    where
        L: Ord,
        L2: Ord,
        F1: FnMut(&'a SE) -> SE2,
        F2: FnOnce(&'a L, &'a SE) -> SE2,
        F3: FnOnce(&'a N) -> N2,
        F4: FnOnce(&'a E) -> E2,
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
        self.map_ref(
            &map_subexpr,
            |_, e| map_subexpr(e),
            N::clone,
            E::clone,
            L::clone,
        )
    }

    pub fn traverse_ref_simple<'a, SE2, Err, F1>(
        &'a self,
        map_subexpr: F1,
    ) -> Result<ExprF<SE2, L, N, E>, Err>
    where
        L: Ord,
        L: Clone,
        N: Clone,
        E: Clone,
        F1: Fn(&'a SE) -> Result<SE2, Err>,
    {
        self.traverse_ref(
            &map_subexpr,
            |_, e| map_subexpr(e),
            |x| Ok(N::clone(x)),
            |x| Ok(E::clone(x)),
            |x| Ok(L::clone(x)),
        )
    }

    // pub fn zip<SE2, L2, N2, E2>(
    //     self,
    //     other: ExprF<SE2, L2, N2, E2>
    // ) -> Option<ExprF<(SE, SE2), (L, L2), (N, N2), (E, E2)>>
    // where
    //     L: Ord,
    //     L2: Ord,
    // {
    //     // What to do with Var ?
    //     use crate::ExprF::*;
    //     match (self, other) {
    //         // Var(V(l, n)) => Var(V(map_label(l), n)),
    //         // Lam(l, t, b) => {
    //         // Pi(l, t, b) => {
    //         // Let(l, t, a, b) => {
    //         // App(f, args) => App(map(f), vec(args, map)),
    //         // Annot(x, t) => Annot(map(x), map(t)),
    //         (Const(x), Const(y)) if x == y => Some(Const(x)),
    //         (Builtin(x), Builtin(y)) if x == y => Some(Builtin(x)),
    //         (BoolLit(x), BoolLit(y)) if x == y => Some(BoolLit(x)),
    //         (NaturalLit(x), NaturalLit(y)) if x == y => Some(NaturalLit(x)),
    //         (IntegerLit(x), IntegerLit(y)) if x == y => Some(IntegerLit(x)),
    //         (DoubleLit(x), DoubleLit(y)) if x == y => Some(DoubleLit(x)),
    //         // TextLit(t) => TextLit(t.map(map)),
    //         // BinOp(o, x, y) => BinOp(o, map(x), map(y)),
    //         // BoolIf(b, t, f) => BoolIf(map(b), map(t), map(f)),
    //         // EmptyListLit(t) => EmptyListLit(map(t)),
    //         // NEListLit(es) => NEListLit(vec(es, map)),
    //         // EmptyOptionalLit(t) => EmptyOptionalLit(map(t)),
    //         // NEOptionalLit(e) => NEOptionalLit(map(e)),
    //         // RecordType(kts) => RecordType(btmap(kts, map_label, map)),
    //         // RecordLit(kvs) => RecordLit(btmap(kvs, map_label, map)),
    //         // UnionType(kts) => UnionType(btmap(kts, map_label, map)),
    //         // UnionLit(k, v, kvs) => {
    //         // Merge(x, y, t) => Merge(map(x), map(y), t.map(map)),
    //         // Field(e, l) => Field(map(e), map_label(l)),
    //         // Projection(e, ls) => Projection(map(e), vec(ls, map_label)),
    //         // Note(n, e) => Note(map_note(n), map(e)),
    //         // Embed(a) => Embed(map_embed(a)),
    //     }
    // }
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
        F2: FnOnce(&'a Label, &'a Self) -> Self,
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
        rc(self.as_ref().map_ref(
            |e| e.note_absurd(),
            |_, e| e.note_absurd(),
            |_| unreachable!(),
            E::clone,
            Label::clone,
        ))
    }
}

impl<E: Clone> Expr<X, E> {
    pub fn note_absurd<N: Clone>(&self) -> Expr<N, E> {
        self.roll().note_absurd().unroll()
    }
}

impl<N: Clone, E: Clone> SubExpr<N, E> {
    pub fn unnote(&self) -> SubExpr<X, E> {
        match self.as_ref() {
            ExprF::Note(_, e) => e.unnote(),
            e => rc(e.map_ref(
                |e| e.unnote(),
                |_, e| e.unnote(),
                |_| unreachable!(),
                E::clone,
                Label::clone,
            )),
        }
    }
}

impl<N: Clone> Expr<N, X> {
    // This is all very sad and I hope this can be avoided sometime
    pub fn absurd_rec<T>(&self) -> Expr<N, T> {
        self.map_ref(
            |e| e.absurd(),
            |_, e| e.absurd(),
            |_| unreachable!(),
            |_| unreachable!(),
            Label::clone,
        )
    }
}

impl<SE, L, N, E> ExprF<SE, L, N, E>
where
    SE: Clone,
    L: Clone + Ord,
    N: Clone,
{
    // When we know there is no Embed
    pub fn absurd<T>(&self) -> ExprF<SE, L, N, T> {
        self.map_ref(
            |e| e.clone(),
            |_, e| e.clone(),
            N::clone,
            |_| unreachable!(),
            L::clone,
        )
    }
}

impl<N, E> Clone for SubExpr<N, E> {
    fn clone(&self) -> Self {
        SubExpr(Rc::clone(&self.0))
    }
}

// Remains of a previous life, where everything was in Boxes
pub fn bx<N, E>(x: Expr<N, E>) -> SubExpr<N, E> {
    SubExpr(Rc::new(x))
}

// Should probably rename this too
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
/// ```
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
