#![allow(non_snake_case)]
use crate::*;
use std::collections::BTreeMap;
use std::rc::Rc;

pub type Int = isize;
pub type Integer = isize;
pub type Natural = usize;
pub type Double = NaiveDouble;

/// An empty type
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum X {}

/// Double with bitwise equality
#[derive(Debug, Copy, Clone)]
pub struct NaiveDouble(f64);

impl PartialEq for NaiveDouble {
    fn eq(&self, other: &Self) -> bool {
        return self.0.to_bits() == other.0.to_bits();
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
///
/// The only axiom is:
///
/// ```c
/// ⊦ Type : Kind
/// ```
///
/// ... and the valid rule pairs are:
///
/// ```c
/// ⊦ Type ↝ Type : Type  -- Functions from terms to terms (ordinary functions)
/// ⊦ Kind ↝ Type : Type  -- Functions from types to terms (polymorphic functions)
/// ⊦ Kind ↝ Kind : Kind  -- Functions from types to types (type constructors)
/// ```
///
/// These are the same rule pairs as System Fω
///
/// Note that Dhall does not support functions from terms to types and therefore
/// Dhall is not a dependently typed language
///
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Const {
    Type,
    Kind,
}

/// Bound variable
///
/// The `Label` field is the variable's name (i.e. \"`x`\").
///
/// The `Int` field disambiguates variables with the same name if there are
/// multiple bound variables of the same name in scope.  Zero refers to the
/// nearest bound variable and the index increases by one for each bound
/// variable of the same name going outward.  The following diagram may help:
///
/// ```c
///                                 +---refers to--+
///                                 |              |
///                                 v              |
/// \(x : Type) -> \(y : Type) -> \(x : Type) -> x@0
///
///   +------------------refers to-----------------+
///   |                                            |
///   v                                            |
/// \(x : Type) -> \(y : Type) -> \(x : Type) -> x@1
/// ```
///
/// This `Int` behaves like a De Bruijn index in the special case where all
/// variables have the same name.
///
/// You can optionally omit the index if it is `0`:
///
/// ```c
///                           +refers to+
///                           |         |
///                           v         |
/// \(x : *) -> \(y : *) -> \(x : *) -> x
/// ```
///
/// Zero indices are omitted when pretty-printing `Var`s and non-zero indices
/// appear as a numeric suffix.
///
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct V(pub Label, pub usize);

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BinOp {
    /// x && y`
    BoolAnd,
    /// x || y`
    BoolOr,
    /// x == y`
    BoolEQ,
    /// x != y`
    BoolNE,
    /// x + y`
    NaturalPlus,
    /// x * y`
    NaturalTimes,
    /// x ++ y`
    TextAppend,
    /// x ∧ y`
    Combine,
    /// x //\\ y
    CombineTypes,
    /// x ? y
    ImportAlt,
    /// x // y
    Prefer,
    /// x # y
    ListAppend,
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
    OptionalSome,
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

pub type SubExpr<Note, Embed> = Rc<Expr<Note, Embed>>;

/// Syntax tree for expressions
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr<Note, Embed> {
    ///  `Const c                                  ~  c`
    Const(Const),
    ///  `Var (V x 0)                              ~  x`<br>
    ///  `Var (V x n)                              ~  x@n`
    Var(V),
    ///  `Lam x     A b                            ~  λ(x : A) -> b`
    Lam(Label, SubExpr<Note, Embed>, SubExpr<Note, Embed>),
    ///  `Pi "_" A B                               ~        A  -> B`
    ///  `Pi x   A B                               ~  ∀(x : A) -> B`
    Pi(Label, SubExpr<Note, Embed>, SubExpr<Note, Embed>),
    ///  `App f A                                  ~  f A`
    App(SubExpr<Note, Embed>, Vec<SubExpr<Note, Embed>>),
    ///  `Let x Nothing  r e  ~  let x     = r in e`
    ///  `Let x (Just t) r e  ~  let x : t = r in e`
    Let(
        Label,
        Option<SubExpr<Note, Embed>>,
        SubExpr<Note, Embed>,
        SubExpr<Note, Embed>,
    ),
    ///  `Annot x t                                ~  x : t`
    Annot(SubExpr<Note, Embed>, SubExpr<Note, Embed>),
    /// Built-in values
    Builtin(Builtin),
    // Binary operations
    BinOp(BinOp, SubExpr<Note, Embed>, SubExpr<Note, Embed>),
    ///  `BoolLit b                                ~  b`
    BoolLit(bool),
    ///  `BoolIf x y z                             ~  if x then y else z`
    BoolIf(
        SubExpr<Note, Embed>,
        SubExpr<Note, Embed>,
        SubExpr<Note, Embed>,
    ),
    ///  `NaturalLit n                             ~  +n`
    NaturalLit(Natural),
    ///  `IntegerLit n                             ~  n`
    IntegerLit(Integer),
    ///  `DoubleLit n                              ~  n`
    DoubleLit(Double),
    ///  `TextLit t                                ~  t`
    TextLit(InterpolatedText<Note, Embed>),
    ///  [] : List t`
    EmptyListLit(SubExpr<Note, Embed>),
    ///  [x, y, z]
    NEListLit(Vec<SubExpr<Note, Embed>>),
    ///  None t
    EmptyOptionalLit(SubExpr<Note, Embed>),
    ///  Some e
    NEOptionalLit(SubExpr<Note, Embed>),
    ///  `Record            [(k1, t1), (k2, t2)]   ~  { k1 : t1, k2 : t1 }`
    RecordType(BTreeMap<Label, SubExpr<Note, Embed>>),
    ///  `RecordLit         [(k1, v1), (k2, v2)]   ~  { k1 = v1, k2 = v2 }`
    RecordLit(BTreeMap<Label, SubExpr<Note, Embed>>),
    ///  `Union             [(k1, t1), (k2, t2)]   ~  < k1 : t1, k2 : t2 >`
    UnionType(BTreeMap<Label, SubExpr<Note, Embed>>),
    ///  `UnionLit (k1, v1) [(k2, t2), (k3, t3)]   ~  < k1 = t1, k2 : t2, k3 : t3 >`
    UnionLit(
        Label,
        SubExpr<Note, Embed>,
        BTreeMap<Label, SubExpr<Note, Embed>>,
    ),
    ///  `Merge x y t                              ~  merge x y : t`
    Merge(
        SubExpr<Note, Embed>,
        SubExpr<Note, Embed>,
        Option<SubExpr<Note, Embed>>,
    ),
    ///  `Field e x                                ~  e.x`
    Field(SubExpr<Note, Embed>, Label),
    /// Annotation on the AST. Unused for now but could hold e.g. file location information
    Note(Note, SubExpr<Note, Embed>),
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
        map_subexpr(
            self,
            |x| rc(map_expr(x.as_ref())),
            map_note,
            map_embed,
            map_label,
            |_, x| rc(map_expr(x.as_ref())),
        )
    }

    pub fn map_embed<B, F>(&self, map_embed: &F) -> Expr<S, B>
    where
        A: Clone,
        S: Clone,
        F: Fn(&A) -> B,
    {
        let recurse = |e: &Expr<S, A>| -> Expr<S, B> { e.map_embed(map_embed) };
        self.map_shallow(recurse, |x| x.clone(), map_embed, |x| x.clone())
    }

    pub fn map_label<F>(&self, map_label: &F) -> Self
    where
        A: Clone,
        S: Clone,
        F: Fn(&Label) -> Label,
    {
        let recurse = |e: &Self| -> Self { e.map_label(map_label) };
        self.map_shallow(recurse, |x| x.clone(), |x| x.clone(), map_label)
    }
}

impl<S: Clone, A: Clone> Expr<S, Expr<S, A>> {
    pub fn squash_embed(&self) -> Expr<S, A> {
        match self {
            Expr::Embed(e) => e.clone(),
            e => e.map_shallow(
                |e| e.squash_embed(),
                |x| x.clone(),
                |_| unreachable!(),
                |x| x.clone(),
            ),
        }
    }
}

// Remains of a previous life, where everything was in Boxes
pub fn bx<T>(x: T) -> Rc<T> {
    Rc::new(x)
}

pub fn rc<T>(x: T) -> Rc<T> {
    Rc::new(x)
}

fn add_ui(u: usize, i: isize) -> usize {
    if i < 0 {
        u.checked_sub(i.checked_neg().unwrap() as usize).unwrap()
    } else {
        u.checked_add(i as usize).unwrap()
    }
}

/// Map over the immediate children of the passed Expr
pub fn map_subexpr<S, T, A, B, F1, F2, F3, F4, F5>(
    e: &Expr<S, A>,
    map: F1,
    map_note: F2,
    map_embed: F3,
    map_label: F4,
    map_under_binder: F5,
) -> Expr<T, B>
where
    F1: Fn(&SubExpr<S, A>) -> SubExpr<T, B>,
    F2: FnOnce(&S) -> T,
    F3: FnOnce(&A) -> B,
    F4: Fn(&Label) -> Label,
    F5: FnOnce(&Label, &SubExpr<S, A>) -> SubExpr<T, B>,
{
    use crate::Expr::*;
    let map = &map;
    let opt = |x: &Option<_>| x.as_ref().map(&map);
    let vec = |x: &Vec<_>| x.iter().map(&map).collect();
    let btmap = |x: &BTreeMap<_, _>| {
        x.into_iter().map(|(k, v)| (map_label(k), map(v))).collect()
    };
    match e {
        Const(k) => Const(*k),
        Var(V(x, n)) => Var(V(map_label(x), *n)),
        Lam(x, t, b) => Lam(map_label(x), map(t), map_under_binder(x, b)),
        Pi(x, t, b) => Pi(map_label(x), map(t), map_under_binder(x, b)),
        App(f, args) => App(map(f), vec(args)),
        Let(l, t, a, b) => {
            Let(map_label(l), opt(t), map(a), map_under_binder(l, b))
        }
        Annot(x, t) => Annot(map(x), map(t)),
        Builtin(v) => Builtin(*v),
        BoolLit(b) => BoolLit(*b),
        BoolIf(b, t, f) => BoolIf(map(b), map(t), map(f)),
        NaturalLit(n) => NaturalLit(*n),
        IntegerLit(n) => IntegerLit(*n),
        DoubleLit(n) => DoubleLit(*n),
        TextLit(t) => TextLit(t.map(&map)),
        BinOp(o, x, y) => BinOp(*o, map(x), map(y)),
        EmptyListLit(t) => EmptyListLit(map(t)),
        NEListLit(es) => NEListLit(vec(es)),
        EmptyOptionalLit(t) => EmptyOptionalLit(map(t)),
        NEOptionalLit(e) => NEOptionalLit(map(e)),
        RecordType(kts) => RecordType(btmap(kts)),
        RecordLit(kvs) => RecordLit(btmap(kvs)),
        UnionType(kts) => UnionType(btmap(kts)),
        UnionLit(k, v, kvs) => UnionLit(map_label(k), map(v), btmap(kvs)),
        Merge(x, y, t) => Merge(map(x), map(y), opt(t)),
        Field(r, x) => Field(map(r), map_label(x)),
        Note(n, e) => Note(map_note(n), map(e)),
        Embed(a) => Embed(map_embed(a)),
    }
}

pub fn map_subexpr_rc_binder<S, A, F1, F2>(
    e: &SubExpr<S, A>,
    map_expr: F1,
    map_under_binder: F2,
) -> SubExpr<S, A>
where
    F1: Fn(&SubExpr<S, A>) -> SubExpr<S, A>,
    F2: FnOnce(&Label, &SubExpr<S, A>) -> SubExpr<S, A>,
{
    match e.as_ref() {
        Expr::Embed(_) => Rc::clone(e),
        Expr::Note(_, e) => {
            map_subexpr_rc_binder(e, map_expr, map_under_binder)
        }
        _ => rc(map_subexpr(
            e,
            map_expr,
            |_| unreachable!(),
            |_| unreachable!(),
            Label::clone,
            map_under_binder,
        )),
    }
}

pub fn map_subexpr_rc<S, A, F1>(
    e: &SubExpr<S, A>,
    map_expr: F1,
) -> SubExpr<S, A>
where
    F1: Fn(&SubExpr<S, A>) -> SubExpr<S, A>,
{
    map_subexpr_rc_binder(e, &map_expr, |_, e| map_expr(e))
}

/// `shift` is used by both normalization and type-checking to avoid variable
/// capture by shifting variable indices
///
/// For example, suppose that you were to normalize the following expression:
///
/// ```c
/// λ(a : Type) → λ(x : a) → (λ(y : a) → λ(x : a) → y) x
/// ```
///
/// If you were to substitute `y` with `x` without shifting any variable
/// indices, then you would get the following incorrect result:
///
/// ```c
/// λ(a : Type) → λ(x : a) → λ(x : a) → x  -- Incorrect normalized form
/// ```
///
/// In order to substitute `x` in place of `y` we need to `shift` `x` by `1` in
/// order to avoid being misinterpreted as the `x` bound by the innermost
/// lambda.  If we perform that `shift` then we get the correct result:
///
/// ```c
/// λ(a : Type) → λ(x : a) → λ(x : a) → x@1
/// ```
///
/// As a more worked example, suppose that you were to normalize the following
/// expression:
///
/// ```c
///     λ(a : Type)
/// →   λ(f : a → a → a)
/// →   λ(x : a)
/// →   λ(x : a)
/// →   (λ(x : a) → f x x@1) x@1
/// ```
///
/// The correct normalized result would be:
///
/// ```c
///     λ(a : Type)
/// →   λ(f : a → a → a)
/// →   λ(x : a)
/// →   λ(x : a)
/// →   f x@1 x
/// ```
///
/// The above example illustrates how we need to both increase and decrease
/// variable indices as part of substitution:
///
/// * We need to increase the index of the outer `x\@1` to `x\@2` before we
///   substitute it into the body of the innermost lambda expression in order
///   to avoid variable capture.  This substitution changes the body of the
///   lambda expression to `(f x\@2 x\@1)`
///
/// * We then remove the innermost lambda and therefore decrease the indices of
///   both `x`s in `(f x\@2 x\@1)` to `(f x\@1 x)` in order to reflect that one
///   less `x` variable is now bound within that scope
///
/// Formally, `(shift d (V x n) e)` modifies the expression `e` by adding `d` to
/// the indices of all variables named `x` whose indices are greater than
/// `(n + m)`, where `m` is the number of bound variables of the same name
/// within that scope
///
/// In practice, `d` is always `1` or `-1` because we either:
///
/// * increment variables by `1` to avoid variable capture during substitution
/// * decrement variables by `1` when deleting lambdas after substitution
///
/// `n` starts off at `0` when substitution begins and increments every time we
/// descend into a lambda or let expression that binds a variable of the same
/// name in order to avoid shifting the bound variables by mistake.
///
pub fn shift<S, A>(
    delta: isize,
    var: &V,
    in_expr: &Rc<Expr<S, A>>,
) -> Rc<Expr<S, A>> {
    use crate::Expr::*;
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
        _ => map_subexpr_rc_binder(
            in_expr,
            |e| shift(delta, var, e),
            under_binder,
        ),
    }
}

/// Substitute all occurrences of a variable with an expression
///
/// ```c
/// subst x C B  ~  B[x := C]
/// ```
///
pub fn subst<S, A>(
    var: &V,
    value: &Rc<Expr<S, A>>,
    in_expr: &Rc<Expr<S, A>>,
) -> Rc<Expr<S, A>> {
    use crate::Expr::*;
    let under_binder = |y: &Label, e: &SubExpr<_, _>| {
        let V(x, n) = var;
        let n = if x == y { n + 1 } else { *n };
        let newvar = &V(x.clone(), n);
        subst(newvar, &shift(1, &V(y.clone(), 0), value), e)
    };
    match in_expr.as_ref() {
        Var(v) if var == v => Rc::clone(value),
        _ => map_subexpr_rc_binder(
            in_expr,
            |e| subst(var, value, e),
            under_binder,
        ),
    }
}
