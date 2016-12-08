#![allow(non_snake_case)]
use std::borrow::Cow;
use std::collections::HashMap;
use std::path::PathBuf;

/*
module Dhall.Core (
    -- * Syntax
      Const(..)
    , Path(..)
    , Var(..)
    , Expr(..)

    -- * Normalization
    , normalize
    , subst
    , shift

    -- * Pretty-printing
    , pretty

    -- * Miscellaneous
    , internalError
    ) where
*/

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
#[derive(Debug, Copy, Clone, PartialEq, Eq)] // (Show, Bounded, Enum)
pub enum Const {
    Type,
    Kind,
}


/// Path to an external resource
#[derive(Debug, Clone, PartialEq, Eq)] // (Eq, Ord, Show)
pub enum Path {
    File(PathBuf),
    URL(String),
}

/// Label for a bound variable
///
/// The `String` field is the variable's name (i.e. \"`x`\").
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
#[derive(Debug, Clone, PartialEq, Eq)] // (Eq, Show)
pub struct V<'i>(pub Cow<'i, str>, pub usize);

/*
instance IsString Var where
    fromString str = V (fromString str) 0

instance Buildable Var where
    build = buildVar
*/

/// Syntax tree for expressions
#[derive(Debug, Clone, PartialEq)] // (Functor, Foldable, Traversable, Show)
pub enum Expr<'i, S, A> {
    ///  `Const c                                  ~  c`
    Const(Const),
    ///  `Var (V x 0)                              ~  x`<br>
    ///  `Var (V x n)                              ~  x@n`
    Var(V<'i>),
    ///  `Lam x     A b                            ~  λ(x : A) -> b`
    Lam(Cow<'i, str>, Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `Pi "_" A B                               ~        A  -> B`
    ///  `Pi x   A B                               ~  ∀(x : A) -> B`
    Pi(Cow<'i, str>, Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `App f A                                  ~  f A`
    App(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `Let x Nothing  r e  ~  let x     = r in e`
    ///  `Let x (Just t) r e  ~  let x : t = r in e`
    Let(Cow<'i, str>, Option<Box<Expr<'i, S, A>>>, Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `Annot x t                                ~  x : t`
    Annot(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `Bool                                     ~  Bool`
    Bool,
    ///  `BoolLit b                                ~  b`
    BoolLit(bool),
    ///  `BoolAnd x y                              ~  x && y`
    BoolAnd(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `BoolOr  x y                              ~  x || y`
    BoolOr(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `BoolEQ  x y                              ~  x == y`
    BoolEQ(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `BoolNE  x y                              ~  x != y`
    BoolNE(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `BoolIf x y z                             ~  if x then y else z`
    BoolIf(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `Natural                                  ~  Natural`
    Natural,
    ///  `NaturalLit n                             ~  +n`
    NaturalLit(Natural),
    ///  `NaturalFold                              ~  Natural/fold`
    NaturalFold,
    ///  `NaturalBuild                             ~  Natural/build`
    NaturalBuild,
    ///  `NaturalIsZero                            ~  Natural/isZero`
    NaturalIsZero,
    ///  `NaturalEven                              ~  Natural/even`
    NaturalEven,
    ///  `NaturalOdd                               ~  Natural/odd`
    NaturalOdd,
    ///  `NaturalPlus x y                          ~  x + y`
    NaturalPlus(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `NaturalTimes x y                         ~  x * y`
    NaturalTimes(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `Integer                                  ~  Integer`
    Integer,
    ///  `IntegerLit n                             ~  n`
    IntegerLit(Integer),
    ///  `Double                                   ~  Double`
    Double,
    ///  `DoubleLit n                              ~  n`
    DoubleLit(Double),
    ///  `Text                                     ~  Text`
    Text,
    ///  `TextLit t                                ~  t`
    TextLit(Builder),
    ///  `TextAppend x y                           ~  x ++ y`
    TextAppend(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `List                                     ~  List`
    List,
    ///  `ListLit t [x, y, z]                      ~  [x, y, z] : List t`
    ListLit(Box<Expr<'i, S, A>>, Vec<Expr<'i, S, A>>),
    ///  `ListBuild                                ~  List/build`
    ListBuild,
    ///  `ListFold                                 ~  List/fold`
    ListFold,
    ///  `ListLength                               ~  List/length`
    ListLength,
    ///  `ListHead                                 ~  List/head`
    ListHead,
    ///  `ListLast                                 ~  List/last`
    ListLast,
    ///  `ListIndexed                              ~  List/indexed`
    ListIndexed,
    ///  `ListReverse                              ~  List/reverse`
    ListReverse,
    ///  `Optional                                 ~  Optional`
    Optional,
    ///  `OptionalLit t [e]                        ~  [e] : Optional t`
    ///  `OptionalLit t []                         ~  []  : Optional t`
    OptionalLit(Box<Expr<'i, S, A>>, Vec<Expr<'i, S, A>>),
    ///  `OptionalFold                             ~  Optional/fold`
    OptionalFold,
    ///  `Record            [(k1, t1), (k2, t2)]   ~  { k1 : t1, k2 : t1 }`
    Record(HashMap<Cow<'i, str>, Expr<'i, S, A>>),
    ///  `RecordLit         [(k1, v1), (k2, v2)]   ~  { k1 = v1, k2 = v2 }`
    RecordLit(HashMap<Cow<'i, str>, Expr<'i, S, A>>),
    ///  `Union             [(k1, t1), (k2, t2)]   ~  < k1 : t1, k2 : t2 >`
    Union(HashMap<Cow<'i, str>, Expr<'i, S, A>>),
    ///  `UnionLit (k1, v1) [(k2, t2), (k3, t3)]   ~  < k1 = t1, k2 : t2, k3 : t3 >`
    UnionLit(Cow<'i, str>, Box<Expr<'i, S, A>>, HashMap<Cow<'i, str>, Expr<'i, S, A>>),
    ///  `Combine x y                              ~  x ∧ y`
    Combine(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `Merge x y t                              ~  merge x y : t`
    Merge(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `Field e x                                ~  e.x`
    Field(Box<Expr<'i, S, A>>, Cow<'i, str>),
    ///  `Note S x                                 ~  e`
    Note(S, Box<Expr<'i, S, A>>),
    ///  `Embed path                               ~  path`
    Embed(A),
}

impl<'i, S, A> Expr<'i, S, A> {
    /// Clones the expression if it is a unit constructor
    fn clone_unit<T, B>(&self) -> Option<Expr<'static, T, B>> {
        use Expr::*;
        match self {
            &Bool          => Some(Bool),
            &Natural       => Some(Natural),
            &NaturalFold   => Some(NaturalFold),
            &NaturalBuild  => Some(NaturalBuild),
            &NaturalIsZero => Some(NaturalIsZero),
            &NaturalEven   => Some(NaturalEven),
            &NaturalOdd    => Some(NaturalOdd),
            &Integer       => Some(Integer),
            &Double        => Some(Double),
            &Text          => Some(Text),
            &List          => Some(List),
            &ListBuild     => Some(ListBuild),
            &ListFold      => Some(ListFold),
            &ListLength    => Some(ListLength),
            &ListHead      => Some(ListHead),
            &ListLast      => Some(ListLast),
            &ListIndexed   => Some(ListIndexed),
            &ListReverse   => Some(ListReverse),
            &Optional      => Some(Optional),
            &OptionalFold  => Some(OptionalFold),
            _              => None,
        }
    }

    /// Returns true if the expression is a unit constructor
    pub fn is_unit(&self) -> bool {
        self.clone_unit::<S, A>().is_some()
    }
}

impl<'i> From<&'i str> for V<'i> {
    fn from(s: &'i str) -> Self {
        V(Cow::Borrowed(s), 0)
    }
}

impl<'i, S, A> From<&'i str> for Expr<'i, S, A> {
    fn from(s: &'i str) -> Self {
        Expr::Var(V(Cow::Borrowed(s), 0))
    }
}

pub fn pi<'i, S, A, Name, Et, Ev>(var: Name, ty: Et, value: Ev) -> Expr<'i, S, A>
    where Name: Into<Cow<'i, str>>,
          Et: Into<Expr<'i, S, A>>,
          Ev: Into<Expr<'i, S, A>>
{
    Expr::Pi(var.into(), bx(ty.into()), bx(value.into()))
}

pub fn app<'i, S, A, Ef, Ex>(f: Ef, x: Ex) -> Expr<'i, S, A>
    where Ef: Into<Expr<'i, S, A>>,
          Ex: Into<Expr<'i, S, A>>
{
    Expr::App(bx(f.into()), bx(x.into()))
}

pub type Builder = String;
pub type Double = f64;
pub type Int = isize;
pub type Integer = isize;
pub type Natural = usize;

/// A void type
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum X {}

pub fn bx<T>(x: T) -> Box<T> {
    Box::new(x)
}

fn add_ui(u: usize, i: isize) -> usize {
    if i < 0 {
        u.checked_sub((i.checked_neg().unwrap() as usize)).unwrap()
    } else {
        u.checked_add(i as usize).unwrap()
    }
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
pub fn shift<'i, S, T, A>(d: isize, v: V, e: Expr<'i, S, A>) -> Expr<'i, T, A>
    where S: ::std::fmt::Debug,
          T: ::std::fmt::Debug,
          A: ::std::fmt::Debug,
{
    use Expr::*;
    match e {
        Const(a) => Const(a),
        Var(V(x2, n2)) => {
            let V(x, n) = v;
            let n3 = if x == x2 && n <= n2 { add_ui(n2, d) } else { n2 };
            Var(V(x2, n3))
        }
        Lam(x2, tA, b) => {
            let V(x, n) = v;
            let n2 = if x == x2 { n + 1 } else { n };
            let tA2 = shift(d, V(x.clone(), n ), *tA);
            let b2  = shift(d, V(x,         n2), *b);
            Lam(x2, bx(tA2), bx(b2))
        }
        Pi(x2, tA, tB) => {
            let V(x, n) = v;
            let n2 = if x == x2 { n + 1 } else { n };
            let tA2 = shift(d, V(x.clone(), n ), *tA);
            let tB2 = shift(d, V(x, n2), *tB);
            pi(x2, tA2, tB2)
        }
        App(f, a) => {
            let f2 = shift(d, v.clone(), *f);
            let a2 = shift(d, v,         *a);
            App(bx(f2), bx(a2))
        }
/*
shift d (V x n) (Let f mt r e) = Let f mt' r' e'
  where
    e' = shift d (V x n') e
      where
        n' = if x == f then n + 1 else n

    mt' = fmap (shift d (V x n)) mt
    r'  =       shift d (V x n)  r
shift d v (Annot a b) = Annot a' b'
  where
    a' = shift d v a
    b' = shift d v b
    */
        BoolLit(a) => BoolLit(a),
        BoolAnd(a, b) => BoolAnd(bx(shift(d, v.clone(), *a)), bx(shift(d, v, *b))),
/*
shift d v (BoolOr a b) = BoolOr a' b'
  where
    a' = shift d v a
    b' = shift d v b
shift d v (BoolEQ a b) = BoolEQ a' b'
  where
    a' = shift d v a
    b' = shift d v b
shift d v (BoolNE a b) = BoolNE a' b'
  where
    a' = shift d v a
    b' = shift d v b
shift d v (BoolIf a b c) = BoolIf a' b' c'
  where
    a' = shift d v a
    b' = shift d v b
    c' = shift d v c
shift _ _ Natural = Natural
shift _ _ (NaturalLit a) = NaturalLit a
shift _ _ NaturalFold = NaturalFold
shift _ _ NaturalBuild = NaturalBuild
shift _ _ NaturalIsZero = NaturalIsZero
shift _ _ NaturalEven = NaturalEven
shift _ _ NaturalOdd = NaturalOdd
shift d v (NaturalPlus a b) = NaturalPlus a' b'
  where
    a' = shift d v a
    b' = shift d v b
shift d v (NaturalTimes a b) = NaturalTimes a' b'
  where
    a' = shift d v a
    b' = shift d v b
shift _ _ Integer = Integer
shift _ _ (IntegerLit a) = IntegerLit a
shift _ _ Double = Double
shift _ _ (DoubleLit a) = DoubleLit a
shift _ _ Text = Text
shift _ _ (TextLit a) = TextLit a
shift d v (TextAppend a b) = TextAppend a' b'
  where
    a' = shift d v a
    b' = shift d v b
shift d v (ListLit a b) = ListLit a' b'
  where
    a' =       shift d v  a
    b' = fmap (shift d v) b
shift _ _ ListBuild = ListBuild
shift _ _ ListFold = ListFold
shift _ _ ListLength = ListLength
shift _ _ ListHead = ListHead
shift _ _ ListLast = ListLast
shift _ _ ListIndexed = ListIndexed
shift _ _ ListReverse = ListReverse
shift _ _ Optional = Optional
shift d v (OptionalLit a b) = OptionalLit a' b'
  where
    a' =       shift d v  a
    b' = fmap (shift d v) b
shift _ _ OptionalFold = OptionalFold
shift d v (Record a) = Record a'
  where
    a' = fmap (shift d v) a
shift d v (RecordLit a) = RecordLit a'
  where
    a' = fmap (shift d v) a
shift d v (Union a) = Union a'
  where
    a' = fmap (shift d v) a
shift d v (UnionLit a b c) = UnionLit a b' c'
  where
    b' =       shift d v  b
    c' = fmap (shift d v) c
shift d v (Combine a b) = Combine a' b'
  where
    a' = shift d v a
    b' = shift d v b
shift d v (Merge a b c) = Merge a' b' c'
  where
    a' = shift d v a
    b' = shift d v b
    c' = shift d v c
shift d v (Field a b) = Field a' b
  where
    a' = shift d v a
shift d v (Note _ b) = b'
  where
    b' = shift d v b
-- The Dhall compiler enforces that all embedded values are closed expressions
-- and `shift` does nothing to a closed expression
shift _ _ (Embed p) = Embed p
*/
        e => if let Some(e2) = e.clone_unit() {
            e2
        } else {
            panic!("Unimplemented shift case: {:?}", (d, v, e))
        },
    }
}


/// Substitute all occurrences of a variable with an expression
///
/// ```c
/// subst x C B  ~  B[x := C]
/// ```
///
pub fn subst<'i, S, T, A>(v: V<'i>, a: Expr<'i, S, A>, b: Expr<'i, T, A>) -> Expr<'i, S, A>
    where S: Clone + ::std::fmt::Debug,
          T: Clone + ::std::fmt::Debug,
          A: Clone + ::std::fmt::Debug,
{
    use Expr::*;
    match (a, b) {
        (_, Const(a)) => Const(a),
        (e, Lam(y, tA, b)) => {
            let V(x, n) = v;
            let n2  = if x == y { n + 1 } else { n };
            let tA2 = subst(V(x.clone(), n),                    e.clone(), *tA);
            let b2  = subst(V(x, n2), shift(1, V(y.clone(), 0), e), *b);
            Lam(y, bx(tA2), bx(b2))
        }
        (e, Pi(y, tA, tB)) => {
            let V(x, n) = v;
            let n2  = if x == y { n + 1 } else { n };
            let tA2 = subst(V(x.clone(), n),                    e.clone(), *tA);
            let tB2 = subst(V(x, n2), shift(1, V(y.clone(), 0), e), *tB);
            pi(y, tA2, tB2)
        }
        (e, App(f, a)) => {
            let f2 = subst(v.clone(), e.clone(), *f);
            let a2 = subst(v, e, *a);
            app(f2, a2)
        }
        (e, Var(v2)) => if v == v2 { e } else { Var(v2) },
        (e, ListLit(a, b)) => {
            let b2 = b.into_iter().map(|be| subst(v.clone(), e.clone(), be)).collect();
            let a2 = subst(v, e, *a);
            ListLit(bx(a2), b2)
        }
        (a, b) => if let Some(e2) = b.clone_unit() {
            e2
        } else {
            panic!("Unimplemented subst case: {:?}", (v, a, b))
        }
    }
}

/// Reduce an expression to its normal form, performing beta reduction
///
/// `normalize` does not type-check the expression.  You may want to type-check
/// expressions before normalizing them since normalization can convert an
/// ill-typed expression into a well-typed expression.
///
/// However, `normalize` will not fail if the expression is ill-typed and will
/// leave ill-typed sub-expressions unevaluated.
///
pub fn normalize<S, T, A>(e: Expr<S, A>) -> Expr<T, A>
    where S: Clone + ::std::fmt::Debug,
          T: Clone + ::std::fmt::Debug,
          A: Clone + ::std::fmt::Debug,
{
    use Expr::*;
    match e {
        Const(k) => Const(k),
        Var(v) => Var(v),
        Lam(x, tA, b) => {
            let tA2 = normalize(*tA);
            let b2  = normalize(*b);
            Lam(x, bx(tA2), bx(b2))
        }
        Pi(x, tA, tB) => {
            let tA2 = normalize(*tA);
            let tB2 = normalize(*tB);
            pi(x, tA2, tB2)
        }
        App(f, a) => match normalize::<S, T, A>(*f) {
            Lam(x, _A, b) => { // Beta reduce
                let vx0 = V(x, 0);
                let a2 = shift::<S, S, A>( 1, vx0.clone(), *a);
                let b2 = subst::<S, T, A>(vx0.clone(), a2, *b);
                let b3 = shift::<S, T, A>(-1, vx0, b2);
                normalize(b3)
            }
            f2 => match (f2, normalize::<S, T, A>(*a)) {
            /*
                -- fold/build fusion for `List`
                App (App ListBuild _) (App (App ListFold _) e') -> normalize e'
                App (App ListFold _) (App (App ListBuild _) e') -> normalize e'

                -- fold/build fusion for `Natural`
                App NaturalBuild (App NaturalFold e') -> normalize e'
                App NaturalFold (App NaturalBuild e') -> normalize e'

                App (App (App (App NaturalFold (NaturalLit n0)) _) succ') zero ->
                    normalize (go n0)
                  where
                    go !0 = zero
                    go !n = App succ' (go (n - 1))
                App NaturalBuild k
                    | check     -> NaturalLit n
                    | otherwise -> App f' a'
                  where
                    labeled =
                        normalize (App (App (App k Natural) "Succ") "Zero")

                    n = go 0 labeled
                      where
                        go !m (App (Var "Succ") e') = go (m + 1) e'
                        go !m (Var "Zero")          = m
                        go !_  _                    = internalError text
                    check = go labeled
                      where
                        go (App (Var "Succ") e') = go e'
                        go (Var "Zero")          = True
                        go  _                    = False
                        */
                (NaturalIsZero, NaturalLit(n)) => BoolLit(n == 0),
                (NaturalEven, NaturalLit(n)) => BoolLit(n % 2 == 0),
                (NaturalOdd, NaturalLit(n)) => BoolLit(n % 2 != 0),
                /*
                App (App ListBuild t) k
                    | check     -> ListLit t (buildVector k')
                    | otherwise -> App f' a'
                  where
                    labeled =
                        normalize (App (App (App k (App List t)) "Cons") "Nil")

                    k' cons nil = go labeled
                      where
                        go (App (App (Var "Cons") x) e') = cons x (go e')
                        go (Var "Nil")                   = nil
                        go  _                            = internalError text
                    check = go labeled
                      where
                        go (App (App (Var "Cons") _) e') = go e'
                        go (Var "Nil")                   = True
                        go  _                            = False
                App (App (App (App (App ListFold _) (ListLit _ xs)) _) cons) nil ->
                    normalize (Data.Vector.foldr cons' nil xs)
                  where
                    cons' y ys = App (App cons y) ys
                App (App ListLength _) (ListLit _ ys) ->
                    NaturalLit (fromIntegral (Data.Vector.length ys))
                App (App ListHead _) (ListLit t ys) ->
                    normalize (OptionalLit t (Data.Vector.take 1 ys))
                App (App ListLast _) (ListLit t ys) ->
                    normalize (OptionalLit t y)
                  where
                    y = if Data.Vector.null ys
                        then Data.Vector.empty
                        else Data.Vector.singleton (Data.Vector.last ys)
                App (App ListIndexed _) (ListLit t xs) ->
                    normalize (ListLit t' (fmap adapt (Data.Vector.indexed xs)))
                  where
                    t' = Record (Data.Map.fromList kts)
                      where
                        kts = [ ("index", Natural)
                              , ("value", t)
                              ]
                    adapt (n, x) = RecordLit (Data.Map.fromList kvs)
                      where
                        kvs = [ ("index", NaturalLit (fromIntegral n))
                              , ("value", x)
                              ]
                App (App ListReverse _) (ListLit t xs) ->
                    normalize (ListLit t (Data.Vector.reverse xs))
                App (App (App (App (App OptionalFold _) (OptionalLit _ xs)) _) just) nothing ->
                    normalize (maybe nothing just' (toMaybe xs))
                  where
                    just' y = App just y
                    toMaybe = Data.Maybe.listToMaybe . Data.Vector.toList
            */
                (f2, a2) => app(f2, a2),
            }
        },
        ListLit(t, es) => {
            let t2  = normalize(*t);
            let es2 = es.into_iter().map(normalize).collect();
            ListLit(bx(t2), es2)
        }
        _ => if let Some(e2) = e.clone_unit() {
            e2
        } else {
            panic!("Unimplemented normalize case: {:?}", e)
        }
    }
}
