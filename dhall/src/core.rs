#![allow(non_snake_case)]
use std::collections::BTreeMap;
use std::fmt::{self, Display};
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
#[derive(Debug, Copy, Clone, PartialEq, Eq)] // (Eq, Show)
pub struct V<'i>(pub &'i str, pub usize);

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
    Lam(&'i str, Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `Pi "_" A B                               ~        A  -> B`
    ///  `Pi x   A B                               ~  ∀(x : A) -> B`
    Pi(&'i str, Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `App f A                                  ~  f A`
    App(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `Let x Nothing  r e  ~  let x     = r in e`
    ///  `Let x (Just t) r e  ~  let x : t = r in e`
    Let(&'i str, Option<Box<Expr<'i, S, A>>>, Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `Annot x t                                ~  x : t`
    Annot(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    /// Built-in values
    Builtin(Builtin),
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
    ///  `NaturalLit n                             ~  +n`
    NaturalLit(Natural),
    ///  `NaturalPlus x y                          ~  x + y`
    NaturalPlus(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `NaturalTimes x y                         ~  x * y`
    NaturalTimes(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `IntegerLit n                             ~  n`
    IntegerLit(Integer),
    ///  `DoubleLit n                              ~  n`
    DoubleLit(Double),
    ///  `TextLit t                                ~  t`
    TextLit(Builder),
    ///  `TextAppend x y                           ~  x ++ y`
    TextAppend(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `ListLit t [x, y, z]                      ~  [x, y, z] : List t`
    ListLit(Box<Expr<'i, S, A>>, Vec<Expr<'i, S, A>>),
    ///  `OptionalLit t [e]                        ~  [e] : Optional t`
    ///  `OptionalLit t []                         ~  []  : Optional t`
    OptionalLit(Box<Expr<'i, S, A>>, Vec<Expr<'i, S, A>>),
    ///  `Record            [(k1, t1), (k2, t2)]   ~  { k1 : t1, k2 : t1 }`
    Record(BTreeMap<&'i str, Expr<'i, S, A>>),
    ///  `RecordLit         [(k1, v1), (k2, v2)]   ~  { k1 = v1, k2 = v2 }`
    RecordLit(BTreeMap<&'i str, Expr<'i, S, A>>),
    ///  `Union             [(k1, t1), (k2, t2)]   ~  < k1 : t1, k2 : t2 >`
    Union(BTreeMap<&'i str, Expr<'i, S, A>>),
    ///  `UnionLit (k1, v1) [(k2, t2), (k3, t3)]   ~  < k1 = t1, k2 : t2, k3 : t3 >`
    UnionLit(&'i str, Box<Expr<'i, S, A>>, BTreeMap<&'i str, Expr<'i, S, A>>),
    ///  `Combine x y                              ~  x ∧ y`
    Combine(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    /// x //\\ y
    CombineTypes(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    /// x ? y
    ImportAlt(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    /// x // y
    Prefer(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    /// x # y
    ListAppend(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `Merge x y t                              ~  merge x y : t`
    Merge(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>),
    ///  `Field e x                                ~  e.x`
    Field(Box<Expr<'i, S, A>>, &'i str),
    ///  `Note S x                                 ~  e`
    Note(S, Box<Expr<'i, S, A>>),
    ///  `Embed path                               ~  path`
    Embed(A),

    FailedParse(String, Vec<Expr<'i, S, A>>),
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
    NaturalFold,
    NaturalBuild,
    NaturalIsZero,
    NaturalEven,
    NaturalOdd,
    NaturalShow,
    ListBuild,
    ListFold,
    ListLength,
    ListHead,
    ListLast,
    ListIndexed,
    ListReverse,
    OptionalFold,
}

impl<'i> From<&'i str> for V<'i> {
    fn from(s: &'i str) -> Self {
        V(s, 0)
    }
}

impl<'i, S, A> From<&'i str> for Expr<'i, S, A> {
    fn from(s: &'i str) -> Self {
        Expr::Var(s.into())
    }
}

impl<'i, S, A> From<Builtin> for Expr<'i, S, A> {
    fn from(t: Builtin) -> Self {
        Expr::Builtin(t)
    }
}

impl<'i, S, A> Expr<'i, S, A> {
    fn bool_lit(&self) -> Option<bool> {
        match *self {
            Expr::BoolLit(v) => Some(v),
            _ => None,
        }
    }

    fn natural_lit(&self) -> Option<usize> {
        match *self {
            Expr::NaturalLit(v) => Some(v),
            _ => None,
        }
    }

    fn text_lit(&self) -> Option<String> {
        match *self {
            Expr::TextLit(ref t) => Some(t.clone()), // FIXME?
            _ => None,
        }
    }
}

//  There is a one-to-one correspondence between the formatters in this section
//  and the grammar in grammar.lalrpop.  Each formatter is named after the
//  corresponding grammar rule and the relationship between formatters exactly matches
//  the relationship between grammar rules.  This leads to the nice emergent property
//  of automatically getting all the parentheses and precedences right.
//
//  This approach has one major disadvantage: you can get an infinite loop if
//  you add a new constructor to the syntax tree without adding a matching
//  case the corresponding builder.

impl<'i, S, A: Display> Display for Expr<'i, S, A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> { // buildExprA
        use crate::Expr::*;
        match self {
            &Annot(ref a, ref b) => { a.fmt_b(f)?; write!(f, " : ")?; b.fmt(f) }
            &Note(_, ref b) => b.fmt(f),
            a => a.fmt_b(f),
        }
    }
}

impl<'i, S, A: Display> Expr<'i, S, A> {
    fn fmt_b(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use crate::Expr::*;
        match self {
            &Lam(a, ref b, ref c) => {
                write!(f, "λ({} : ", a)?;
                b.fmt(f)?;
                write!(f, ") → ")?;
                c.fmt_b(f)
            }
            &BoolIf(ref a, ref b, ref c) => {
                write!(f, "if ")?;
                a.fmt(f)?;
                write!(f, " then ")?;
                b.fmt_b(f)?;
                write!(f, " else ")?;
                c.fmt_c(f)
            }
            &Pi("_", ref b, ref c) => {
                b.fmt_c(f)?;
                write!(f, " → ")?;
                c.fmt_b(f)
            }
            &Pi(a, ref b, ref c) => {
                write!(f, "∀({} : ", a)?;
                b.fmt(f)?;
                write!(f, ") → ")?;
                c.fmt_b(f)
            }
            &Let(a, None, ref c, ref d) => {
                write!(f, "let {} = ", a)?;
                c.fmt(f)?;
                write!(f, ") → ")?;
                d.fmt_b(f)
            }
            &Let(a, Some(ref b), ref c, ref d) => {
                write!(f, "let {} : ", a)?;
                b.fmt(f)?;
                write!(f, " = ")?;
                c.fmt(f)?;
                write!(f, ") → ")?;
                d.fmt_b(f)
            }
            &ListLit(ref t, ref es) => {
                fmt_list("[", "] : List ", es, f, |e, f| e.fmt(f))?;
                t.fmt_e(f)
            }
            &OptionalLit(ref t, ref es) => {
                fmt_list("[", "] : Optional ", es, f, |e, f| e.fmt(f))?;
                t.fmt_e(f)
            }
            &Merge(ref a, ref b, ref c) => {
                write!(f, "merge ")?;
                a.fmt_e(f)?;
                write!(f, " ")?;
                b.fmt_e(f)?;
                write!(f, " : ")?;
                c.fmt_d(f)
            }
            &Note(_, ref b) => b.fmt_b(f),
            a => a.fmt_c(f),
        }
    }

    fn fmt_c(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use crate::Expr::*;
        match self {
            // FIXME precedence
            &BoolOr(ref a, ref b) => { a.fmt_d(f)?; f.write_str(" || ")?; b.fmt_c(f) }
            &TextAppend(ref a, ref b) => { a.fmt_d(f)?; f.write_str(" ++ ")?; b.fmt_c(f) }
            &NaturalPlus(ref a, ref b) => { a.fmt_d(f)?; f.write_str(" + ")?; b.fmt_c(f) }
            &BoolAnd(ref a, ref b) => { a.fmt_d(f)?; f.write_str(" && ")?; b.fmt_c(f) }
            &Combine(ref a, ref b) => { a.fmt_d(f)?; f.write_str(" ^ ")?; b.fmt_c(f) }
            &NaturalTimes(ref a, ref b) => { a.fmt_d(f)?; f.write_str(" * ")?; b.fmt_c(f) }
            &BoolEQ(ref a, ref b) => { a.fmt_d(f)?; f.write_str(" == ")?; b.fmt_c(f) }
            &BoolNE(ref a, ref b) => { a.fmt_d(f)?; f.write_str(" != ")?; b.fmt_c(f) }
            &Note(_, ref b) => b.fmt_c(f),
            a => a.fmt_d(f),
        }
    }

    fn fmt_d(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use crate::Expr::*;
        match self {
            &App(ref a, ref b) => { a.fmt_d(f)?; f.write_str(" ")?; b.fmt_e(f) }
            &Note(_, ref b) => b.fmt_d(f),
            a => a.fmt_e(f)
        }
    }

    fn fmt_e(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use crate::Expr::*;
        match self {
            &Field(ref a, b) => { a.fmt_e(f)?; write!(f, ".{}", b) }
            &Note(_, ref b) => b.fmt_e(f),
            a => a.fmt_f(f)
        }
    }

    fn fmt_f(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use crate::Expr::*;
        match self {
            &Var(a) => a.fmt(f),
            &Const(k) => k.fmt(f),
            &Builtin(v) => v.fmt(f),
            &BoolLit(true) => f.write_str("True"),
            &BoolLit(false) => f.write_str("False"),
            &IntegerLit(a) => a.fmt(f),
            &NaturalLit(a) => {
                f.write_str("+")?;
                a.fmt(f)
            }
            &DoubleLit(a) => a.fmt(f),
            &TextLit(ref a) => <String as fmt::Debug>::fmt(a, f), // FIXME Format with Haskell escapes
            &Record(ref a) if a.is_empty() => f.write_str("{}"),
            &Record(ref a) => {
                fmt_list("{ ", " }", a, f, |(k, t), f| write!(f, "{} : {}", k, t))
            }
            &RecordLit(ref a) if a.is_empty() => f.write_str("{=}"),
            &RecordLit(ref a) => {
                fmt_list("{ ", " }", a, f, |(k, v), f| write!(f, "{} = {}", k, v))
            }
            &Union(ref _a) => f.write_str("Union"),
            &UnionLit(_a, ref _b, ref _c) => f.write_str("UnionLit"),
            &Embed(ref a) => a.fmt(f),
            &Note(_, ref b) => b.fmt_f(f),
            a => write!(f, "({})", a),
        }
    }
}

fn fmt_list<T, I, F>(open: &str,
                     close: &str,
                     it: I,
                     f: &mut fmt::Formatter,
                     func: F)
                     -> Result<(), fmt::Error>
    where I: IntoIterator<Item = T>,
          F: Fn(T, &mut fmt::Formatter) -> Result<(), fmt::Error>
{
    f.write_str(open)?;
    for (i, x) in it.into_iter().enumerate() {
        if i > 0 {
            f.write_str(", ")?;
        }
        func(x, f)?;
    }
    f.write_str(close)
}

impl Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Debug>::fmt(self, f)
    }
}

impl Display for Builtin {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use crate::Builtin::*;
        f.write_str(match *self {
            Bool     => "Bool",
            Natural  => "Natural",
            Integer  => "Integer",
            Double   => "Double",
            Text     => "Text",
            List     => "List",
            Optional => "Optional",
            NaturalFold => "Natural/fold",
            NaturalBuild => "Natural/build",
            NaturalIsZero => "Natural/isZero",
            NaturalEven => "Natural/even",
            NaturalOdd => "Natural/odd",
            NaturalShow => "Natural/show",
            ListBuild => "List/build",
            ListFold => "List/fold",
            ListLength => "List/length",
            ListHead => "List/head",
            ListLast => "List/last",
            ListIndexed => "List/indexed",
            ListReverse => "List/reverse",
            OptionalFold => "Optional/fold",
        })
    }
}

impl Builtin {
    pub fn parse(s: &str) -> Option<Self> {
        use self::Builtin::*;
        match s {
            "Bool" => Some(Bool),
            "Natural" => Some(Natural),
            "Integer" => Some(Integer),
            "Double" => Some(Double),
            "Text" => Some(Text),
            "List" => Some(List),
            "Optional" => Some(Optional),
            "Natural/fold" => Some(NaturalFold),
            "Natural/build" => Some(NaturalBuild),
            "Natural/isZero" => Some(NaturalIsZero),
            "Natural/even" => Some(NaturalEven),
            "Natural/odd" => Some(NaturalOdd),
            "Natural/show" => Some(NaturalShow),
            "List/build" => Some(ListBuild),
            "List/fold" => Some(ListFold),
            "List/length" => Some(ListLength),
            "List/head" => Some(ListHead),
            "List/last" => Some(ListLast),
            "List/indexed" => Some(ListIndexed),
            "List/reverse" => Some(ListReverse),
            "Optional/fold" => Some(OptionalFold),
            _ => None,
        }
    }
}

impl<'i> Display for V<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let V(x, n) = *self;
        f.write_str(x)?;
        if n != 0 {
            write!(f, "@{}", n)?;
        }
        Ok(())
    }
}

pub fn pi<'i, S, A, Name, Et, Ev>(var: Name, ty: Et, value: Ev) -> Expr<'i, S, A>
    where Name: Into<&'i str>,
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

impl Display for X {
    fn fmt(&self, _: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {}
    }
}

pub fn bx<T>(x: T) -> Box<T> {
    Box::new(x)
}

fn add_ui(u: usize, i: isize) -> usize {
    if i < 0 {
        u.checked_sub(i.checked_neg().unwrap() as usize).unwrap()
    } else {
        u.checked_add(i as usize).unwrap()
    }
}

fn map_record_value<'a, I, K, V, U, F>(it: I, f: F) -> BTreeMap<K, U>
    where I: IntoIterator<Item = (&'a K, &'a V)>,
          K: Eq + Ord + Copy + 'a,
          V: 'a,
          F: Fn(&V) -> U
{
    it.into_iter().map(|(&k, v)| (k, f(v))).collect()
}

fn map_op2<T, U, V, F, G>(f: F, g: G, a: T, b: T) -> V
    where F: FnOnce(U, U) -> V,
          G: Fn(T) -> U,
{
    f(g(a), g(b))
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
pub fn shift<'i, S, T, A: Clone>(d: isize, v: V, e: &Expr<'i, S, A>) -> Expr<'i, T, A> {
    use crate::Expr::*;
    let V(x, n) = v;
    match *e {
        Const(a) => Const(a),
        Var(V(x2, n2)) => {
            let n3 = if x == x2 && n <= n2 { add_ui(n2, d) } else { n2 };
            Var(V(x2, n3))
        }
        Lam(x2, ref tA, ref b) => {
            let n2 = if x == x2 { n + 1 } else { n };
            let tA2 = shift(d, V(x, n ), tA);
            let b2  = shift(d, V(x, n2), b);
            Lam(x2, bx(tA2), bx(b2))
        }
        Pi(x2, ref tA, ref tB) => {
            let n2 = if x == x2 { n + 1 } else { n };
            let tA2 = shift(d, V(x, n ), tA);
            let tB2 = shift(d, V(x, n2), tB);
            pi(x2, tA2, tB2)
        }
        App(ref f, ref a) => app(shift(d, v, f), shift(d, v, a)),
        Let(f, ref mt, ref r, ref e) => {
            let n2 = if x == f { n + 1 } else { n };
            let e2 = shift(d, V(x, n2), e);
            let mt2 = mt.as_ref().map(|t| bx(shift(d, V(x, n), t)));
            let r2  = shift(d, V(x, n), r);
            Let(f, mt2, bx(r2), bx(e2))
        }
        Annot(ref a, ref b) => shift_op2(Annot, d, v, a, b),
        Builtin(v) => Builtin(v),
        BoolLit(a) => BoolLit(a),
        BoolAnd(ref a, ref b) => shift_op2(BoolAnd, d, v, a, b),
        BoolOr(ref a, ref b) => shift_op2(BoolOr, d, v, a, b),
        BoolEQ(ref a, ref b) => shift_op2(BoolEQ, d, v, a, b),
        BoolNE(ref a, ref b) => shift_op2(BoolNE, d, v, a, b),
        BoolIf(ref a, ref b, ref c) => {
            BoolIf(bx(shift(d, v, a)), bx(shift(d, v, b)), bx(shift(d, v, c)))
        }
        NaturalLit(a) => NaturalLit(a),
        NaturalPlus(ref a, ref b) => NaturalPlus(bx(shift(d, v, a)), bx(shift(d, v, b))),
        NaturalTimes(ref a, ref b) => shift_op2(NaturalTimes, d, v, a, b),
        IntegerLit(a) => IntegerLit(a),
        DoubleLit(a) => DoubleLit(a),
        TextLit(ref a) => TextLit(a.clone()),
        TextAppend(ref a, ref b) => shift_op2(TextAppend, d, v, a, b),
        ListLit(ref t, ref es) => {
            ListLit(bx(shift(d, v, t)),
                    es.iter().map(|e| shift(d, v, e)).collect())
        }
        OptionalLit(ref t, ref es) => {
            OptionalLit(bx(shift(d, v, t)),
                        es.iter().map(|e| shift(d, v, e)).collect())
        }
        Record(ref a) => Record(map_record_value(a, |val| shift(d, v, val))),
        RecordLit(ref a) => RecordLit(map_record_value(a, |val| shift(d, v, val))),
        Union(ref a) => Union(map_record_value(a, |val| shift(d, v, val))),
        UnionLit(k, ref uv, ref a) => {
            UnionLit(k,
                     bx(shift(d, v, uv)),
                     map_record_value(a, |val| shift(d, v, val)))
        }
        Combine(ref a, ref b) => shift_op2(Combine, d, v, a, b),
        Merge(ref a, ref b, ref c) => {
            Merge(bx(shift(d, v, a)), bx(shift(d, v, b)), bx(shift(d, v, c)))
        }
        Field(ref a, b) => Field(bx(shift(d, v, a)), b),
        Note(_, ref b) => shift(d, v, b),
        // The Dhall compiler enforces that all embedded values are closed expressions
        // and `shift` does nothing to a closed expression
        Embed(ref p) => Embed(p.clone()),
        _ => panic!(),
    }
}

fn shift_op2<'i, S, T, A, F>(f: F,
                             d: isize,
                             v: V,
                             a: &Expr<'i, S, A>,
                             b: &Expr<'i, S, A>)
                             -> Expr<'i, T, A>
    where F: FnOnce(Box<Expr<'i, T, A>>, Box<Expr<'i, T, A>>) -> Expr<'i, T, A>,
          A: Clone
{
    map_op2(f, |x| bx(shift(d, v, x)), a, b)
}

/// Substitute all occurrences of a variable with an expression
///
/// ```c
/// subst x C B  ~  B[x := C]
/// ```
///
pub fn subst<'i, S, T, A>(v: V<'i>, e: &Expr<'i, S, A>, b: &Expr<'i, T, A>) -> Expr<'i, S, A>
    where S: Clone,
          A: Clone
{
    use crate::Expr::*;
    let V(x, n) = v;
    match *b {
        Const(a) => Const(a),
        Lam(y, ref tA, ref b) => {
            let n2  = if x == y { n + 1 } else { n };
            let b2  = subst(V(x, n2), &shift(1, V(y, 0), e), b);
            let tA2 = subst(V(x, n),                     e, tA);
            Lam(y, bx(tA2), bx(b2))
        }
        Pi(y, ref tA, ref tB) => {
            let n2  = if x == y { n + 1 } else { n };
            let tB2 = subst(V(x, n2), &shift(1, V(y, 0), e), tB);
            let tA2 = subst(V(x, n),                     e,  tA);
            pi(y, tA2, tB2)
        }
        App(ref f, ref a) => {
            let f2 = subst(v, e, f);
            let a2 = subst(v, e, a);
            app(f2, a2)
        }
        Var(v2) => if v == v2 { e.clone() } else { Var(v2) },
        Let(f, ref mt, ref r, ref b) => {
            let n2 = if x == f { n + 1 } else { n };
            let b2 = subst(V(x, n2), &shift(1, V(f, 0), e), b);
            let mt2 = mt.as_ref().map(|t| bx(subst(V(x, n), e, t)));
            let r2  = subst(V(x, n), e, r);
            Let(f, mt2, bx(r2), bx(b2))
        }
        Annot(ref a, ref b) => subst_op2(Annot, v, e, a, b),
        Builtin(v) => Builtin(v),
        BoolLit(a) => BoolLit(a),
        BoolAnd(ref a, ref b) => subst_op2(BoolAnd, v, e, a, b),
        BoolOr(ref a, ref b) => subst_op2(BoolOr, v, e, a, b),
        BoolEQ(ref a, ref b) => subst_op2(BoolEQ, v, e, a, b),
        BoolNE(ref a, ref b) => subst_op2(BoolNE, v, e, a, b),
        BoolIf(ref a, ref b, ref c) => {
            BoolIf(bx(subst(v, e, a)), bx(subst(v, e, b)), bx(subst(v, e, c)))
        }
        NaturalLit(a) => NaturalLit(a),
        NaturalPlus(ref a, ref b) => subst_op2(NaturalPlus, v, e, a, b),
        NaturalTimes(ref a, ref b) => subst_op2(NaturalTimes, v, e, a, b),
        IntegerLit(a) => IntegerLit(a),
        DoubleLit(a) => DoubleLit(a),
        TextLit(ref a) => TextLit(a.clone()),
        TextAppend(ref a, ref b) => subst_op2(TextAppend, v, e, a, b),
        ListLit(ref a, ref b) => {
            let a2 = subst(v, e, a);
            let b2 = b.iter().map(|be| subst(v, e, be)).collect();
            ListLit(bx(a2), b2)
        }
        OptionalLit(ref a, ref b) => {
            let a2 = subst(v, e, a);
            let b2 = b.iter().map(|be| subst(v, e, be)).collect();
            OptionalLit(bx(a2), b2)
        }
        Record(ref kts) => Record(map_record_value(kts, |t| subst(v, e, t))),
        RecordLit(ref kvs) => RecordLit(map_record_value(kvs, |val| subst(v, e, val))),
        Union(ref kts) => Union(map_record_value(kts, |t| subst(v, e, t))),
        UnionLit(k, ref uv, ref kvs) => {
            UnionLit(k,
                     bx(subst(v, e, uv)),
                     map_record_value(kvs, |val| subst(v, e, val)))
        }
        Combine(ref a, ref b) => subst_op2(Combine, v, e, a, b),
        Merge(ref a, ref b, ref c) => {
            Merge(bx(subst(v, e, a)), bx(subst(v, e, b)), bx(subst(v, e, c)))
        }
        Field(ref a, b) => Field(bx(subst(v, e, a)), b),
        Note(_, ref b) => subst(v, e, b),
        Embed(ref p) => Embed(p.clone()),
        _ => panic!(),
    }
}

fn subst_op2<'i, S, T, A, F>(f: F,
                             v: V<'i>,
                             e: &Expr<'i, S, A>,
                             a: &Expr<'i, T, A>,
                             b: &Expr<'i, T, A>)
                             -> Expr<'i, S, A>
    where F: FnOnce(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>) -> Expr<'i, S, A>,
          S: Clone,
          A: Clone
{
    map_op2(f, |x| bx(subst(v, e, x)), a, b)
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
pub fn normalize<'i, S, T, A>(e: &Expr<'i, S, A>) -> Expr<'i, T, A>
    where S: Clone + fmt::Debug,
          T: Clone + fmt::Debug,
          A: Clone + fmt::Debug,
{
    use crate::Builtin::*;
    use crate::Expr::*;
    match *e {
        Const(k) => Const(k),
        Var(v) => Var(v),
        Lam(x, ref tA, ref b) => {
            let tA2 = normalize(tA);
            let b2  = normalize(b);
            Lam(x, bx(tA2), bx(b2))
        }
        Pi(x, ref tA, ref tB) => {
            let tA2 = normalize(tA);
            let tB2 = normalize(tB);
            pi(x, tA2, tB2)
        }
        App(ref f, ref a) => match normalize::<S, T, A>(f) {
            Lam(x, _A, b) => { // Beta reduce
                let vx0 = V(x, 0);
                let a2 = shift::<S, S, A>( 1, vx0, a);
                let b2 = subst::<S, T, A>(vx0, &a2, &b);
                let b3 = shift::<S, T, A>(-1, vx0, &b2);
                normalize(&b3)
            }
            f2 => match (f2, normalize::<S, T, A>(a)) {
                // fold/build fusion for `List`
                (App(box Builtin(ListBuild), _), App(box App(box Builtin(ListFold), _), box e2)) |
                (App(box Builtin(ListFold), _), App(box App(box Builtin(ListBuild), _), box e2)) |

                // fold/build fusion for `Natural`
                (Builtin(NaturalBuild), App(box Builtin(NaturalFold), box e2)) |
                (Builtin(NaturalFold), App(box Builtin(NaturalBuild), box e2)) => normalize(&e2),

            /*
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
                (Builtin(NaturalIsZero), NaturalLit(n)) => BoolLit(n == 0),
                (Builtin(NaturalEven), NaturalLit(n)) => BoolLit(n % 2 == 0),
                (Builtin(NaturalOdd), NaturalLit(n)) => BoolLit(n % 2 != 0),
                (Builtin(NaturalShow), NaturalLit(n)) => TextLit(n.to_string()),
                (App(f@box Builtin(ListBuild), box t), k) => {
                        let labeled =
                            normalize::<_, T, _>(&app(app(app(k.clone(), app(
                                Builtin(self::Builtin::List), t.clone())), "Cons"), "Nil"));

                        fn list_to_vector<'i, S, A>(v: &mut Vec<Expr<'i, S, A>>, e: Expr<'i, S, A>)
                            where S: Clone, A: Clone
                        {
                            match e {
                                App(box App(box Var(V("Cons", _)), box x), box e2) => {
                                    v.push(x);
                                    list_to_vector(v, e2)
                                }
                                Var(V("Nil", _)) => {}
                                _ => panic!("internalError list_to_vector"),
                            }
                        }
                        fn check<S, A>(e: &Expr<S, A>) -> bool {
                            match *e {
                                App(box App(box Var(V("Cons", _)), _), ref e2) => check(e2),
                                Var(V("Nil", _)) => true,
                                _ => false,
                            }
                        }

                        if check(&labeled) {
                            let mut v = vec![];
                            list_to_vector(&mut v, labeled);
                            ListLit(bx(t), v)
                        } else {
                            app(App(f, bx(t)), k)
                        }
                    }
                (App(box App(box App(box App(box Builtin(ListFold), _), box ListLit(_, xs)), _), cons), nil) => {
                    let e2: Expr<_, _> = xs.into_iter().rev().fold(nil, |y, ys| // foldr
                        App(bx(App(cons.clone(), bx(y))), bx(ys))
                    );
                    normalize(&e2)
                }
                (App(f, x_), ListLit(t, ys)) => match *f {
                    Builtin(ListLength) =>
                        NaturalLit(ys.len()),
                    Builtin(ListHead) =>
                        normalize(&OptionalLit(t, ys.into_iter().take(1).collect())),
                    Builtin(ListLast) =>
                        normalize(&OptionalLit(t, ys.into_iter().last().into_iter().collect())),
                    Builtin(ListReverse) => {
                        let mut xs = ys;
                        xs.reverse();
                        normalize(&ListLit(t, xs))
                    }
                    _ => app(App(f, x_), ListLit(t, ys)),
                },
                /*
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
                App (App (App (App (App OptionalFold _) (OptionalLit _ xs)) _) just) nothing ->
                    normalize (maybe nothing just' (toMaybe xs))
                  where
                    just' y = App just y
                    toMaybe = Data.Maybe.listToMaybe . Data.Vector.toList
            */
                (f2, a2) => app(f2, a2),
            }
        },
        Let(f, _, ref r, ref b) => {
            let r2 = shift::<_, S, _>( 1, V(f, 0), r);
            let b2 = subst(V(f, 0), &r2, b);
            let b3 = shift::<_, T, _>(-1, V(f, 0), &b2);
            normalize(&b3)
        }
        Annot(ref x, _) => normalize(x),
        Builtin(v) => Builtin(v),
        BoolLit(b) => BoolLit(b),
        BoolAnd(ref x, ref y) => {
            with_binop(BoolAnd, Expr::bool_lit,
                       |xn, yn| BoolLit(xn && yn),
                       normalize(x), normalize(y))
        }
        BoolOr(ref x, ref y) => {
            with_binop(BoolOr, Expr::bool_lit,
                       |xn, yn| BoolLit(xn || yn),
                       normalize(x), normalize(y))
        }
        BoolEQ(ref x, ref y) => {
            with_binop(BoolEQ, Expr::bool_lit,
                       |xn, yn| BoolLit(xn == yn),
                       normalize(x), normalize(y))
        }
        BoolNE(ref x, ref y) => {
            with_binop(BoolNE, Expr::bool_lit,
                       |xn, yn| BoolLit(xn != yn),
                       normalize(x), normalize(y))
        }
        BoolIf(ref b, ref t, ref f) => match normalize(b) {
            BoolLit(true) => normalize(t),
            BoolLit(false) => normalize(f),
            b2 => BoolIf(bx(b2), bx(normalize(t)), bx(normalize(f))),
        },
        NaturalLit(n) => NaturalLit(n),
        NaturalPlus(ref x, ref y) => {
            with_binop(NaturalPlus, Expr::natural_lit,
                       |xn, yn| NaturalLit(xn + yn),
                       normalize(x), normalize(y))
        }
        NaturalTimes(ref x, ref y) => {
            with_binop(NaturalTimes, Expr::natural_lit,
                       |xn, yn| NaturalLit(xn * yn),
                       normalize(x), normalize(y))
        }
        IntegerLit(n) => IntegerLit(n),
        DoubleLit(n) => DoubleLit(n),
        TextLit(ref t) => TextLit(t.clone()),
        TextAppend(ref x, ref y) => {
            with_binop(TextAppend, Expr::text_lit,
                       |xt, yt| TextLit(xt + &yt),
                       normalize(x), normalize(y))
        }
        ListLit(ref t, ref es) => {
            let t2  = normalize(t);
            let es2 = es.iter().map(normalize).collect();
            ListLit(bx(t2), es2)
        }
        OptionalLit(ref t, ref es) => {
            let t2  = normalize(t);
            let es2 = es.iter().map(normalize).collect();
            OptionalLit(bx(t2), es2)
        }
        Record(ref kts) => Record(map_record_value(kts, normalize)),
        RecordLit(ref kvs) => RecordLit(map_record_value(kvs, normalize)),
        Union(ref kts) => Union(map_record_value(kts, normalize)),
        UnionLit(k, ref v, ref kvs) => UnionLit(k, bx(normalize(v)), map_record_value(kvs, normalize)),
        Combine(ref _x0, ref _y0) => unimplemented!(),
        Merge(ref _x, ref _y, ref _t) => unimplemented!(),
        Field(ref r, x) => match normalize(r) {
            RecordLit(kvs) => match kvs.get(x) {
                Some(r2) => normalize(r2),
                None => Field(bx(RecordLit(map_record_value(&kvs, normalize))), x),
            },
            r2 => Field(bx(r2), x),
        },
        Note(_, ref e) => normalize(e),
        Embed(ref a) => Embed(a.clone()),
        _ => panic!(),
    }
}

fn with_binop<T, U, Get, Set, Op>(op: Op, get: Get, set: Set, x: T, y: T) -> T
    where Get: Fn(&T) -> Option<U>,
          Set: FnOnce(U, U) -> T,
          Op: FnOnce(Box<T>, Box<T>) -> T,
{
    if let (Some(xv), Some(yv)) = (get(&x), get(&y)) {
        set(xv, yv)
    } else {
        op(bx(x), bx(y))
    }
}
