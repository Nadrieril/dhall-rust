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
#[derive(Debug, PartialEq, Eq)] // (Show, Bounded, Enum)
pub enum Const {
    Type,
    Kind,
}


/// Path to an external resource
#[derive(Debug, PartialEq, Eq)] // (Eq, Ord, Show)
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
#[derive(Debug, PartialEq, Eq)] // (Eq, Show)
pub struct Var(pub String, pub Int);

/*
instance IsString Var where
    fromString str = V (fromString str) 0

instance Buildable Var where
    build = buildVar
*/

/// Syntax tree for expressions
#[derive(Debug, PartialEq)] // (Functor, Foldable, Traversable, Show)
pub enum Expr<S, A> {
    ///  `Const c                                  ~  c`
    Const(Const),
    ///  `Var (V x 0)                              ~  x`<br>
    ///  `Var (V x n)                              ~  x@n`
    Var(Var),
    ///  `Lam x     A b                            ~  λ(x : A) -> b`
    Lam(String, Box<Expr<S, A>>, Box<Expr<S, A>>),
    ///  `Pi "_" A B                               ~        A  -> B`
    ///  `Pi x   A B                               ~  ∀(x : A) -> B`
    Pi(String, Box<Expr<S, A>>, Box<Expr<S, A>>),
    ///  `App f A                                  ~  f A`
    App(Box<Expr<S, A>>, Box<Expr<S, A>>),
    ///  `Let x Nothing  r e  ~  let x     = r in e`
    ///  `Let x (Just t) r e  ~  let x : t = r in e`
    Let(String, Option<Box<Expr<S, A>>>, Box<Expr<S, A>>, Box<Expr<S, A>>),
    ///  `Annot x t                                ~  x : t`
    Annot(Box<Expr<S, A>>, Box<Expr<S, A>>),
    ///  `Bool                                     ~  Bool`
    Bool,
    ///  `BoolLit b                                ~  b`
    BoolLit(bool),
    ///  `BoolAnd x y                              ~  x && y`
    BoolAnd(Box<Expr<S, A>>, Box<Expr<S, A>>),
    ///  `BoolOr  x y                              ~  x || y`
    BoolOr(Box<Expr<S, A>>, Box<Expr<S, A>>),
    ///  `BoolEQ  x y                              ~  x == y`
    BoolEQ(Box<Expr<S, A>>, Box<Expr<S, A>>),
    ///  `BoolNE  x y                              ~  x != y`
    BoolNE(Box<Expr<S, A>>, Box<Expr<S, A>>),
    ///  `BoolIf x y z                             ~  if x then y else z`
    BoolIf(Box<Expr<S, A>>, Box<Expr<S, A>>, Box<Expr<S, A>>),
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
    NaturalPlus(Box<Expr<S, A>>, Box<Expr<S, A>>),
    ///  `NaturalTimes x y                         ~  x * y`
    NaturalTimes(Box<Expr<S, A>>, Box<Expr<S, A>>),
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
    TextAppend(Box<Expr<S, A>>, Box<Expr<S, A>>),
    ///  `List                                     ~  List`
    List,
    ///  `ListLit t [x, y, z]                      ~  [x, y, z] : List t`
    ListLit(Box<Expr<S, A>>, Vec<Expr<S, A>>),
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
    OptionalLit(Box<Expr<S, A>>, Vec<Expr<S, A>>),
    ///  `OptionalFold                             ~  Optional/fold`
    OptionalFold,
    ///  `Record            [(k1, t1), (k2, t2)]   ~  { k1 : t1, k2 : t1 }`
    Record(HashMap<String, Expr<S, A>>),
    ///  `RecordLit         [(k1, v1), (k2, v2)]   ~  { k1 = v1, k2 = v2 }`
    RecordLit(HashMap<String, Expr<S, A>>),
    ///  `Union             [(k1, t1), (k2, t2)]   ~  < k1 : t1, k2 : t2 >`
    Union(HashMap<String, Expr<S, A>>),
    ///  `UnionLit (k1, v1) [(k2, t2), (k3, t3)]   ~  < k1 = t1, k2 : t2, k3 : t3 >`
    UnionLit(String, Box<Expr<S, A>>, HashMap<String, Expr<S, A>>),
    ///  `Combine x y                              ~  x ∧ y`
    Combine(Box<Expr<S, A>>, Box<Expr<S, A>>),
    ///  `Merge x y t                              ~  merge x y : t`
    Merge(Box<Expr<S, A>>, Box<Expr<S, A>>, Box<Expr<S, A>>),
    ///  `Field e x                                ~  e.x`
    Field(Box<Expr<S, A>>, String),
    ///  `Note S x                                 ~  e`
    Note(S, Box<Expr<S, A>>),
    ///  `Embed path                               ~  path`
    Embed(A),
}

pub type Builder = String;
pub type Double = f64;
pub type Int = isize;
pub type Integer = isize;
pub type Natural = usize;
