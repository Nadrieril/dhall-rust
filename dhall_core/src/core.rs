#![allow(non_snake_case)]
use std::collections::BTreeMap;
use std::fmt::{self, Display};
use std::path::PathBuf;
use std::rc::Rc;

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

/// The beginning of a file path which anchors subsequent path components
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FilePrefix {
    /// Absolute path
    Absolute,
    /// Path relative to .
    Here,
    /// Path relative to ..
    Parent,
    /// Path relative to ~
    Home,
}

/// The location of import (i.e. local vs. remote vs. environment)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportLocation {
    Local(FilePrefix, PathBuf),
    // TODO: other import types
}

/// How to interpret the import's contents (i.e. as Dhall code or raw text)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportMode {
    Code,
    // TODO
    // RawText,
}

/// Reference to an external resource
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Import {
    pub mode: ImportMode,
    pub location: ImportLocation,
    // TODO
    pub hash: Option<()>,
}

// The type for labels throughout the AST
// It owns the data because otherwise lifetimes would make recursive imports impossible
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Label(Rc<str>);

impl From<String> for Label {
    fn from(s: String) -> Self {
        let s: &str = &s;
        Label(s.into())
    }
}

impl From<&'static str> for Label {
    fn from(s: &'static str) -> Self {
        Label(s.into())
    }
}

impl From<Label> for String {
    fn from(x: Label) -> String {
        x.0.as_ref().to_owned()
    }
}

impl Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.0.as_ref().fmt(f)
    }
}

impl Label {
    pub fn from_str(s: &str) -> Label {
        Label(s.into())
    }
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

/// Syntax tree for expressions
#[derive(Debug, Clone, PartialEq)]
pub enum Expr<Note, Embed> {
    ///  `Const c                                  ~  c`
    Const(Const),
    ///  `Var (V x 0)                              ~  x`<br>
    ///  `Var (V x n)                              ~  x@n`
    Var(V),
    ///  `Lam x     A b                            ~  λ(x : A) -> b`
    Lam(Label, Box<Expr<Note, Embed>>, Box<Expr<Note, Embed>>),
    ///  `Pi "_" A B                               ~        A  -> B`
    ///  `Pi x   A B                               ~  ∀(x : A) -> B`
    Pi(Label, Box<Expr<Note, Embed>>, Box<Expr<Note, Embed>>),
    ///  `App f A                                  ~  f A`
    App(Box<Expr<Note, Embed>>, Box<Expr<Note, Embed>>),
    ///  `Let x Nothing  r e  ~  let x     = r in e`
    ///  `Let x (Just t) r e  ~  let x : t = r in e`
    Let(
        Label,
        Option<Box<Expr<Note, Embed>>>,
        Box<Expr<Note, Embed>>,
        Box<Expr<Note, Embed>>,
    ),
    ///  `Annot x t                                ~  x : t`
    Annot(Box<Expr<Note, Embed>>, Box<Expr<Note, Embed>>),
    /// Built-in values
    Builtin(Builtin),
    // Binary operations
    BinOp(BinOp, Box<Expr<Note, Embed>>, Box<Expr<Note, Embed>>),
    ///  `BoolLit b                                ~  b`
    BoolLit(bool),
    ///  `BoolIf x y z                             ~  if x then y else z`
    BoolIf(
        Box<Expr<Note, Embed>>,
        Box<Expr<Note, Embed>>,
        Box<Expr<Note, Embed>>,
    ),
    ///  `NaturalLit n                             ~  +n`
    NaturalLit(Natural),
    ///  `IntegerLit n                             ~  n`
    IntegerLit(Integer),
    ///  `DoubleLit n                              ~  n`
    DoubleLit(Double),
    ///  `TextLit t                                ~  t`
    TextLit(Builder),
    ///  `ListLit t [x, y, z]                      ~  [x, y, z] : List t`
    ListLit(Option<Box<Expr<Note, Embed>>>, Vec<Expr<Note, Embed>>),
    ///  `OptionalLit t [e]                        ~  [e] : Optional t`
    ///  `OptionalLit t []                         ~  []  : Optional t`
    OptionalLit(Option<Box<Expr<Note, Embed>>>, Vec<Expr<Note, Embed>>),
    ///  `Record            [(k1, t1), (k2, t2)]   ~  { k1 : t1, k2 : t1 }`
    Record(BTreeMap<Label, Expr<Note, Embed>>),
    ///  `RecordLit         [(k1, v1), (k2, v2)]   ~  { k1 = v1, k2 = v2 }`
    RecordLit(BTreeMap<Label, Expr<Note, Embed>>),
    ///  `Union             [(k1, t1), (k2, t2)]   ~  < k1 : t1, k2 : t2 >`
    Union(BTreeMap<Label, Expr<Note, Embed>>),
    ///  `UnionLit (k1, v1) [(k2, t2), (k3, t3)]   ~  < k1 = t1, k2 : t2, k3 : t3 >`
    UnionLit(
        Label,
        Box<Expr<Note, Embed>>,
        BTreeMap<Label, Expr<Note, Embed>>,
    ),
    ///  `Merge x y t                              ~  merge x y : t`
    Merge(
        Box<Expr<Note, Embed>>,
        Box<Expr<Note, Embed>>,
        Option<Box<Expr<Note, Embed>>>,
    ),
    ///  `Field e x                                ~  e.x`
    Field(Box<Expr<Note, Embed>>, Label),
    /// Annotation on the AST. Unused for now but could hold e.g. file location information
    Note(Note, Box<Expr<Note, Embed>>),
    /// Embeds an import or the result of resolving the import
    Embed(Embed),
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

impl From<Label> for V {
    fn from(s: Label) -> Self {
        V(s, 0)
    }
}

impl From<&'static str> for V {
    fn from(s: &'static str) -> Self {
        V(s.into(), 0)
    }
}

impl<S, A> From<&'static str> for Expr<S, A> {
    fn from(s: &'static str) -> Self {
        Expr::Var(V(s.into(), 0))
    }
}

impl<S, A> From<Builtin> for Expr<S, A> {
    fn from(t: Builtin) -> Self {
        Expr::Builtin(t)
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
        F2: FnOnce(&S) -> T,
        F3: FnOnce(&A) -> B,
        F4: Fn(&Label) -> Label,
    {
        map_shallow(self, map_expr, map_note, map_embed, map_label)
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

    pub fn bool_lit(&self) -> Option<bool> {
        match *self {
            Expr::BoolLit(v) => Some(v),
            _ => None,
        }
    }

    pub fn natural_lit(&self) -> Option<usize> {
        match *self {
            Expr::NaturalLit(v) => Some(v),
            _ => None,
        }
    }

    pub fn text_lit(&self) -> Option<String> {
        match *self {
            Expr::TextLit(ref t) => Some(t.clone()), // FIXME?
            _ => None,
        }
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

//  There is a one-to-one correspondence between the formatters in this section
//  and the grammar in grammar.lalrpop.  Each formatter is named after the
//  corresponding grammar rule and the relationship between formatters exactly matches
//  the relationship between grammar rules.  This leads to the nice emergent property
//  of automatically getting all the parentheses and precedences right.
//
//  This approach has one major disadvantage: you can get an infinite loop if
//  you add a new constructor to the syntax tree without adding a matching
//  case the corresponding builder.

impl<S, A: Display> Display for Expr<S, A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        // buildExprA
        use crate::Expr::*;
        match self {
            &Annot(ref a, ref b) => {
                a.fmt_b(f)?;
                write!(f, " : ")?;
                b.fmt(f)
            }
            &Note(_, ref b) => b.fmt(f),
            a => a.fmt_b(f),
        }
    }
}

impl<S, A: Display> Expr<S, A> {
    fn fmt_b(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use crate::Expr::*;
        match self {
            &Lam(ref a, ref b, ref c) => {
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
            // TODO: wait for decision on label types
            // &Pi("_", ref b, ref c) => {
            //     b.fmt_c(f)?;
            //     write!(f, " → ")?;
            //     c.fmt_b(f)
            // }
            &Pi(ref a, ref b, ref c) => {
                write!(f, "∀({} : ", a)?;
                b.fmt(f)?;
                write!(f, ") → ")?;
                c.fmt_b(f)
            }
            &Let(ref a, None, ref c, ref d) => {
                write!(f, "let {} = ", a)?;
                c.fmt(f)?;
                write!(f, ") → ")?;
                d.fmt_b(f)
            }
            &Let(ref a, Some(ref b), ref c, ref d) => {
                write!(f, "let {} : ", a)?;
                b.fmt(f)?;
                write!(f, " = ")?;
                c.fmt(f)?;
                write!(f, ") → ")?;
                d.fmt_b(f)
            }
            &ListLit(ref t, ref es) => {
                fmt_list("[", "]", es, f, |e, f| e.fmt(f))?;
                match t {
                    Some(t) => {
                        write!(f, " : List ")?;
                        t.fmt_e(f)?
                    }
                    None => {}
                }
                Ok(())
            }
            &OptionalLit(ref t, ref es) => {
                fmt_list("[", "]", es, f, |e, f| e.fmt(f))?;
                match t {
                    Some(t) => {
                        write!(f, " : Optional ")?;
                        t.fmt_e(f)?
                    }
                    None => {}
                }
                Ok(())
            }
            &Merge(ref a, ref b, ref c) => {
                write!(f, "merge ")?;
                a.fmt_e(f)?;
                write!(f, " ")?;
                b.fmt_e(f)?;
                match c {
                    Some(c) => {
                        write!(f, " : ")?;
                        c.fmt_d(f)?
                    }
                    None => {}
                }
                Ok(())
            }
            &Note(_, ref b) => b.fmt_b(f),
            a => a.fmt_c(f),
        }
    }

    fn fmt_c(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use crate::BinOp::*;
        use crate::Expr::*;
        match self {
            // FIXME precedence
            &BinOp(BoolOr, ref a, ref b) => {
                a.fmt_d(f)?;
                f.write_str(" || ")?;
                b.fmt_c(f)
            }
            &BinOp(TextAppend, ref a, ref b) => {
                a.fmt_d(f)?;
                f.write_str(" ++ ")?;
                b.fmt_c(f)
            }
            &BinOp(NaturalPlus, ref a, ref b) => {
                a.fmt_d(f)?;
                f.write_str(" + ")?;
                b.fmt_c(f)
            }
            &BinOp(BoolAnd, ref a, ref b) => {
                a.fmt_d(f)?;
                f.write_str(" && ")?;
                b.fmt_c(f)
            }
            &BinOp(Combine, ref a, ref b) => {
                a.fmt_d(f)?;
                f.write_str(" ^ ")?;
                b.fmt_c(f)
            }
            &BinOp(NaturalTimes, ref a, ref b) => {
                a.fmt_d(f)?;
                f.write_str(" * ")?;
                b.fmt_c(f)
            }
            &BinOp(BoolEQ, ref a, ref b) => {
                a.fmt_d(f)?;
                f.write_str(" == ")?;
                b.fmt_c(f)
            }
            &BinOp(BoolNE, ref a, ref b) => {
                a.fmt_d(f)?;
                f.write_str(" != ")?;
                b.fmt_c(f)
            }
            &Note(_, ref b) => b.fmt_c(f),
            a => a.fmt_d(f),
        }
    }

    fn fmt_d(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use crate::Expr::*;
        match self {
            &App(ref a, ref b) => {
                a.fmt_d(f)?;
                f.write_str(" ")?;
                b.fmt_e(f)
            }
            &Note(_, ref b) => b.fmt_d(f),
            a => a.fmt_e(f),
        }
    }

    fn fmt_e(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use crate::Expr::*;
        match self {
            &Field(ref a, ref b) => {
                a.fmt_e(f)?;
                write!(f, ".{}", b)
            }
            &Note(_, ref b) => b.fmt_e(f),
            a => a.fmt_f(f),
        }
    }

    fn fmt_f(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use crate::Expr::*;
        match &self {
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
            &Record(ref a) => fmt_list("{ ", " }", a, f, |(k, t), f| {
                write!(f, "{} : {}", k, t)
            }),
            &RecordLit(ref a) if a.is_empty() => f.write_str("{=}"),
            &RecordLit(ref a) => fmt_list("{ ", " }", a, f, |(k, v), f| {
                write!(f, "{} = {}", k, v)
            }),
            &Union(ref _a) => f.write_str("Union"),
            &UnionLit(ref _a, ref _b, ref _c) => f.write_str("UnionLit"),
            &Embed(ref a) => a.fmt(f),
            &Note(_, ref b) => b.fmt_f(f),
            a => write!(f, "({})", a),
        }
    }
}

fn fmt_list<T, I, F>(
    open: &str,
    close: &str,
    it: I,
    f: &mut fmt::Formatter,
    func: F,
) -> Result<(), fmt::Error>
where
    I: IntoIterator<Item = T>,
    F: Fn(T, &mut fmt::Formatter) -> Result<(), fmt::Error>,
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

impl Display for Import {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Debug>::fmt(self, f)
    }
}

impl Display for Builtin {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use crate::Builtin::*;
        f.write_str(match *self {
            Bool => "Bool",
            Natural => "Natural",
            Integer => "Integer",
            Double => "Double",
            Text => "Text",
            List => "List",
            Optional => "Optional",
            NaturalBuild => "Natural/build",
            NaturalFold => "Natural/fold",
            NaturalIsZero => "Natural/isZero",
            NaturalEven => "Natural/even",
            NaturalOdd => "Natural/odd",
            NaturalToInteger => "Natural/toInteger",
            NaturalShow => "Natural/show",
            IntegerToDouble => "Integer/toDouble",
            IntegerShow => "Integer/show",
            DoubleShow => "Double/show",
            ListBuild => "List/build",
            ListFold => "List/fold",
            ListLength => "List/length",
            ListHead => "List/head",
            ListLast => "List/last",
            ListIndexed => "List/indexed",
            ListReverse => "List/reverse",
            OptionalFold => "Optional/fold",
            OptionalBuild => "Optional/build",
            TextShow => "Text/show",
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
            "Natural/build" => Some(NaturalBuild),
            "Natural/fold" => Some(NaturalFold),
            "Natural/isZero" => Some(NaturalIsZero),
            "Natural/even" => Some(NaturalEven),
            "Natural/odd" => Some(NaturalOdd),
            "Natural/toInteger" => Some(NaturalToInteger),
            "Natural/show" => Some(NaturalShow),
            "Integer/toDouble" => Some(IntegerToDouble),
            "Integer/show" => Some(IntegerShow),
            "Double/show" => Some(DoubleShow),
            "List/build" => Some(ListBuild),
            "List/fold" => Some(ListFold),
            "List/length" => Some(ListLength),
            "List/head" => Some(ListHead),
            "List/last" => Some(ListLast),
            "List/indexed" => Some(ListIndexed),
            "List/reverse" => Some(ListReverse),
            "Optional/fold" => Some(OptionalFold),
            "Optional/build" => Some(OptionalBuild),
            "Text/show" => Some(TextShow),
            _ => None,
        }
    }
}

impl Display for V {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let V(ref x, ref n) = *self;
        x.fmt(f)?;
        if *n != 0 {
            write!(f, "@{}", n)?;
        }
        Ok(())
    }
}

pub fn pi<S, A, Name, Et, Ev>(var: Name, ty: Et, value: Ev) -> Expr<S, A>
where
    Name: Into<Label>,
    Et: Into<Expr<S, A>>,
    Ev: Into<Expr<S, A>>,
{
    Expr::Pi(var.into(), bx(ty.into()), bx(value.into()))
}

pub fn app<S, A, Ef, Ex>(f: Ef, x: Ex) -> Expr<S, A>
where
    Ef: Into<Expr<S, A>>,
    Ex: Into<Expr<S, A>>,
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

/// Map over the immediate children of the passed Expr
pub fn map_shallow<S, T, A, B, F1, F2, F3, F4>(
    e: &Expr<S, A>,
    map: F1,
    map_note: F2,
    map_embed: F3,
    map_label: F4,
) -> Expr<T, B>
where
    A: Clone,
    S: Clone,
    T: Clone,
    F1: Fn(&Expr<S, A>) -> Expr<T, B>,
    F2: FnOnce(&S) -> T,
    F3: FnOnce(&A) -> B,
    F4: Fn(&Label) -> Label,
{
    use crate::Expr::*;
    let bxmap = |x: &Expr<S, A>| -> Box<Expr<T, B>> { bx(map(x)) };
    let opt = |x| map_opt_box(x, &map);
    match *e {
        Const(k) => Const(k),
        Var(V(ref x, n)) => Var(V(map_label(x), n)),
        Lam(ref x, ref t, ref b) => Lam(map_label(x), bxmap(t), bxmap(b)),
        Pi(ref x, ref t, ref b) => Pi(map_label(x), bxmap(t), bxmap(b)),
        App(ref f, ref a) => App(bxmap(f), bxmap(a)),
        Let(ref l, ref t, ref a, ref b) => {
            Let(map_label(l), opt(t), bxmap(a), bxmap(b))
        }
        Annot(ref x, ref t) => Annot(bxmap(x), bxmap(t)),
        Builtin(v) => Builtin(v),
        BoolLit(b) => BoolLit(b),
        BoolIf(ref b, ref t, ref f) => BoolIf(bxmap(b), bxmap(t), bxmap(f)),
        NaturalLit(n) => NaturalLit(n),
        IntegerLit(n) => IntegerLit(n),
        DoubleLit(n) => DoubleLit(n),
        TextLit(ref t) => TextLit(t.clone()),
        BinOp(o, ref x, ref y) => BinOp(o, bxmap(x), bxmap(y)),
        ListLit(ref t, ref es) => {
            let es = es.iter().map(&map).collect();
            ListLit(opt(t), es)
        }
        OptionalLit(ref t, ref es) => {
            let es = es.iter().map(&map).collect();
            OptionalLit(opt(t), es)
        }
        Record(ref kts) => {
            Record(map_record_value_and_keys(kts, map, map_label))
        }
        RecordLit(ref kvs) => {
            RecordLit(map_record_value_and_keys(kvs, map, map_label))
        }
        Union(ref kts) => Union(map_record_value_and_keys(kts, map, map_label)),
        UnionLit(ref k, ref v, ref kvs) => UnionLit(
            map_label(k),
            bxmap(v),
            map_record_value_and_keys(kvs, map, map_label),
        ),
        Merge(ref x, ref y, ref t) => Merge(bxmap(x), bxmap(y), opt(t)),
        Field(ref r, ref x) => Field(bxmap(r), map_label(x)),
        Note(ref n, ref e) => Note(map_note(n), bxmap(e)),
        Embed(ref a) => Embed(map_embed(a)),
    }
}

pub fn map_record_value<'a, I, K, V, U, F>(it: I, f: F) -> BTreeMap<K, U>
where
    I: IntoIterator<Item = (&'a K, &'a V)>,
    K: Eq + Ord + Clone + 'a,
    V: 'a,
    F: FnMut(&V) -> U,
{
    map_record_value_and_keys(it, f, |x| x.clone())
}

pub fn map_record_value_and_keys<'a, I, K, L, V, U, F, G>(
    it: I,
    mut f: F,
    mut g: G,
) -> BTreeMap<L, U>
where
    I: IntoIterator<Item = (&'a K, &'a V)>,
    K: Eq + Ord + 'a,
    L: Eq + Ord + 'a,
    V: 'a,
    F: FnMut(&V) -> U,
    G: FnMut(&K) -> L,
{
    it.into_iter().map(|(k, v)| (g(k), f(v))).collect()
}

pub fn map_opt_box<T, U, F>(x: &Option<Box<T>>, f: F) -> Option<Box<U>>
where
    F: FnOnce(&T) -> U,
{
    x.as_ref().map(|x| x.as_ref()).map(f).map(bx)
}

fn map_op2<T, U, V, F, G>(f: F, g: G, a: T, b: T) -> V
where
    F: FnOnce(U, U) -> V,
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
pub fn shift<S, T, A: Clone>(d: isize, v: &V, e: &Expr<S, A>) -> Expr<T, A> {
    use crate::Expr::*;
    let V(x, n) = v;
    match e {
        Const(a) => Const(*a),
        Var(V(x2, n2)) => {
            let n3 = if x == x2 && n <= n2 {
                add_ui(*n2, d)
            } else {
                *n2
            };
            Var(V(x2.clone(), n3))
        }
        Lam(x2, tA, b) => {
            let n2 = if x == x2 { n + 1 } else { *n };
            let tA2 = shift(d, v, tA);
            let b2 = shift(d, &V(x.clone(), n2), b);
            Lam(x2.clone(), bx(tA2), bx(b2))
        }
        Pi(x2, tA, tB) => {
            let n2 = if x == x2 { n + 1 } else { *n };
            let tA2 = shift(d, v, tA);
            let tB2 = shift(d, &V(x.clone(), n2), tB);
            Pi(x2.clone(), bx(tA2), bx(tB2))
        }
        App(f, a) => app(shift(d, v, f), shift(d, v, a)),
        Let(f, mt, r, e) => {
            let n2 = if x == f { n + 1 } else { *n };
            let e2 = shift(d, &V(x.clone(), n2), e);
            let mt2 = mt.as_ref().map(|t| bx(shift(d, v, t)));
            let r2 = shift(d, v, r);
            Let(f.clone(), mt2, bx(r2), bx(e2))
        }
        Annot(a, b) => shift_op2(Annot, d, v, a, b),
        Builtin(v) => Builtin(*v),
        BoolLit(a) => BoolLit(*a),
        BinOp(o, a, b) => shift_op2(|x, y| BinOp(*o, x, y), d, v, a, b),
        BoolIf(a, b, c) => {
            BoolIf(bx(shift(d, v, a)), bx(shift(d, v, b)), bx(shift(d, v, c)))
        }
        NaturalLit(a) => NaturalLit(*a),
        IntegerLit(a) => IntegerLit(*a),
        DoubleLit(a) => DoubleLit(*a),
        TextLit(a) => TextLit(a.clone()),
        ListLit(t, es) => ListLit(
            t.as_ref().map(|t| bx(shift(d, v, t))),
            es.iter().map(|e| shift(d, v, e)).collect(),
        ),
        OptionalLit(t, es) => OptionalLit(
            t.as_ref().map(|t| bx(shift(d, v, t))),
            es.iter().map(|e| shift(d, v, e)).collect(),
        ),
        Record(a) => Record(map_record_value(a, |val| shift(d, v, val))),
        RecordLit(a) => RecordLit(map_record_value(a, |val| shift(d, v, val))),
        Union(a) => Union(map_record_value(a, |val| shift(d, v, val))),
        UnionLit(k, uv, a) => UnionLit(
            k.clone(),
            bx(shift(d, v, uv)),
            map_record_value(a, |val| shift(d, v, val)),
        ),
        Merge(a, b, c) => Merge(
            bx(shift(d, v, a)),
            bx(shift(d, v, b)),
            c.as_ref().map(|c| bx(shift(d, v, c))),
        ),
        Field(a, b) => Field(bx(shift(d, v, a)), b.clone()),
        Note(_, b) => shift(d, v, b),
        // The Dhall compiler enforces that all embedded values are closed expressions
        // and `shift` does nothing to a closed expression
        Embed(p) => Embed(p.clone()),
    }
}

fn shift_op2<S, T, A, F>(
    f: F,
    d: isize,
    v: &V,
    a: &Expr<S, A>,
    b: &Expr<S, A>,
) -> Expr<T, A>
where
    F: FnOnce(Box<Expr<T, A>>, Box<Expr<T, A>>) -> Expr<T, A>,
    A: Clone,
{
    map_op2(f, |x| bx(shift(d, v, x)), a, b)
}

/// Substitute all occurrences of a variable with an expression
///
/// ```c
/// subst x C B  ~  B[x := C]
/// ```
///
pub fn subst<S, T, A>(v: &V, e: &Expr<S, A>, b: &Expr<T, A>) -> Expr<S, A>
where
    S: Clone,
    A: Clone,
{
    use crate::Expr::*;
    let V(x, n) = v;
    match b {
        Const(a) => Const(*a),
        Lam(y, tA, b) => {
            let n2 = if x == y { n + 1 } else { *n };
            let b2 =
                subst(&V(x.clone(), n2), &shift(1, &V(y.clone(), 0), e), b);
            let tA2 = subst(v, e, tA);
            Lam(y.clone(), bx(tA2), bx(b2))
        }
        Pi(y, tA, tB) => {
            let n2 = if x == y { n + 1 } else { *n };
            let tB2 =
                subst(&V(x.clone(), n2), &shift(1, &V(y.clone(), 0), e), tB);
            let tA2 = subst(v, e, tA);
            Pi(y.clone(), bx(tA2), bx(tB2))
        }
        App(f, a) => {
            let f2 = subst(v, e, f);
            let a2 = subst(v, e, a);
            app(f2, a2)
        }
        Var(v2) => {
            if v == v2 {
                e.clone()
            } else {
                Var(v2.clone())
            }
        }
        Let(f, mt, r, b) => {
            let n2 = if x == f { n + 1 } else { *n };
            let b2 =
                subst(&V(x.clone(), n2), &shift(1, &V(f.clone(), 0), e), b);
            let mt2 = mt.as_ref().map(|t| bx(subst(v, e, t)));
            let r2 = subst(v, e, r);
            Let(f.clone(), mt2, bx(r2), bx(b2))
        }
        Annot(a, b) => subst_op2(Annot, v, e, a, b),
        Builtin(v) => Builtin(*v),
        BoolLit(a) => BoolLit(*a),
        BinOp(o, a, b) => subst_op2(|x, y| BinOp(*o, x, y), v, e, a, b),
        BoolIf(a, b, c) => {
            BoolIf(bx(subst(v, e, a)), bx(subst(v, e, b)), bx(subst(v, e, c)))
        }
        NaturalLit(a) => NaturalLit(*a),
        IntegerLit(a) => IntegerLit(*a),
        DoubleLit(a) => DoubleLit(*a),
        TextLit(a) => TextLit(a.clone()),
        ListLit(a, b) => {
            let a2 = a.as_ref().map(|a| bx(subst(v, e, a)));
            let b2 = b.iter().map(|be| subst(v, e, be)).collect();
            ListLit(a2, b2)
        }
        OptionalLit(a, b) => {
            let a2 = a.as_ref().map(|a| bx(subst(v, e, a)));
            let b2 = b.iter().map(|be| subst(v, e, be)).collect();
            OptionalLit(a2, b2)
        }
        Record(kts) => Record(map_record_value(kts, |t| subst(v, e, t))),
        RecordLit(kvs) => {
            RecordLit(map_record_value(kvs, |val| subst(v, e, val)))
        }
        Union(kts) => Union(map_record_value(kts, |t| subst(v, e, t))),
        UnionLit(k, uv, kvs) => UnionLit(
            k.clone(),
            bx(subst(v, e, uv)),
            map_record_value(kvs, |val| subst(v, e, val)),
        ),
        Merge(a, b, c) => Merge(
            bx(subst(v, e, a)),
            bx(subst(v, e, b)),
            c.as_ref().map(|c| bx(subst(v, e, c))),
        ),
        Field(a, b) => Field(bx(subst(v, e, a)), b.clone()),
        Note(_, b) => subst(v, e, b),
        Embed(p) => Embed(p.clone()),
    }
}

fn subst_op2<S, T, A, F>(
    f: F,
    v: &V,
    e: &Expr<S, A>,
    a: &Expr<T, A>,
    b: &Expr<T, A>,
) -> Expr<S, A>
where
    F: FnOnce(Box<Expr<S, A>>, Box<Expr<S, A>>) -> Expr<S, A>,
    S: Clone,
    A: Clone,
{
    map_op2(f, |x| bx(subst(v, e, x)), a, b)
}
