#![allow(non_snake_case)]
use std::collections::BTreeMap;
use std::fmt::{self, Display};
use std::path::PathBuf;

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
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct V<Label>(pub Label, pub usize);

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
pub type Expr<'i, S, A> = Expr_<&'i str, S, A>;
#[derive(Debug, Clone, PartialEq)]
pub enum Expr_<Label, Note, Embed> {
    ///  `Const c                                  ~  c`
    Const(Const),
    ///  `Var (V x 0)                              ~  x`<br>
    ///  `Var (V x n)                              ~  x@n`
    Var(V<Label>),
    ///  `Lam x     A b                            ~  λ(x : A) -> b`
    Lam(Label, Box<Expr_<Label, Note, Embed>>, Box<Expr_<Label, Note, Embed>>),
    ///  `Pi "_" A B                               ~        A  -> B`
    ///  `Pi x   A B                               ~  ∀(x : A) -> B`
    Pi(Label, Box<Expr_<Label, Note, Embed>>, Box<Expr_<Label, Note, Embed>>),
    ///  `App f A                                  ~  f A`
    App(Box<Expr_<Label, Note, Embed>>, Box<Expr_<Label, Note, Embed>>),
    ///  `Let x Nothing  r e  ~  let x     = r in e`
    ///  `Let x (Just t) r e  ~  let x : t = r in e`
    Let(
        Label,
        Option<Box<Expr_<Label, Note, Embed>>>,
        Box<Expr_<Label, Note, Embed>>,
        Box<Expr_<Label, Note, Embed>>,
    ),
    ///  `Annot x t                                ~  x : t`
    Annot(Box<Expr_<Label, Note, Embed>>, Box<Expr_<Label, Note, Embed>>),
    /// Built-in values
    Builtin(Builtin),
    // Binary operations
    BinOp(BinOp, Box<Expr_<Label, Note, Embed>>, Box<Expr_<Label, Note, Embed>>),
    ///  `BoolLit b                                ~  b`
    BoolLit(bool),
    ///  `BoolIf x y z                             ~  if x then y else z`
    BoolIf(
        Box<Expr_<Label, Note, Embed>>,
        Box<Expr_<Label, Note, Embed>>,
        Box<Expr_<Label, Note, Embed>>,
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
    ListLit(Option<Box<Expr_<Label, Note, Embed>>>, Vec<Expr_<Label, Note, Embed>>),
    ///  `OptionalLit t [e]                        ~  [e] : Optional t`
    ///  `OptionalLit t []                         ~  []  : Optional t`
    OptionalLit(Option<Box<Expr_<Label, Note, Embed>>>, Vec<Expr_<Label, Note, Embed>>),
    ///  `Record            [(k1, t1), (k2, t2)]   ~  { k1 : t1, k2 : t1 }`
    Record(BTreeMap<Label, Expr_<Label, Note, Embed>>),
    ///  `RecordLit         [(k1, v1), (k2, v2)]   ~  { k1 = v1, k2 = v2 }`
    RecordLit(BTreeMap<Label, Expr_<Label, Note, Embed>>),
    ///  `Union             [(k1, t1), (k2, t2)]   ~  < k1 : t1, k2 : t2 >`
    Union(BTreeMap<Label, Expr_<Label, Note, Embed>>),
    ///  `UnionLit (k1, v1) [(k2, t2), (k3, t3)]   ~  < k1 = t1, k2 : t2, k3 : t3 >`
    UnionLit(
        Label,
        Box<Expr_<Label, Note, Embed>>,
        BTreeMap<Label, Expr_<Label, Note, Embed>>,
    ),
    ///  `Merge x y t                              ~  merge x y : t`
    Merge(
        Box<Expr_<Label, Note, Embed>>,
        Box<Expr_<Label, Note, Embed>>,
        Option<Box<Expr_<Label, Note, Embed>>>,
    ),
    ///  `Field e x                                ~  e.x`
    Field(Box<Expr_<Label, Note, Embed>>, Label),
    /// Annotation on the AST. Unused for now but could hold e.g. file location information
    Note(Note, Box<Expr_<Label, Note, Embed>>),
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

impl<'i> From<&'i str> for V<&'i str> {
    fn from(s: &'i str) -> Self {
        V(s, 0)
    }
}

impl<'i, S, A> From<&'i str> for Expr<'i, S, A> {
    fn from(s: &'i str) -> Self {
        Expr_::Var(s.into())
    }
}

impl<'i, S, A> From<Builtin> for Expr<'i, S, A> {
    fn from(t: Builtin) -> Self {
        Expr_::Builtin(t)
    }
}

impl<'i, S, A> Expr<'i, S, A> {
    pub fn map_shallow<T, B, F1, F2, F3>(
        &self,
        map_expr: F1,
        map_note: F2,
        map_embed: F3,
    ) -> Expr<'i, T, B>
    where
        A: Clone,
        T: Clone,
        S: Clone,
        F1: Fn(&Self) -> Expr<'i, T, B>,
        F2: FnOnce(&S) -> T,
        F3: FnOnce(&A) -> B,
    {
        map_shallow(self, map_expr, map_note, map_embed)
    }

    pub fn map_embed<B, F>(&self, map_embed: &F) -> Expr<'i, S, B>
    where
        A: Clone,
        S: Clone,
        F: Fn(&A) -> B,
    {
        let recurse =
            |e: &Expr<'i, S, A>| -> Expr<'i, S, B> { e.map_embed(map_embed) };
        map_shallow(self, recurse, |x| x.clone(), map_embed)
    }

    pub fn bool_lit(&self) -> Option<bool> {
        match *self {
            Expr_::BoolLit(v) => Some(v),
            _ => None,
        }
    }

    pub fn natural_lit(&self) -> Option<usize> {
        match *self {
            Expr_::NaturalLit(v) => Some(v),
            _ => None,
        }
    }

    pub fn text_lit(&self) -> Option<String> {
        match *self {
            Expr_::TextLit(ref t) => Some(t.clone()), // FIXME?
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
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        // buildExprA
        use crate::Expr_::*;
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

impl<'i, S, A: Display> Expr<'i, S, A> {
    fn fmt_b(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use crate::Expr_::*;
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
        use crate::Expr_::*;
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
        use crate::Expr_::*;
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
        use crate::Expr_::*;
        match self {
            &Field(ref a, b) => {
                a.fmt_e(f)?;
                write!(f, ".{}", b)
            }
            &Note(_, ref b) => b.fmt_e(f),
            a => a.fmt_f(f),
        }
    }

    fn fmt_f(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use crate::Expr_::*;
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
            &Record(ref a) => fmt_list("{ ", " }", a, f, |(k, t), f| {
                write!(f, "{} : {}", k, t)
            }),
            &RecordLit(ref a) if a.is_empty() => f.write_str("{=}"),
            &RecordLit(ref a) => fmt_list("{ ", " }", a, f, |(k, v), f| {
                write!(f, "{} = {}", k, v)
            }),
            &Union(ref _a) => f.write_str("Union"),
            &UnionLit(_a, ref _b, ref _c) => f.write_str("UnionLit"),
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

impl<'i> Display for V<&'i str> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let V(x, n) = *self;
        f.write_str(x)?;
        if n != 0 {
            write!(f, "@{}", n)?;
        }
        Ok(())
    }
}

pub fn pi<'i, S, A, Name, Et, Ev>(
    var: Name,
    ty: Et,
    value: Ev,
) -> Expr<'i, S, A>
where
    Name: Into<&'i str>,
    Et: Into<Expr<'i, S, A>>,
    Ev: Into<Expr<'i, S, A>>,
{
    Expr_::Pi(var.into(), bx(ty.into()), bx(value.into()))
}

pub fn app<'i, S, A, Ef, Ex>(f: Ef, x: Ex) -> Expr<'i, S, A>
where
    Ef: Into<Expr<'i, S, A>>,
    Ex: Into<Expr<'i, S, A>>,
{
    Expr_::App(bx(f.into()), bx(x.into()))
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

pub fn map_shallow<'i, S, T, A, B, F1, F2, F3>(
    e: &Expr<'i, S, A>,
    map: F1,
    map_note: F2,
    map_embed: F3,
) -> Expr<'i, T, B>
where
    A: Clone,
    S: Clone,
    T: Clone,
    F1: Fn(&Expr<'i, S, A>) -> Expr<'i, T, B>,
    F2: FnOnce(&S) -> T,
    F3: FnOnce(&A) -> B,
{
    use crate::Expr_::*;
    let bxmap = |x: &Expr<'i, S, A>| -> Box<Expr<'i, T, B>> { bx(map(x)) };
    let opt = |x| map_opt_box(x, &map);
    match *e {
        Const(k) => Const(k),
        Var(v) => Var(v),
        Lam(x, ref t, ref b) => Lam(x, bxmap(t), bxmap(b)),
        Pi(x, ref t, ref b) => Pi(x, bxmap(t), bxmap(b)),
        App(ref f, ref a) => App(bxmap(f), bxmap(a)),
        Let(l, ref t, ref a, ref b) => Let(l, opt(t), bxmap(a), bxmap(b)),
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
        Record(ref kts) => Record(map_record_value(kts, map)),
        RecordLit(ref kvs) => RecordLit(map_record_value(kvs, map)),
        Union(ref kts) => Union(map_record_value(kts, map)),
        UnionLit(k, ref v, ref kvs) => {
            UnionLit(k, bxmap(v), map_record_value(kvs, map))
        }
        Merge(ref x, ref y, ref t) => Merge(bxmap(x), bxmap(y), opt(t)),
        Field(ref r, x) => Field(bxmap(r), x),
        Note(ref n, ref e) => Note(map_note(n), bxmap(e)),
        Embed(ref a) => Embed(map_embed(a)),
    }
}

pub fn map_record_value<'a, I, K, V, U, F>(it: I, mut f: F) -> BTreeMap<K, U>
where
    I: IntoIterator<Item = (&'a K, &'a V)>,
    K: Eq + Ord + Copy + 'a,
    V: 'a,
    F: FnMut(&V) -> U,
{
    it.into_iter().map(|(&k, v)| (k, f(v))).collect()
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
pub fn shift<'i, S, T, A: Clone>(
    d: isize,
    v: V<&'i str>,
    e: &Expr<'i, S, A>,
) -> Expr<'i, T, A> {
    use crate::Expr_::*;
    let V(x, n) = v;
    match *e {
        Const(a) => Const(a),
        Var(V(x2, n2)) => {
            let n3 = if x == x2 && n <= n2 {
                add_ui(n2, d)
            } else {
                n2
            };
            Var(V(x2, n3))
        }
        Lam(x2, ref tA, ref b) => {
            let n2 = if x == x2 { n + 1 } else { n };
            let tA2 = shift(d, V(x, n), tA);
            let b2 = shift(d, V(x, n2), b);
            Lam(x2, bx(tA2), bx(b2))
        }
        Pi(x2, ref tA, ref tB) => {
            let n2 = if x == x2 { n + 1 } else { n };
            let tA2 = shift(d, V(x, n), tA);
            let tB2 = shift(d, V(x, n2), tB);
            pi(x2, tA2, tB2)
        }
        App(ref f, ref a) => app(shift(d, v, f), shift(d, v, a)),
        Let(f, ref mt, ref r, ref e) => {
            let n2 = if x == f { n + 1 } else { n };
            let e2 = shift(d, V(x, n2), e);
            let mt2 = mt.as_ref().map(|t| bx(shift(d, V(x, n), t)));
            let r2 = shift(d, V(x, n), r);
            Let(f, mt2, bx(r2), bx(e2))
        }
        Annot(ref a, ref b) => shift_op2(Annot, d, v, a, b),
        Builtin(v) => Builtin(v),
        BoolLit(a) => BoolLit(a),
        BinOp(o, ref a, ref b) => shift_op2(|x, y| BinOp(o, x, y), d, v, a, b),
        BoolIf(ref a, ref b, ref c) => {
            BoolIf(bx(shift(d, v, a)), bx(shift(d, v, b)), bx(shift(d, v, c)))
        }
        NaturalLit(a) => NaturalLit(a),
        IntegerLit(a) => IntegerLit(a),
        DoubleLit(a) => DoubleLit(a),
        TextLit(ref a) => TextLit(a.clone()),
        ListLit(ref t, ref es) => ListLit(
            t.as_ref().map(|t| bx(shift(d, v, t))),
            es.iter().map(|e| shift(d, v, e)).collect(),
        ),
        OptionalLit(ref t, ref es) => OptionalLit(
            t.as_ref().map(|t| bx(shift(d, v, t))),
            es.iter().map(|e| shift(d, v, e)).collect(),
        ),
        Record(ref a) => Record(map_record_value(a, |val| shift(d, v, val))),
        RecordLit(ref a) => {
            RecordLit(map_record_value(a, |val| shift(d, v, val)))
        }
        Union(ref a) => Union(map_record_value(a, |val| shift(d, v, val))),
        UnionLit(k, ref uv, ref a) => UnionLit(
            k,
            bx(shift(d, v, uv)),
            map_record_value(a, |val| shift(d, v, val)),
        ),
        Merge(ref a, ref b, ref c) => Merge(
            bx(shift(d, v, a)),
            bx(shift(d, v, b)),
            c.as_ref().map(|c| bx(shift(d, v, c))),
        ),
        Field(ref a, b) => Field(bx(shift(d, v, a)), b),
        Note(_, ref b) => shift(d, v, b),
        // The Dhall compiler enforces that all embedded values are closed expressions
        // and `shift` does nothing to a closed expression
        Embed(ref p) => Embed(p.clone()),
    }
}

fn shift_op2<'i, S, T, A, F>(
    f: F,
    d: isize,
    v: V<&'i str>,
    a: &Expr<'i, S, A>,
    b: &Expr<'i, S, A>,
) -> Expr<'i, T, A>
where
    F: FnOnce(Box<Expr<'i, T, A>>, Box<Expr<'i, T, A>>) -> Expr<'i, T, A>,
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
pub fn subst<'i, S, T, A>(
    v: V<&'i str>,
    e: &Expr<'i, S, A>,
    b: &Expr<'i, T, A>,
) -> Expr<'i, S, A>
where
    S: Clone,
    A: Clone,
{
    use crate::Expr_::*;
    let V(x, n) = v;
    match *b {
        Const(a) => Const(a),
        Lam(y, ref tA, ref b) => {
            let n2 = if x == y { n + 1 } else { n };
            let b2 = subst(V(x, n2), &shift(1, V(y, 0), e), b);
            let tA2 = subst(V(x, n), e, tA);
            Lam(y, bx(tA2), bx(b2))
        }
        Pi(y, ref tA, ref tB) => {
            let n2 = if x == y { n + 1 } else { n };
            let tB2 = subst(V(x, n2), &shift(1, V(y, 0), e), tB);
            let tA2 = subst(V(x, n), e, tA);
            pi(y, tA2, tB2)
        }
        App(ref f, ref a) => {
            let f2 = subst(v, e, f);
            let a2 = subst(v, e, a);
            app(f2, a2)
        }
        Var(v2) => {
            if v == v2 {
                e.clone()
            } else {
                Var(v2)
            }
        }
        Let(f, ref mt, ref r, ref b) => {
            let n2 = if x == f { n + 1 } else { n };
            let b2 = subst(V(x, n2), &shift(1, V(f, 0), e), b);
            let mt2 = mt.as_ref().map(|t| bx(subst(V(x, n), e, t)));
            let r2 = subst(V(x, n), e, r);
            Let(f, mt2, bx(r2), bx(b2))
        }
        Annot(ref a, ref b) => subst_op2(Annot, v, e, a, b),
        Builtin(v) => Builtin(v),
        BoolLit(a) => BoolLit(a),
        BinOp(o, ref a, ref b) => subst_op2(|x, y| BinOp(o, x, y), v, e, a, b),
        BoolIf(ref a, ref b, ref c) => {
            BoolIf(bx(subst(v, e, a)), bx(subst(v, e, b)), bx(subst(v, e, c)))
        }
        NaturalLit(a) => NaturalLit(a),
        IntegerLit(a) => IntegerLit(a),
        DoubleLit(a) => DoubleLit(a),
        TextLit(ref a) => TextLit(a.clone()),
        ListLit(ref a, ref b) => {
            let a2 = a.as_ref().map(|a| bx(subst(v, e, a)));
            let b2 = b.iter().map(|be| subst(v, e, be)).collect();
            ListLit(a2, b2)
        }
        OptionalLit(ref a, ref b) => {
            let a2 = a.as_ref().map(|a| bx(subst(v, e, a)));
            let b2 = b.iter().map(|be| subst(v, e, be)).collect();
            OptionalLit(a2, b2)
        }
        Record(ref kts) => Record(map_record_value(kts, |t| subst(v, e, t))),
        RecordLit(ref kvs) => {
            RecordLit(map_record_value(kvs, |val| subst(v, e, val)))
        }
        Union(ref kts) => Union(map_record_value(kts, |t| subst(v, e, t))),
        UnionLit(k, ref uv, ref kvs) => UnionLit(
            k,
            bx(subst(v, e, uv)),
            map_record_value(kvs, |val| subst(v, e, val)),
        ),
        Merge(ref a, ref b, ref c) => Merge(
            bx(subst(v, e, a)),
            bx(subst(v, e, b)),
            c.as_ref().map(|c| bx(subst(v, e, c))),
        ),
        Field(ref a, b) => Field(bx(subst(v, e, a)), b),
        Note(_, ref b) => subst(v, e, b),
        Embed(ref p) => Embed(p.clone()),
    }
}

fn subst_op2<'i, S, T, A, F>(
    f: F,
    v: V<&'i str>,
    e: &Expr<'i, S, A>,
    a: &Expr<'i, T, A>,
    b: &Expr<'i, T, A>,
) -> Expr<'i, S, A>
where
    F: FnOnce(Box<Expr<'i, S, A>>, Box<Expr<'i, S, A>>) -> Expr<'i, S, A>,
    S: Clone,
    A: Clone,
{
    map_op2(f, |x| bx(subst(v, e, x)), a, b)
}
