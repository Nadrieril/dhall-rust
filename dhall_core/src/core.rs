#![allow(non_snake_case)]
use std::collections::BTreeMap;
use std::fmt::{self, Display};
use std::iter::FromIterator;
use std::ops::Add;
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

impl<'a> From<&'a str> for Label {
    fn from(s: &'a str) -> Self {
        Label(Rc::from(s))
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

#[derive(Debug, Clone, PartialEq)]
pub struct InterpolatedText<Note, Embed> {
    head: String,
    tail: Vec<(Rc<Expr<Note, Embed>>, String)>,
}

impl<N, E> From<(String, Vec<(Rc<Expr<N, E>>, String)>)>
    for InterpolatedText<N, E>
{
    fn from(x: (String, Vec<(Rc<Expr<N, E>>, String)>)) -> Self {
        InterpolatedText {
            head: x.0,
            tail: x.1,
        }
    }
}

impl<N, E> From<String> for InterpolatedText<N, E> {
    fn from(s: String) -> Self {
        InterpolatedText {
            head: s,
            tail: vec![],
        }
    }
}

pub enum InterpolatedTextContents<'a, Note, Embed> {
    Text(&'a str),
    Expr(SubExpr<Note, Embed>),
}

impl<N, E> InterpolatedText<N, E> {
    pub fn map<N2, E2, F>(&self, mut f: F) -> InterpolatedText<N2, E2>
    where
        F: FnMut(&Rc<Expr<N, E>>) -> Rc<Expr<N2, E2>>,
    {
        InterpolatedText {
            head: self.head.clone(),
            tail: self.tail.iter().map(|(e, s)| (f(e), s.clone())).collect(),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = InterpolatedTextContents<N, E>> {
        use std::iter::once;
        once(InterpolatedTextContents::Text(self.head.as_ref())).chain(
            self.tail.iter().flat_map(|(e, s)| {
                once(InterpolatedTextContents::Expr(Rc::clone(e)))
                    .chain(once(InterpolatedTextContents::Text(s)))
            }),
        )
    }
}

impl<'a, N: 'a, E: 'a> FromIterator<InterpolatedTextContents<'a, N, E>>
    for InterpolatedText<N, E>
{
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = InterpolatedTextContents<'a, N, E>>,
    {
        let mut res = InterpolatedText {
            head: "".to_owned(),
            tail: vec![],
        };
        // let mut empty_string = "".to_owned();
        let mut crnt_str = &mut res.head;
        for x in iter.into_iter() {
            match x {
                InterpolatedTextContents::Text(s) => crnt_str.push_str(s),
                InterpolatedTextContents::Expr(e) => {
                    // crnt_str = &mut empty_string;
                    res.tail.push((e.clone(), "".to_owned()));
                    crnt_str = &mut res.tail.last_mut().unwrap().1;
                }
            }
        }
        res
    }
}

impl<N, E> Add for &InterpolatedText<N, E> {
    type Output = InterpolatedText<N, E>;
    fn add(self, rhs: &InterpolatedText<N, E>) -> Self::Output {
        self.iter().chain(rhs.iter()).collect()
    }
}

pub type SubExpr<Note, Embed> = Rc<Expr<Note, Embed>>;

/// Syntax tree for expressions
#[derive(Debug, Clone, PartialEq)]
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
    ///  `OptionalLit t [e]                        ~  [e] : Optional t`
    ///  `OptionalLit t []                         ~  []  : Optional t`
    OptionalLit(Option<SubExpr<Note, Embed>>, Option<SubExpr<Note, Embed>>),
    ///  `Record            [(k1, t1), (k2, t2)]   ~  { k1 : t1, k2 : t1 }`
    Record(BTreeMap<Label, SubExpr<Note, Embed>>),
    ///  `RecordLit         [(k1, v1), (k2, v2)]   ~  { k1 = v1, k2 = v2 }`
    RecordLit(BTreeMap<Label, SubExpr<Note, Embed>>),
    ///  `Union             [(k1, t1), (k2, t2)]   ~  < k1 : t1, k2 : t2 >`
    Union(BTreeMap<Label, SubExpr<Note, Embed>>),
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

// WARNING: this may cause stack overflows when adding new variants
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
                write!(f, " in ")?;
                d.fmt_b(f)
            }
            &Let(ref a, Some(ref b), ref c, ref d) => {
                write!(f, "let {} : ", a)?;
                b.fmt(f)?;
                write!(f, " = ")?;
                c.fmt(f)?;
                write!(f, " in ")?;
                d.fmt_b(f)
            }
            &EmptyListLit(ref t) => {
                write!(f, "[] : List ")?;
                t.fmt_e(f)
            }
            &NEListLit(ref es) => {
                fmt_list("[", ", ", "]", es, f, |e, f| e.fmt(f))
            }
            &OptionalLit(ref t, ref es) => {
                match es {
                    None => {
                        // TODO: use None when parsing fixed
                        write!(f, "[] : Optional ")?;
                        t.as_ref().unwrap().fmt_e(f)?;
                    }
                    Some(e) => {
                        // TODO: use Some when parsing fixed
                        write!(f, "[ ")?;
                        e.fmt_e(f)?;
                        write!(f, " ]")?;
                        if let Some(t) = t {
                            write!(f, " : Optional ")?;
                            t.fmt_e(f)?;
                        }
                    }
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
            &BinOp(op, ref a, ref b) => {
                write!(f, "(")?;
                a.fmt_d(f)?;
                write!(
                    f,
                    " {} ",
                    match op {
                        BoolOr => "||",
                        TextAppend => "++",
                        NaturalPlus => "+",
                        BoolAnd => "&&",
                        Combine => "/\\",
                        NaturalTimes => "*",
                        BoolEQ => "==",
                        BoolNE => "!=",
                        CombineTypes => "//\\\\",
                        ImportAlt => "?",
                        Prefer => "//",
                        ListAppend => "#",
                    }
                )?;
                b.fmt_c(f)?;
                write!(f, ")")
            }
            &Note(_, ref b) => b.fmt_c(f),
            a => a.fmt_d(f),
        }
    }

    fn fmt_d(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use crate::Expr::*;
        match self {
            &App(ref a, ref args) => {
                a.fmt_d(f)?;
                for x in args {
                    f.write_str(" ")?;
                    x.fmt_e(f)?;
                }
                Ok(())
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
            &NaturalLit(a) => a.fmt(f),
            &IntegerLit(a) if *a >= 0 => {
                f.write_str("+")?;
                a.fmt(f)
            }
            &IntegerLit(a) => a.fmt(f),
            &DoubleLit(a) => a.fmt(f),
            &TextLit(ref a) => {
                f.write_str("\"")?;
                for x in a.iter() {
                    match x {
                        InterpolatedTextContents::Text(a) => {
                            // TODO Format all escapes properly
                            f.write_str(
                                &a.replace("\n", "\\n")
                                    .replace("\t", "\\t")
                                    .replace("\r", "\\r")
                                    .replace("\"", "\\\""),
                            )?;
                        }
                        InterpolatedTextContents::Expr(e) => {
                            f.write_str("${ ")?;
                            e.fmt(f)?;
                            f.write_str(" }")?;
                        }
                    }
                }
                f.write_str("\"")?;
                Ok(())
            }
            &Record(ref a) if a.is_empty() => f.write_str("{}"),
            &Record(ref a) => fmt_list("{ ", ", ", " }", a, f, |(k, t), f| {
                write!(f, "{} : {}", k, t)
            }),
            &RecordLit(ref a) if a.is_empty() => f.write_str("{=}"),
            &RecordLit(ref a) => {
                fmt_list("{ ", ", ", " }", a, f, |(k, v), f| {
                    write!(f, "{} = {}", k, v)
                })
            }
            &Union(ref a) => fmt_list("< ", " | ", " >", a, f, |(k, v), f| {
                write!(f, "{} : {}", k, v)
            }),
            &UnionLit(ref a, ref b, ref c) => {
                f.write_str("< ")?;
                write!(f, "{} = {}", a, b)?;
                for (k, v) in c {
                    f.write_str(" | ")?;
                    write!(f, "{} : {}", k, v)?;
                }
                f.write_str(" >")
            }
            &Embed(ref a) => a.fmt(f),
            &Note(_, ref b) => b.fmt_f(f),
            a => write!(f, "({})", a),
        }
    }
}

fn fmt_list<T, I, F>(
    open: &str,
    sep: &str,
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
            f.write_str(sep)?;
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
            OptionalSome => "Some",
            OptionalNone => "None",
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
            "Some" => Some(OptionalSome),
            "None" => Some(OptionalNone),
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

pub fn app<S, A, Ef>(f: Ef, x: Vec<Rc<Expr<S, A>>>) -> Expr<S, A>
where
    Ef: Into<Expr<S, A>>,
{
    Expr::App(bx(f.into()), x)
}

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
        OptionalLit(t, es) => OptionalLit(opt(t), opt(es)),
        Record(kts) => Record(btmap(kts)),
        RecordLit(kvs) => RecordLit(btmap(kvs)),
        Union(kts) => Union(btmap(kts)),
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
