use crate::*;
use itertools::Itertools;
use std::fmt::{self, Display};

/// Generic instance that delegates to subexpressions
impl<SE: Display + Clone, E: Display> Display for ExprF<SE, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use crate::ExprF::*;
        match self {
            Lam(a, b, c) => {
                write!(f, "λ({} : {}) → {}", a, b, c)?;
            }
            BoolIf(a, b, c) => {
                write!(f, "if {} then {} else {}", a, b, c)?;
            }
            Pi(a, b, c) if &String::from(a) == "_" => {
                write!(f, "{} → {}", b, c)?;
            }
            Pi(a, b, c) => {
                write!(f, "∀({} : {}) → {}", a, b, c)?;
            }
            Let(a, b, c, d) => {
                write!(f, "let {}", a)?;
                if let Some(b) = b {
                    write!(f, " : {}", b)?;
                }
                write!(f, " = {} in {}", c, d)?;
            }
            EmptyListLit(t) => {
                write!(f, "[] : {}", t)?;
            }
            NEListLit(es) => {
                fmt_list("[", ", ", "]", es, f, Display::fmt)?;
            }
            SomeLit(e) => {
                write!(f, "Some {}", e)?;
            }
            Merge(a, b, c) => {
                write!(f, "merge {} {}", a, b)?;
                if let Some(c) = c {
                    write!(f, " : {}", c)?;
                }
            }
            Annot(a, b) => {
                write!(f, "{} : {}", a, b)?;
            }
            Assert(a) => {
                write!(f, "assert : {}", a)?;
            }
            ExprF::BinOp(op, a, b) => {
                write!(f, "{} {} {}", a, op, b)?;
            }
            ExprF::App(a, b) => {
                write!(f, "{} {}", a, b)?;
            }
            Field(a, b) => {
                write!(f, "{}.{}", a, b)?;
            }
            Projection(e, ls) => {
                write!(f, "{}.", e)?;
                fmt_list("{ ", ", ", " }", ls, f, Display::fmt)?;
            }
            Var(a) => a.fmt(f)?,
            Const(k) => k.fmt(f)?,
            Builtin(v) => v.fmt(f)?,
            BoolLit(true) => f.write_str("True")?,
            BoolLit(false) => f.write_str("False")?,
            NaturalLit(a) => a.fmt(f)?,
            IntegerLit(a) if *a >= 0 => {
                f.write_str("+")?;
                a.fmt(f)?;
            }
            IntegerLit(a) => a.fmt(f)?,
            DoubleLit(a) => a.fmt(f)?,
            TextLit(a) => a.fmt(f)?,
            RecordType(a) if a.is_empty() => f.write_str("{}")?,
            RecordType(a) => fmt_list("{ ", ", ", " }", a, f, |(k, t), f| {
                write!(f, "{} : {}", k, t)
            })?,
            RecordLit(a) if a.is_empty() => f.write_str("{=}")?,
            RecordLit(a) => fmt_list("{ ", ", ", " }", a, f, |(k, v), f| {
                write!(f, "{} = {}", k, v)
            })?,
            UnionType(a) => fmt_list("< ", " | ", " >", a, f, |(k, v), f| {
                write!(f, "{}", k)?;
                if let Some(v) = v {
                    write!(f, ": {}", v)?;
                }
                Ok(())
            })?,
            Import(a) => a.fmt(f)?,
            Embed(a) => a.fmt(f)?,
        }
        Ok(())
    }
}

// There is a one-to-one correspondence between the formatter and the grammar. Each phase is
// named after a corresponding grammar group, and the structure of the formatter reflects
// the relationship between the corresponding grammar rules. This leads to the nice property
// of automatically getting all the parentheses and precedences right.
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
enum PrintPhase {
    Base,
    Operator,
    BinOp(core::BinOp),
    App,
    Import,
    Primitive,
}

// Wraps an Expr with a phase, so that phase selsction can be done
// separate from the actual printing
#[derive(Clone)]
struct PhasedExpr<'a, A>(&'a SubExpr<A>, PrintPhase);

impl<'a, A: Display + Clone> Display for PhasedExpr<'a, A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.0.as_ref().fmt_phase(f, self.1)
    }
}

impl<'a, A: Display + Clone> PhasedExpr<'a, A> {
    fn phase(self, phase: PrintPhase) -> PhasedExpr<'a, A> {
        PhasedExpr(self.0, phase)
    }
}

impl<A: Display + Clone> Expr<A> {
    fn fmt_phase(
        &self,
        f: &mut fmt::Formatter,
        phase: PrintPhase,
    ) -> Result<(), fmt::Error> {
        use crate::ExprF::*;
        use PrintPhase::*;

        let needs_paren = match self {
            Lam(_, _, _)
            | BoolIf(_, _, _)
            | Pi(_, _, _)
            | Let(_, _, _, _)
            | EmptyListLit(_)
            | NEListLit(_)
            | SomeLit(_)
            | Merge(_, _, _)
            | Annot(_, _)
                if phase > Base =>
            {
                true
            }
            // Precedence is magically handled by the ordering of BinOps.
            ExprF::BinOp(op, _, _) if phase > PrintPhase::BinOp(*op) => true,
            ExprF::App(_, _) if phase > PrintPhase::App => true,
            Field(_, _) | Projection(_, _) if phase > PrintPhase::Import => {
                true
            }
            _ => false,
        };

        // Annotate subexpressions with the appropriate phase, defaulting to Base
        let phased_self = match self.map_ref(|e| PhasedExpr(e, Base)) {
            Pi(a, b, c) => {
                if &String::from(&a) == "_" {
                    Pi(a, b.phase(Operator), c)
                } else {
                    Pi(a, b, c)
                }
            }
            Merge(a, b, c) => Merge(
                a.phase(PrintPhase::Import),
                b.phase(PrintPhase::Import),
                c.map(|x| x.phase(PrintPhase::App)),
            ),
            Annot(a, b) => Annot(a.phase(Operator), b),
            ExprF::BinOp(op, a, b) => ExprF::BinOp(
                op,
                a.phase(PrintPhase::BinOp(op)),
                b.phase(PrintPhase::BinOp(op)),
            ),
            SomeLit(e) => SomeLit(e.phase(PrintPhase::Import)),
            ExprF::App(f, a) => ExprF::App(
                f.phase(PrintPhase::Import),
                a.phase(PrintPhase::Import),
            ),
            Field(a, b) => Field(a.phase(Primitive), b),
            Projection(e, ls) => Projection(e.phase(Primitive), ls),
            e => e,
        };

        if needs_paren {
            f.write_str("(")?;
        }

        // Uses the ExprF<PhasedExpr<_>, _> instance
        phased_self.fmt(f)?;

        if needs_paren {
            f.write_str(")")?;
        }
        Ok(())
    }
}

impl<A: Display + Clone> Display for SubExpr<A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.as_ref().fmt_phase(f, PrintPhase::Base)
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

impl<SubExpr: Display> Display for InterpolatedText<SubExpr> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        f.write_str("\"")?;
        for x in self.iter() {
            match x {
                InterpolatedTextContents::Text(a) => {
                    for c in a.chars() {
                        match c {
                            '\\' => f.write_str("\\\\"),
                            '"' => f.write_str("\\\""),
                            '$' => f.write_str("\\u0024"),
                            '\u{0008}' => f.write_str("\\b"),
                            '\u{000C}' => f.write_str("\\f"),
                            '\n' => f.write_str("\\n"),
                            '\r' => f.write_str("\\r"),
                            '\t' => f.write_str("\\t"),
                            '\u{0000}'..='\u{001F}' => {
                                // Escape to an explicit "\u{XXXX}" form
                                let escaped: String =
                                    c.escape_default().collect();
                                // Print as "\uXXXX"
                                write!(
                                    f,
                                    "\\u{:0>4}",
                                    &escaped[3..escaped.len() - 1]
                                )
                            }
                            c => write!(f, "{}", c),
                        }?;
                    }
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
}

impl Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Debug>::fmt(self, f)
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use crate::BinOp::*;
        f.write_str(match self {
            BoolOr => "||",
            TextAppend => "++",
            NaturalPlus => "+",
            BoolAnd => "&&",
            RecursiveRecordMerge => "∧",
            NaturalTimes => "*",
            BoolEQ => "==",
            BoolNE => "!=",
            RecursiveRecordTypeMerge => "⩓",
            ImportAlt => "?",
            RightBiasedRecordMerge => "⫽",
            ListAppend => "#",
            Equivalence => "≡",
        })
    }
}

impl Display for NaiveDouble {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let v = f64::from(*self);
        if v == std::f64::INFINITY {
            f.write_str("Infinity")
        } else if v == std::f64::NEG_INFINITY {
            f.write_str("-Infinity")
        } else if v.is_nan() {
            f.write_str("NaN")
        } else {
            let s = format!("{}", v);
            if s.contains('e') || s.contains('.') {
                f.write_str(&s)
            } else {
                write!(f, "{}.0", s)
            }
        }
    }
}

impl Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        // TODO: distinguish between reserved and nonreserved locations for quoting builtins
        let s = String::from(self);
        let is_reserved = match s.as_str() {
            "let" | "in" | "if" | "then" | "else" | "Type" | "Kind"
            | "Sort" | "True" | "False" => true,
            _ => crate::Builtin::parse(&s).is_some(),
        };
        if !is_reserved && s.chars().all(|c| c.is_ascii_alphanumeric()) {
            write!(f, "{}", s)
        } else {
            write!(f, "`{}`", s)
        }
    }
}

impl Display for Hash {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Hash::SHA256(hash) => write!(f, "sha256:{}", hex::encode(hash)),
        }
    }
}
impl<SubExpr: Display> Display for Import<SubExpr> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use FilePrefix::*;
        use ImportLocation::*;
        use ImportMode::*;
        let fmt_remote_path_component = |s: &str| -> String {
            use percent_encoding::{
                utf8_percent_encode, PATH_SEGMENT_ENCODE_SET,
            };
            utf8_percent_encode(s, PATH_SEGMENT_ENCODE_SET).to_string()
        };
        let fmt_local_path_component = |s: &str| -> String {
            if s.chars().all(|c| c.is_ascii_alphanumeric()) {
                s.to_owned()
            } else {
                format!("\"{}\"", s)
            }
        };

        match &self.location {
            Local(prefix, path) => {
                let prefix = match prefix {
                    Here => ".",
                    Parent => "..",
                    Home => "~",
                    Absolute => "",
                };
                write!(f, "{}/", prefix)?;
                let path: String = path
                    .iter()
                    .map(|c| fmt_local_path_component(c.as_ref()))
                    .join("/");
                f.write_str(&path)?;
            }
            Remote(url) => {
                write!(f, "{}://{}/", url.scheme, url.authority,)?;
                let path: String = url
                    .path
                    .iter()
                    .map(|c| fmt_remote_path_component(c.as_ref()))
                    .join("/");
                f.write_str(&path)?;
                if let Some(q) = &url.query {
                    write!(f, "?{}", q)?
                }
                if let Some(h) = &url.headers {
                    write!(f, " using ({})", h)?
                }
            }
            Env(s) => {
                write!(f, "env:")?;
                if s.chars().all(|c| c.is_ascii_alphanumeric()) {
                    write!(f, "{}", s)?;
                } else {
                    write!(f, "\"")?;
                    for c in s.chars() {
                        match c {
                            '"' => f.write_str("\\\"")?,
                            '\\' => f.write_str("\\\\")?,
                            '\u{0007}' => f.write_str("\\a")?,
                            '\u{0008}' => f.write_str("\\b")?,
                            '\u{000C}' => f.write_str("\\f")?,
                            '\n' => f.write_str("\\n")?,
                            '\r' => f.write_str("\\r")?,
                            '\t' => f.write_str("\\t")?,
                            '\u{000B}' => f.write_str("\\v")?,
                            _ => write!(f, "{}", c)?,
                        }
                    }
                    write!(f, "\"")?;
                }
            }
            Missing => {
                write!(f, "missing")?;
            }
        }
        if let Some(hash) = &self.hash {
            write!(f, " ")?;
            hash.fmt(f)?;
        }
        match self.mode {
            Code => {}
            RawText => write!(f, " as Text")?,
            Location => write!(f, " as Location")?,
        }
        Ok(())
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
            OptionalNone => "None",
            NaturalBuild => "Natural/build",
            NaturalFold => "Natural/fold",
            NaturalIsZero => "Natural/isZero",
            NaturalEven => "Natural/even",
            NaturalOdd => "Natural/odd",
            NaturalToInteger => "Natural/toInteger",
            NaturalShow => "Natural/show",
            NaturalSubtract => "Natural/subtract",
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

impl Display for Scheme {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use crate::Scheme::*;
        f.write_str(match *self {
            HTTP => "http",
            HTTPS => "https",
        })
    }
}

impl<Label: Display> Display for V<Label> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let V(x, n) = self;
        x.fmt(f)?;
        if *n != 0 {
            write!(f, "@{}", n)?;
        }
        Ok(())
    }
}
