use crate::*;
use itertools::Itertools;
use std::fmt::{self, Display};

impl<S, A: Display> Display for Expr<S, A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.fmt_phase(f, PrintPhase::Base)
    }
}

impl<S, A: Display> Display for SubExpr<S, A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.as_ref().fmt(f)
    }
}

//  There is a one-to-one correspondence between the formatter and the grammar. Each phase is
//  named after a corresponding grammar group, and the structure of the formatter reflects
//  the relationship between the corresponding grammar rules. This leads to the nice property
//  of automatically getting all the parentheses and precedences right.
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
enum PrintPhase {
    Base,
    Operator,
    BinOp(core::BinOp),
    App,
    Import,
    Primitive,
    Paren,
}

impl<S, A: Display> Expr<S, A> {
    fn fmt_phase(
        &self,
        f: &mut fmt::Formatter,
        phase: PrintPhase,
    ) -> Result<(), fmt::Error> {
        use crate::ExprF::*;
        use PrintPhase::*;
        match self {
            _ if phase == Paren => {
                f.write_str("(")?;
                self.fmt_phase(f, Base)?;
                f.write_str(")")?;
            }

            Lam(a, b, c) => {
                if phase > Base {
                    return self.fmt_phase(f, Paren);
                }
                write!(f, "λ({} : ", a)?;
                b.fmt(f)?;
                write!(f, ") → ")?;
                c.fmt(f)?;
            }
            BoolIf(a, b, c) => {
                if phase > Base {
                    return self.fmt_phase(f, Paren);
                }
                write!(f, "if ")?;
                a.fmt(f)?;
                write!(f, " then ")?;
                b.fmt(f)?;
                write!(f, " else ")?;
                c.fmt(f)?;
            }
            Pi(a, b, c) if &String::from(a) == "_" => {
                if phase > Base {
                    return self.fmt_phase(f, Paren);
                }
                b.fmt_phase(f, Operator)?;
                write!(f, " → ")?;
                c.fmt(f)?;
            }
            Pi(a, b, c) => {
                if phase > Base {
                    return self.fmt_phase(f, Paren);
                }
                write!(f, "∀({} : ", a)?;
                b.fmt(f)?;
                write!(f, ") → ")?;
                c.fmt(f)?;
            }
            Let(a, b, c, d) => {
                if phase > Base {
                    return self.fmt_phase(f, Paren);
                }
                write!(f, "let {}", a)?;
                if let Some(b) = b {
                    write!(f, " : ")?;
                    b.fmt(f)?;
                }
                write!(f, " = ")?;
                c.fmt(f)?;
                write!(f, " in ")?;
                d.fmt(f)?;
            }
            EmptyListLit(t) => {
                if phase > Base {
                    return self.fmt_phase(f, Paren);
                }
                write!(f, "[] : List ")?;
                t.fmt_phase(f, Import)?;
            }
            NEListLit(es) => {
                if phase > Base {
                    return self.fmt_phase(f, Paren);
                }
                fmt_list("[", ", ", "]", es, f, |e, f| e.fmt(f))?;
            }
            EmptyOptionalLit(t) => {
                if phase > Base {
                    return self.fmt_phase(f, Paren);
                }
                write!(f, "None ")?;
                t.fmt_phase(f, Import)?;
            }
            NEOptionalLit(e) => {
                if phase > Base {
                    return self.fmt_phase(f, Paren);
                }
                write!(f, "Some ")?;
                e.fmt_phase(f, Import)?;
            }
            Merge(a, b, c) => {
                if phase > Base {
                    return self.fmt_phase(f, Paren);
                }
                write!(f, "merge ")?;
                a.fmt_phase(f, Import)?;
                write!(f, " ")?;
                b.fmt_phase(f, Import)?;
                if let Some(c) = c {
                    write!(f, " : ")?;
                    c.fmt_phase(f, PrintPhase::App)?;
                }
            }
            Annot(a, b) => {
                if phase > Base {
                    return self.fmt_phase(f, Paren);
                }
                a.fmt_phase(f, Operator)?;
                write!(f, " : ")?;
                b.fmt(f)?;
            }
            ExprF::BinOp(op, a, b) => {
                // Precedence is magically handled by the ordering of BinOps.
                if phase > PrintPhase::BinOp(*op) {
                    return self.fmt_phase(f, Paren);
                }
                a.fmt_phase(f, PrintPhase::BinOp(*op))?;
                write!(f, " {} ", op)?;
                b.fmt_phase(f, PrintPhase::BinOp(*op))?;
            }
            ExprF::App(a, args) => {
                if phase > PrintPhase::App {
                    return self.fmt_phase(f, Paren);
                }
                a.fmt_phase(f, Import)?;
                for x in args {
                    f.write_str(" ")?;
                    x.fmt_phase(f, Import)?;
                }
            }
            Field(a, b) => {
                if phase > Import {
                    return self.fmt_phase(f, Paren);
                }
                a.fmt_phase(f, Primitive)?;
                write!(f, ".{}", b)?;
            }
            Projection(e, ls) => {
                if phase > Import {
                    return self.fmt_phase(f, Paren);
                }
                e.fmt_phase(f, Primitive)?;
                write!(f, ".")?;
                fmt_list("{ ", ", ", " }", ls, f, |l, f| write!(f, "{}", l))?;
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
                write!(f, "{} : {}", k, v)
            })?,
            UnionLit(a, b, c) => {
                f.write_str("< ")?;
                write!(f, "{} = {}", a, b)?;
                for (k, v) in c {
                    f.write_str(" | ")?;
                    write!(f, "{} : {}", k, v)?;
                }
                f.write_str(" >")?
            }
            Embed(a) => a.fmt(f)?,
            Note(_, b) => b.fmt_phase(f, phase)?,
        }
        Ok(())
    }
}

impl<S, A: Display> SubExpr<S, A> {
    fn fmt_phase(
        &self,
        f: &mut fmt::Formatter,
        phase: PrintPhase,
    ) -> Result<(), fmt::Error> {
        self.0.as_ref().fmt_phase(f, phase)
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

impl<SubExpr: Display + Clone> Display for InterpolatedText<SubExpr> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        f.write_str("\"")?;
        for x in self.iter() {
            match x {
                InterpolatedTextContents::Text(a) => {
                    for c in a.chars() {
                        match c {
                            '\\' => f.write_str("\\\\"),
                            '"' => f.write_str("\\\""),
                            '$' => f.write_str("\\$"),
                            '\u{0008}' => f.write_str("\\b"),
                            '\u{000C}' => f.write_str("\\f"),
                            '\n' => f.write_str("\\n"),
                            '\r' => f.write_str("\\r"),
                            '\t' => f.write_str("\\t"),
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
            Combine => "/\\",
            NaturalTimes => "*",
            BoolEQ => "==",
            BoolNE => "!=",
            CombineTypes => "//\\\\",
            ImportAlt => "?",
            Prefer => "//",
            ListAppend => "#",
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
            if s.contains("e") || s.contains(".") {
                f.write_str(&s)
            } else {
                write!(f, "{}.0", s)
            }
        }
    }
}

impl Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let s = String::from(self);
        let is_keyword = |s| match s {
            "let" | "in" | "if" | "then" | "else" => true,
            _ => false,
        };
        if s.chars().all(|c| c.is_ascii_alphanumeric()) && !is_keyword(&s) {
            write!(f, "{}", s)
        } else {
            write!(f, "`{}`", s)
        }
    }
}

impl Display for Hash {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}:{}", self.protocol, self.hash)
    }
}
impl Display for ImportHashed {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use std::path::PathBuf;
        use FilePrefix::*;
        use ImportLocation::*;
        let quoted = |s: &str| -> String {
            if s.chars().all(|c| c.is_ascii_alphanumeric()) {
                s.to_owned()
            } else {
                format!("\"{}\"", s)
            }
        };
        let fmt_path = |f: &mut fmt::Formatter, p: &PathBuf| {
            let res: String = p
                .iter()
                .map(|c| quoted(c.to_string_lossy().as_ref()))
                .join("/");
            f.write_str(&res)
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
                fmt_path(f, path)?;
            }
            Remote(url) => {
                write!(f, "{}://{}/", url.scheme, url.authority,)?;
                fmt_path(f, &url.path)?;
                if let Some(q) = &url.query {
                    write!(f, "?{}", q)?
                }
                if let Some(h) = &url.headers {
                    write!(f, " using ({})", h)?
                }
            }
            Env(e) => {
                write!(f, "env:{}", quoted(e))?;
            }
            Missing => {
                write!(f, "missing")?;
            }
        }
        if let Some(hash) = &self.hash {
            write!(f, " ")?;
            hash.fmt(f)?;
        }
        Ok(())
    }
}

impl Display for Import {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.location_hashed.fmt(f)?;
        use ImportMode::*;
        match self.mode {
            Code => {}
            RawText => write!(f, " as Text")?,
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

impl Display for X {
    fn fmt(&self, _: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {}
    }
}
