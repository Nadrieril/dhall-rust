use crate::*;
use std::fmt::{self, Display};

//  There used to be a one-to-one correspondence between the formatters in this section
//  and the grammar.  Each formatter is named after the
//  corresponding grammar rule and the relationship between formatters exactly matches
//  the relationship between grammar rules.  This leads to the nice emergent property
//  of automatically getting all the parentheses and precedences right.
//
//  WARNING: This approach has one major disadvantage: you can get an infinite loop if
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
            &EmptyOptionalLit(ref t) => {
                write!(f, "None ")?;
                t.fmt_e(f)?;
                Ok(())
            }
            &NEOptionalLit(ref e) => {
                write!(f, "Some ")?;
                e.fmt_e(f)?;
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
            &RecordType(ref a) if a.is_empty() => f.write_str("{}"),
            &RecordType(ref a) => {
                fmt_list("{ ", ", ", " }", a, f, |(k, t), f| {
                    write!(f, "{} : {}", k, t)
                })
            }
            &RecordLit(ref a) if a.is_empty() => f.write_str("{=}"),
            &RecordLit(ref a) => {
                fmt_list("{ ", ", ", " }", a, f, |(k, v), f| {
                    write!(f, "{} = {}", k, v)
                })
            }
            &UnionType(ref a) => {
                fmt_list("< ", " | ", " >", a, f, |(k, v), f| {
                    write!(f, "{} : {}", k, v)
                })
            }
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

impl Display for X {
    fn fmt(&self, _: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {}
    }
}
