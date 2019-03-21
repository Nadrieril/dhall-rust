use pest::iterators::Pair;
use pest::Parser;
use std::collections::BTreeMap;
use std::path::PathBuf;

use dhall_parser::{DhallParser, Rule};

use crate::*;

// This file consumes the parse tree generated by pest and turns it into
// our own AST. All those custom macros should eventually moved into
// their own crate because they are quite general and useful. For now they
// are here and hopefully you can figure out how they work.

type ParsedExpr = crate::ParsedExpr<X>;
type ParsedText = InterpolatedText<X, Import>;
type ParsedTextContents<'a> = InterpolatedTextContents<'a, X, Import>;

pub type ParseError = pest::error::Error<Rule>;

pub type ParseResult<T> = Result<T, ParseError>;

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

pub fn custom_parse_error(pair: &Pair<Rule>, msg: String) -> ParseError {
    let msg =
        format!("{} while matching on:\n{}", msg, debug_pair(pair.clone()));
    let e = pest::error::ErrorVariant::CustomError { message: msg };
    pest::error::Error::new_from_span(e, pair.as_span())
}

fn debug_pair(pair: Pair<Rule>) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    fn aux(s: &mut String, indent: usize, prefix: String, pair: Pair<Rule>) {
        let indent_str = "| ".repeat(indent);
        let rule = pair.as_rule();
        let contents = pair.as_str();
        let mut inner = pair.into_inner();
        let mut first = true;
        while let Some(p) = inner.next() {
            if first {
                first = false;
                let last = inner.peek().is_none();
                if last && p.as_str() == contents {
                    let prefix = format!("{}{:?} > ", prefix, rule);
                    aux(s, indent, prefix, p);
                    continue;
                } else {
                    writeln!(
                        s,
                        r#"{}{}{:?}: "{}""#,
                        indent_str, prefix, rule, contents
                    )
                    .unwrap();
                }
            }
            aux(s, indent + 1, "".into(), p);
        }
        if first {
            writeln!(
                s,
                r#"{}{}{:?}: "{}""#,
                indent_str, prefix, rule, contents
            )
            .unwrap();
        }
    }
    aux(&mut s, 0, "".into(), pair);
    s
}

macro_rules! match_pair {
    (@make_child_match, ($pair:expr, $($vars:tt)*), ($($outer_acc:tt)*), ($($acc:tt)*), ($(,)* $ty:ident ($x:ident..) $($rest_of_match:tt)*) => $body:expr, $($rest:tt)*) => {
        match_pair!(@make_child_match, ($pair, $($vars)*), ($($outer_acc)*), ($($acc)*, xs..), ($($rest_of_match)*) => {
            let xs = xs.map(|x| match x {
                ParsedValue::$ty(y) => Ok(y),
                x => Err(custom_parse_error(&$pair,
                    format!("Unexpected child: {:?}", x)
                )),
            }).collect::<Result<Vec<_>, _>>()?;
            let $x = xs.into_iter();
            $body
        }, $($rest)*)
    };
    (@make_child_match, ($($vars:tt)*), ($($outer_acc:tt)*), ($($acc:tt)*), ($(,)* $ty:ident ($x:pat)  $($rest_of_match:tt)*) => $body:expr, $($rest:tt)*) => {
        match_pair!(@make_child_match, ($($vars)*), ($($outer_acc)*), ($($acc)*, ParsedValue::$ty($x)), ($($rest_of_match)*) => $body, $($rest)*)
    };
    (@make_child_match, ($($vars:tt)*), ($($outer_acc:tt)*), (, $($acc:tt)*), ($(,)*) => $body:expr, $($rest:tt)*) => {
        match_pair!(@make_matches, ($($vars)*), ($($outer_acc)* [$($acc)*] => { $body },), $($rest)*)
    };
    (@make_child_match, ($($vars:tt)*), ($($outer_acc:tt)*), (), ($(,)*) => $body:expr, $($rest:tt)*) => {
        match_pair!(@make_matches, ($($vars)*), ($($outer_acc)* [] => { $body },), $($rest)*)
    };

    (@make_matches, ($($vars:tt)*), ($($acc:tt)*), [$($args:tt)*] => $body:expr, $($rest:tt)*) => {
        match_pair!(@make_child_match, ($($vars)*), ($($acc)*), (), ($($args)*) => $body, $($rest)*)
    };
    (@make_matches, ($pair:expr, $parsed:expr), ($($acc:tt)*) $(,)*) => {
        {
            let pair = $pair.clone();
            #[allow(unreachable_code)]
            iter_patterns::match_vec!($parsed;
                $($acc)*
                [x..] => Err(
                    custom_parse_error(&pair,
                        format!("Unexpected children: {:?}", x.collect::<Vec<_>>())
                    )
                )?,
            ).ok_or_else(|| unreachable!())
        }
    };

    (($($vars:tt)*); $( [$($args:tt)*] => $body:expr ),* $(,)*) => {
        match_pair!(@make_matches, ($($vars)*), (), $( [$($args)*] => $body ),* ,)
    };
}

macro_rules! make_parser {
    (@pattern, rule, $name:ident) => (Rule::$name);
    (@pattern, rule_group, $name:ident) => (_);
    (@filter, rule) => (true);
    (@filter, rule_group) => (false);

    (@body, $pair:expr, $parsed:expr, rule!( $name:ident<$o:ty>; $($args:tt)* )) => (
        make_parser!(@body, $pair, $parsed, rule!( $name<$o> as $name; $($args)* ))
    );
    (@body, $pair:expr, $parsed:expr, rule!( $name:ident<$o:ty> as $group:ident; raw_pair!($x:pat) => $body:expr )) => ( {
        let $x = $pair;
        let res: $o = $body;
        Ok(ParsedValue::$group(res))
    });
    (@body, $pair:expr, $parsed:expr, rule!( $name:ident<$o:ty> as $group:ident; captured_str!($x:pat) => $body:expr )) => ( {
        let $x = $pair.as_str();
        let res: $o = $body;
        Ok(ParsedValue::$group(res))
    });
    (@body, $pair:expr, $parsed:expr, rule!( $name:ident<$o:ty> as $group:ident; children!( $($args:tt)* ) )) => ( {
        let res: $o = match_pair!(($pair, $parsed); $($args)*)?;
        Ok(ParsedValue::$group(res))
    });
    (@body, $pair:expr, $parsed:expr, rule_group!( $name:ident<$o:ty> )) => (
        unreachable!()
    );

    ($( $submac:ident!( $name:ident<$o:ty> $($args:tt)* ); )*) => (
        #[allow(non_camel_case_types, dead_code)]
        #[derive(Debug)]
        enum ParsedValue<'a> {
            $( $name($o), )*
        }

        // Non-recursive implementation to avoid stack overflows
        fn parse_any<'a>(initial_pair: Pair<'a, Rule>) -> ParseResult<ParsedValue<'a>> {
            enum StackFrame<'a> {
                Unprocessed(Pair<'a, Rule>),
                Processed(Pair<'a, Rule>, usize),
            }
            use StackFrame::*;
            let mut pairs_stack: Vec<StackFrame> = vec![Unprocessed(initial_pair.clone())];
            let mut values_stack: Vec<ParsedValue> = vec![];
            while let Some(p) = pairs_stack.pop() {
                match p {
                    Unprocessed(mut pair) => {
                        loop {
                            let mut pairs: Vec<_> = pair.clone().into_inner().collect();
                            let n_children = pairs.len();
                            if n_children == 1 && can_be_shortcutted(pair.as_rule()) {
                                pair = pairs.pop().unwrap();
                                continue
                            } else {
                                pairs_stack.push(Processed(pair, n_children));
                                pairs_stack.extend(pairs.into_iter().map(StackFrame::Unprocessed));
                                break
                            }
                        }
                    }
                    Processed(pair, n) => {
                        let mut parsed: Vec<_> = values_stack.split_off(values_stack.len() - n);
                        parsed.reverse();
                        let val = match pair.as_rule() {
                            $(
                                make_parser!(@pattern, $submac, $name)
                                if make_parser!(@filter, $submac)
                                => make_parser!(@body, pair, parsed, $submac!( $name<$o> $($args)* ))
                                ,
                            )*
                            r => Err(custom_parse_error(&pair, format!("parse_any: Unexpected {:?}", r))),
                        }?;
                        values_stack.push(val);
                    }
                }
            }
            Ok(values_stack.pop().unwrap())
        }
    );
}

// List of rules that can be shortcutted if they have a single child
fn can_be_shortcutted(rule: Rule) -> bool {
    use Rule::*;
    match rule {
        import_alt_expression
        | or_expression
        | plus_expression
        | text_append_expression
        | list_append_expression
        | and_expression
        | combine_expression
        | prefer_expression
        | combine_types_expression
        | times_expression
        | equal_expression
        | not_equal_expression
        | application_expression
        | selector_expression_raw
        | annotated_expression => true,
        _ => false,
    }
}

make_parser! {
    rule!(EOI<()>; raw_pair!(_) => ());

    rule!(label_raw<Label>; captured_str!(s) => Label::from(s.trim().to_owned()));

    rule!(double_quote_literal<ParsedText>; children!(
        [double_quote_chunk(chunks..)] => {
            chunks.collect()
        }
    ));

    rule!(double_quote_chunk<ParsedTextContents<'a>>; children!(
        [interpolation(e)] => {
            InterpolatedTextContents::Expr(e)
        },
        [double_quote_escaped(s)] => {
            InterpolatedTextContents::Text(s)
        },
        [double_quote_char(s)] => {
            InterpolatedTextContents::Text(s)
        },
    ));
    rule!(double_quote_escaped<&'a str>;
        // TODO: parse all escapes
        captured_str!(s) => {
            match s {
                "\"" => "\"",
                "$" => "$",
                "\\" => "\\",
                "/" => "/",
                // "b" => "\b",
                // "f" => "\f",
                "n" => "\n",
                "r" => "\r",
                "t" => "\t",
                // "uXXXX"
                _ => unimplemented!(),
            }
        }
    );
    rule!(double_quote_char<&'a str>;
        captured_str!(s) => s
    );

    rule!(end_of_line<()>; raw_pair!(_) => ());

    rule!(single_quote_literal<ParsedText>; children!(
        [end_of_line(eol), single_quote_continue(contents)] => {
            contents.into_iter().rev().collect::<ParsedText>()
        }
    ));
    rule!(single_quote_char<&'a str>;
        captured_str!(s) => s
    );
    rule!(escaped_quote_pair<&'a str>;
        raw_pair!(_) => "''"
    );
    rule!(escaped_interpolation<&'a str>;
        raw_pair!(_) => "${"
    );
    rule!(interpolation<ParsedExpr>; children!(
        [expression(e)] => e
    ));

    rule!(single_quote_continue<Vec<ParsedTextContents<'a>>>; children!(
        [interpolation(c), single_quote_continue(rest)] => {
            let mut rest = rest;
            rest.push(InterpolatedTextContents::Expr(c)); rest
        },
        [escaped_quote_pair(c), single_quote_continue(rest)] => {
            let mut rest = rest;
            rest.push(InterpolatedTextContents::Text(c)); rest
        },
        [escaped_interpolation(c), single_quote_continue(rest)] => {
            let mut rest = rest;
            rest.push(InterpolatedTextContents::Text(c)); rest
        },
        [single_quote_char(c), single_quote_continue(rest)] => {
            let mut rest = rest;
            rest.push(InterpolatedTextContents::Text(c)); rest
        },
        [] => {
            vec![]
        },
    ));

    rule!(NaN_raw<()>; raw_pair!(_) => ());
    rule!(minus_infinity_literal<()>; raw_pair!(_) => ());
    rule!(plus_infinity_literal<()>; raw_pair!(_) => ());

    rule!(double_literal_raw<core::Double>;
        raw_pair!(pair) => {
            pair.as_str().trim()
                .parse::<f64>()
                .map(NaiveDouble::from)
                .map_err(|e: std::num::ParseFloatError| custom_parse_error(&pair, format!("{}", e)))?
        }
    );

    rule!(natural_literal_raw<core::Natural>;
        raw_pair!(pair) => {
            pair.as_str().trim()
                .parse()
                .map_err(|e: std::num::ParseIntError| custom_parse_error(&pair, format!("{}", e)))?
        }
    );

    rule!(integer_literal_raw<core::Integer>;
        raw_pair!(pair) => {
            pair.as_str().trim()
                .parse()
                .map_err(|e: std::num::ParseIntError| custom_parse_error(&pair, format!("{}", e)))?
        }
    );

    rule!(path<PathBuf>;
        captured_str!(s) => (".".to_owned() + s).into()
    );

    rule_group!(local_raw<(FilePrefix, PathBuf)>);

    rule!(parent_path<(FilePrefix, PathBuf)> as local_raw; children!(
        [path(p)] => (FilePrefix::Parent, p)
    ));

    rule!(here_path<(FilePrefix, PathBuf)> as local_raw; children!(
        [path(p)] => (FilePrefix::Here, p)
    ));

    rule!(home_path<(FilePrefix, PathBuf)> as local_raw; children!(
        [path(p)] => (FilePrefix::Home, p)
    ));

    rule!(absolute_path<(FilePrefix, PathBuf)> as local_raw; children!(
        [path(p)] => (FilePrefix::Absolute, p)
    ));

    // TODO: other import types
    rule!(import_type_raw<ImportLocation>; children!(
        // [missing_raw(_e)] => {
        //     ImportLocation::Missing
        // }
        // [env_raw(e)] => {
        //     ImportLocation::Env(e)
        // }
        // [http(url)] => {
        //     ImportLocation::Remote(url)
        // }
        [local_raw((prefix, path))] => {
            ImportLocation::Local(prefix, path)
        }
    ));

    rule!(import_hashed_raw<(ImportLocation, Option<()>)>; children!(
        // TODO: handle hash
        [import_type_raw(import)] => (import, None)
    ));

    rule_group!(expression<ParsedExpr>);

    rule!(import_raw<ParsedExpr> as expression; children!(
        // TODO: handle "as Text"
        [import_hashed_raw((location, hash))] => {
            bx(Expr::Embed(Import {
                mode: ImportMode::Code,
                hash,
                location,
            }))
        }
    ));

    rule!(lambda_expression<ParsedExpr> as expression; children!(
        [label_raw(l), expression(typ), expression(body)] => {
            bx(Expr::Lam(l, typ, body))
        }
    ));

    rule!(ifthenelse_expression<ParsedExpr> as expression; children!(
        [expression(cond), expression(left), expression(right)] => {
            bx(Expr::BoolIf(cond, left, right))
        }
    ));

    rule!(let_expression<ParsedExpr> as expression; children!(
        [let_binding(bindings..), expression(final_expr)] => {
            bindings.fold(final_expr, |acc, x| bx(Expr::Let(x.0, x.1, x.2, acc)))
        }
    ));

    rule!(let_binding<(Label, Option<ParsedExpr>, ParsedExpr)>; children!(
        [label_raw(name), expression(annot), expression(expr)] => (name, Some(annot), expr),
        [label_raw(name), expression(expr)] => (name, None, expr),
    ));

    rule!(forall_expression<ParsedExpr> as expression; children!(
        [label_raw(l), expression(typ), expression(body)] => {
            bx(Expr::Pi(l, typ, body))
        }
    ));

    rule!(arrow_expression<ParsedExpr> as expression; children!(
        [expression(typ), expression(body)] => {
            bx(Expr::Pi("_".into(), typ, body))
        }
    ));

    rule!(merge_expression<ParsedExpr> as expression; children!(
        [expression(x), expression(y), expression(z)] => bx(Expr::Merge(x, y, Some(z))),
        [expression(x), expression(y)] => bx(Expr::Merge(x, y, None)),
    ));

    rule!(List<()>; raw_pair!(_) => ());
    rule!(Optional<()>; raw_pair!(_) => ());

    rule!(empty_collection<ParsedExpr> as expression; children!(
        [List(_), expression(t)] => {
            bx(Expr::EmptyListLit(t))
        },
        [Optional(_), expression(t)] => {
            bx(Expr::EmptyOptionalLit(t))
        },
    ));

    rule!(non_empty_optional<ParsedExpr> as expression; children!(
        [expression(x), Optional(_), expression(t)] => {
            rc(Expr::Annot(rc(Expr::NEOptionalLit(x)), t))
        }
    ));

    rule!(import_alt_expression<ParsedExpr> as expression; children!(
        [expression(e)] => e,
        [expression(first), expression(rest..)] => {
            rest.fold(first, |acc, e| bx(Expr::BinOp(BinOp::ImportAlt, acc, e)))
        },
    ));
    rule!(or_expression<ParsedExpr> as expression; children!(
        [expression(e)] => e,
        [expression(first), expression(rest..)] => {
            rest.fold(first, |acc, e| bx(Expr::BinOp(BinOp::BoolOr, acc, e)))
        },
    ));
    rule!(plus_expression<ParsedExpr> as expression; children!(
        [expression(e)] => e,
        [expression(first), expression(rest..)] => {
            rest.fold(first, |acc, e| bx(Expr::BinOp(BinOp::NaturalPlus, acc, e)))
        },
    ));
    rule!(text_append_expression<ParsedExpr> as expression; children!(
        [expression(e)] => e,
        [expression(first), expression(rest..)] => {
            rest.fold(first, |acc, e| bx(Expr::BinOp(BinOp::TextAppend, acc, e)))
        },
    ));
    rule!(list_append_expression<ParsedExpr> as expression; children!(
        [expression(e)] => e,
        [expression(first), expression(rest..)] => {
            rest.fold(first, |acc, e| bx(Expr::BinOp(BinOp::ListAppend, acc, e)))
        },
    ));
    rule!(and_expression<ParsedExpr> as expression; children!(
        [expression(e)] => e,
        [expression(first), expression(rest..)] => {
            rest.fold(first, |acc, e| bx(Expr::BinOp(BinOp::BoolAnd, acc, e)))
        },
    ));
    rule!(combine_expression<ParsedExpr> as expression; children!(
        [expression(e)] => e,
        [expression(first), expression(rest..)] => {
            rest.fold(first, |acc, e| bx(Expr::BinOp(BinOp::Combine, acc, e)))
        },
    ));
    rule!(prefer_expression<ParsedExpr> as expression; children!(
        [expression(e)] => e,
        [expression(first), expression(rest..)] => {
            rest.fold(first, |acc, e| bx(Expr::BinOp(BinOp::Prefer, acc, e)))
        },
    ));
    rule!(combine_types_expression<ParsedExpr> as expression; children!(
        [expression(e)] => e,
        [expression(first), expression(rest..)] => {
            rest.fold(first, |acc, e| bx(Expr::BinOp(BinOp::CombineTypes, acc, e)))
        },
    ));
    rule!(times_expression<ParsedExpr> as expression; children!(
        [expression(e)] => e,
        [expression(first), expression(rest..)] => {
            rest.fold(first, |acc, e| bx(Expr::BinOp(BinOp::NaturalTimes, acc, e)))
        },
    ));
    rule!(equal_expression<ParsedExpr> as expression; children!(
        [expression(e)] => e,
        [expression(first), expression(rest..)] => {
            rest.fold(first, |acc, e| bx(Expr::BinOp(BinOp::BoolEQ, acc, e)))
        },
    ));
    rule!(not_equal_expression<ParsedExpr> as expression; children!(
        [expression(e)] => e,
        [expression(first), expression(rest..)] => {
            rest.fold(first, |acc, e| bx(Expr::BinOp(BinOp::BoolNE, acc, e)))
        },
    ));

    rule!(annotated_expression<ParsedExpr> as expression; children!(
        [expression(e)] => e,
        [expression(e), expression(annot)] => {
            bx(Expr::Annot(e, annot))
        },
    ));

    rule!(application_expression<ParsedExpr> as expression; children!(
        [expression(e)] => e,
        [expression(first), expression(second)] => {
            match first.as_ref() {
                Expr::Builtin(Builtin::OptionalNone) =>
                    bx(Expr::EmptyOptionalLit(second)),
                Expr::Builtin(Builtin::OptionalSome) =>
                    bx(Expr::NEOptionalLit(second)),
                _ => bx(Expr::App(first, vec![second])),
            }
        },
        [expression(first), expression(second), expression(rest..)] => {
            match first.as_ref() {
                Expr::Builtin(Builtin::OptionalNone) =>
                    bx(Expr::App(bx(Expr::EmptyOptionalLit(second)), rest.collect())),
                Expr::Builtin(Builtin::OptionalSome) =>
                    bx(Expr::App(bx(Expr::NEOptionalLit(second)), rest.collect())),
                _ => bx(Expr::App(first, std::iter::once(second).chain(rest).collect())),
            }
        },
    ));

    rule!(selector_expression_raw<ParsedExpr> as expression; children!(
        [expression(e)] => e,
        [expression(first), selector_raw(rest..)] => {
            rest.fold(first, |acc, e| bx(Expr::Field(acc, e)))
        }
    ));

    // TODO: handle record projection
    rule!(selector_raw<Label>; children!(
        [label_raw(l)] => l
    ));

    rule!(literal_expression_raw<ParsedExpr> as expression; children!(
        [double_literal_raw(n)] => bx(Expr::DoubleLit(n)),
        [minus_infinity_literal(n)] => bx(Expr::DoubleLit(std::f64::NEG_INFINITY.into())),
        [plus_infinity_literal(n)] => bx(Expr::DoubleLit(std::f64::INFINITY.into())),
        [NaN_raw(n)] => bx(Expr::DoubleLit(std::f64::NAN.into())),
        [natural_literal_raw(n)] => bx(Expr::NaturalLit(n)),
        [integer_literal_raw(n)] => bx(Expr::IntegerLit(n)),
        [double_quote_literal(s)] => bx(Expr::TextLit(s)),
        [single_quote_literal(s)] => bx(Expr::TextLit(s)),
        [expression(e)] => e,
    ));

    rule!(identifier_raw<ParsedExpr> as expression; children!(
        [label_raw(l), natural_literal_raw(idx)] => {
            let name = String::from(l.clone());
            match Builtin::parse(name.as_str()) {
                Some(b) => bx(Expr::Builtin(b)),
                None => match name.as_str() {
                    "True" => bx(Expr::BoolLit(true)),
                    "False" => bx(Expr::BoolLit(false)),
                    "Type" => bx(Expr::Const(Const::Type)),
                    "Kind" => bx(Expr::Const(Const::Kind)),
                    _ => bx(Expr::Var(V(l, idx))),
                }
            }
        },
        [label_raw(l)] => {
            let name = String::from(l.clone());
            match Builtin::parse(name.as_str()) {
                Some(b) => bx(Expr::Builtin(b)),
                None => match name.as_str() {
                    "True" => bx(Expr::BoolLit(true)),
                    "False" => bx(Expr::BoolLit(false)),
                    "Type" => bx(Expr::Const(Const::Type)),
                    "Kind" => bx(Expr::Const(Const::Kind)),
                    _ => bx(Expr::Var(V(l, 0))),
                }
            }
        },
    ));

    rule!(empty_record_literal<ParsedExpr> as expression;
        raw_pair!(_) => bx(Expr::RecordLit(BTreeMap::new()))
    );

    rule!(empty_record_type<ParsedExpr> as expression;
        raw_pair!(_) => bx(Expr::RecordType(BTreeMap::new()))
    );

    rule!(non_empty_record_type_or_literal<ParsedExpr> as expression; children!(
        [label_raw(first_label), non_empty_record_type(rest)] => {
            let (first_expr, mut map) = rest;
            map.insert(first_label, first_expr);
            bx(Expr::RecordType(map))
        },
        [label_raw(first_label), non_empty_record_literal(rest)] => {
            let (first_expr, mut map) = rest;
            map.insert(first_label, first_expr);
            bx(Expr::RecordLit(map))
        },
    ));

    rule!(non_empty_record_type<(ParsedExpr, BTreeMap<Label, ParsedExpr>)>; children!(
        [expression(expr), record_type_entry(entries..)] => {
            (expr, entries.collect())
        }
    ));

    rule!(record_type_entry<(Label, ParsedExpr)>; children!(
        [label_raw(name), expression(expr)] => (name, expr)
    ));

    rule!(non_empty_record_literal<(ParsedExpr, BTreeMap<Label, ParsedExpr>)>; children!(
        [expression(expr), record_literal_entry(entries..)] => {
            (expr, entries.collect())
        }
    ));

    rule!(record_literal_entry<(Label, ParsedExpr)>; children!(
        [label_raw(name), expression(expr)] => (name, expr)
    ));

    rule!(union_type_or_literal<ParsedExpr> as expression; children!(
        [empty_union_type(_)] => {
            bx(Expr::UnionType(BTreeMap::new()))
        },
        [non_empty_union_type_or_literal((Some((l, e)), entries))] => {
            bx(Expr::UnionLit(l, e, entries))
        },
        [non_empty_union_type_or_literal((None, entries))] => {
            bx(Expr::UnionType(entries))
        },
    ));

    rule!(empty_union_type<()>; raw_pair!(_) => ());

    rule!(non_empty_union_type_or_literal
          <(Option<(Label, ParsedExpr)>, BTreeMap<Label, ParsedExpr>)>; children!(
        [label_raw(l), expression(e), union_type_entries(entries)] => {
            (Some((l, e)), entries)
        },
        [label_raw(l), expression(e), non_empty_union_type_or_literal(rest)] => {
            let (x, mut entries) = rest;
            entries.insert(l, e);
            (x, entries)
        },
        [label_raw(l), expression(e)] => {
            let mut entries = BTreeMap::new();
            entries.insert(l, e);
            (None, entries)
        },
    ));

    rule!(union_type_entries<BTreeMap<Label, ParsedExpr>>; children!(
        [union_type_entry(entries..)] => entries.collect()
    ));

    rule!(union_type_entry<(Label, ParsedExpr)>; children!(
        [label_raw(name), expression(expr)] => (name, expr)
    ));

    rule!(non_empty_list_literal_raw<ParsedExpr> as expression; children!(
        [expression(items..)] => bx(Expr::NEListLit(items.collect()))
    ));

    rule!(final_expression<ParsedExpr> as expression; children!(
        [expression(e), EOI(_eoi)] => e
    ));
}

pub fn parse_expr(s: &str) -> ParseResult<crate::ParsedExpr<X>> {
    let mut pairs = DhallParser::parse(Rule::final_expression, s)?;
    let expr = parse_any(pairs.next().unwrap())?;
    assert_eq!(pairs.next(), None);
    match expr {
        ParsedValue::expression(e) => Ok(e),
        _ => unreachable!(),
    }
    // Ok(bx(Expr::BoolLit(false)))
}

#[test]
fn test_parse() {
    // let expr = r#"{ x = "foo", y = 4 }.x"#;
    // let expr = r#"(1 + 2) * 3"#;
    let expr = r#"(1) + 3 * 5"#;
    println!("{:?}", parse_expr(expr));
    match parse_expr(expr) {
        Err(e) => {
            println!("{:?}", e);
            println!("{}", e);
        }
        ok => println!("{:?}", ok),
    };
    // assert!(false);
}
