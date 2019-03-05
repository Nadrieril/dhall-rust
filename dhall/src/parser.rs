use std::collections::BTreeMap;
// use itertools::*;
use lalrpop_util;
use pest::iterators::Pair;
use pest::Parser;

use dhall_parser::{DhallParser, Rule};

use crate::core;
use crate::core::{bx, Builtin, Const, Expr, BinOp, V};
use crate::grammar;
use crate::grammar_util::{BoxExpr, ParsedExpr};
use crate::lexer::{Lexer, LexicalError, Tok};

pub fn parse_expr_lalrpop(
    s: &str,
) -> Result<BoxExpr, lalrpop_util::ParseError<usize, Tok, LexicalError>> {
    grammar::ExprParser::new().parse(Lexer::new(s))
    // Ok(bx(Expr::BoolLit(false)))
}

pub type ParseError = pest::error::Error<Rule>;

pub type ParseResult<T> = Result<T, ParseError>;

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
        let contents = pair.as_str().clone();
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

/* Macro to pattern-match iterators.
 * Returns `Result<_, IterMatchError<_>>`.
 *
 * Example:
 * ```
 * let vec = vec![1, 2, 3];
 *
 * match_iter!(vec.into_iter(); (x, y?, z) => {
 *  // x: T
 *  // y: Option<T>
 *  // z: T
 * })
 *
 * // or
 * match_iter!(vec.into_iter(); (x, y, z*) => {
 *  // x, y: T
 *  // z: impl Iterator<T>
 * })
 * ```
 *
*/
#[derive(Debug)]
enum IterMatchError<T> {
    NotEnoughItems,
    TooManyItems,
    NoMatchFound,
    Other(T), // Allow other macros to inject their own errors
}
macro_rules! match_iter {
    // Everything else pattern
    (@match 0, $iter:expr, $x:ident* $($rest:tt)*) => {
        match_iter!(@match 2, $iter $($rest)*);
        #[allow(unused_mut)]
        let mut $x = $iter;
    };
    // Alias to use in macros
    (@match 0, $iter:expr, $x:ident?? $($rest:tt)*) => {
        match_iter!(@match 2, $iter $($rest)*);
        #[allow(unused_mut)]
        let mut $x = $iter;
    };
    // Optional pattern
    (@match 0, $iter:expr, $x:ident? $($rest:tt)*) => {
        match_iter!(@match 1, $iter $($rest)*);
        #[allow(unused_mut)]
        let mut $x = $iter.next();
        match $iter.next() {
            Some(_) => break Err(IterMatchError::TooManyItems),
            None => {},
        };
    };
    // Normal pattern
    (@match 0, $iter:expr, $x:ident $($rest:tt)*) => {
        #[allow(unused_mut)]
        let mut $x = match $iter.next() {
            Some(x) => x,
            None => break Err(IterMatchError::NotEnoughItems),
        };
        match_iter!(@match 0, $iter $($rest)*);
    };
    // Normal pattern after a variable length one: declare reversed and take from the end
    (@match $w:expr, $iter:expr, $x:ident $($rest:tt)*) => {
        match_iter!(@match $w, $iter $($rest)*);
        #[allow(unused_mut)]
        let mut $x = match $iter.next_back() {
            Some(x) => x,
            None => break Err(IterMatchError::NotEnoughItems),
        };
    };

    // Check no elements remain
    (@match 0, $iter:expr $(,)*) => {
        match $iter.next() {
            Some(_) => break Err(IterMatchError::TooManyItems),
            None => {},
        };
    };
    (@match $_:expr, $iter:expr) => {};

    (@panic; $($args:tt)*) => {
        {
            let ret: Result<_, IterMatchError<()>> = match_iter!($($args)*);
            ret.unwrap()
        }
    };
    ($iter:expr; ($($args:tt)*) => $body:expr) => {
        {
            #[allow(unused_mut)]
            let mut iter = $iter;
            // Not a real loop; used for error handling
            let ret: Result<_, IterMatchError<_>> = loop {
                match_iter!(@match 0, iter, $($args)*);
                break Ok($body);
            };
            ret
        }
    };
}

/* Extends match_iter with typed matches. Takes a callback that determines
 * when a capture matches.
 * Returns `Result<_, IterMatchError<_>>`; errors returned by the callback will
 * get propagated using IterMatchError::Other.
 *
 * Example:
 * ```
 * macro_rules! callback {
 *     (@type_callback, positive, $x:expr) => {
 *         if $x >= 0 { Ok($x) } else { Err(()) }
 *     };
 *     (@type_callback, negative, $x:expr) => {
 *         if $x <= 0 { Ok($x) } else { Err(()) }
 *     };
 *     (@type_callback, any, $x:expr) => {
 *         Ok($x)
 *     };
 * }
 *
 * let vec = vec![-1, 2, 3];
 *
 * match_iter_typed!(callback; vec.into_iter();
 *     (x: positive, y?: negative, z: any) => { ... },
 * )
 * ```
 *
*/
macro_rules! match_iter_typed {
    // Collect untyped arguments to pass to match_iter!
    (@collect, ($($vars:tt)*), ($($args:tt)*), ($($acc:tt)*), ($x:ident : $ty:ident, $($rest:tt)*)) => {
        match_iter_typed!(@collect, ($($vars)*), ($($args)*), ($($acc)*, $x), ($($rest)*))
    };
    (@collect, ($($vars:tt)*), ($($args:tt)*), ($($acc:tt)*), ($x:ident? : $ty:ident, $($rest:tt)*)) => {
        match_iter_typed!(@collect, ($($vars)*), ($($args)*), ($($acc)*, $x?), ($($rest)*))
    };
    (@collect, ($($vars:tt)*), ($($args:tt)*), ($($acc:tt)*), ($x:ident* : $ty:ident, $($rest:tt)*)) => {
        match_iter_typed!(@collect, ($($vars)*), ($($args)*), ($($acc)*, $x??), ($($rest)*))
    };
    // Catch extra comma if exists
    (@collect, ($($vars:tt)*), ($($args:tt)*), (,$($acc:tt)*), ($(,)*)) => {
        match_iter_typed!(@collect, ($($vars)*), ($($args)*), ($($acc)*), ())
    };
    (@collect, ($iter:expr, $body:expr, $callback:ident, $error:ident), ($($args:tt)*), ($($acc:tt)*), ($(,)*)) => {
        match_iter!($iter; ($($acc)*) => {
            match_iter_typed!(@callback, $callback, $iter, $($args)*);
            $body
        })
    };

    // Pass the matches through the callback
    (@callback, $callback:ident, $iter:expr, $x:ident : $ty:ident $($rest:tt)*) => {
        let $x = $callback!(@type_callback, $ty, $x);
        #[allow(unused_mut)]
        let mut $x = match $x {
            Ok(x) => x,
            Err(e) => break Err(IterMatchError::Other(e)),
        };
        match_iter_typed!(@callback, $callback, $iter $($rest)*);
    };
    (@callback, $callback: ident, $iter:expr, $x:ident? : $ty:ident $($rest:tt)*) => {
        let $x = $x.map(|x| $callback!(@type_callback, $ty, x));
        #[allow(unused_mut)]
        let mut $x = match $x {
            Some(Ok(x)) => Some(x),
            Some(Err(e)) => break Err(IterMatchError::Other(e)),
            None => None,
        };
        match_iter_typed!(@callback, $callback, $iter $($rest)*);
    };
    (@callback, $callback: ident, $iter:expr, $x:ident* : $ty:ident $($rest:tt)*) => {
        let $x = $x.map(|x| $callback!(@type_callback, $ty, x)).collect();
        let $x: Vec<_> = match $x {
            Ok(x) => x,
            Err(e) => break Err(IterMatchError::Other(e)),
        };
        #[allow(unused_mut)]
        let mut $x = $x.into_iter();
        match_iter_typed!(@callback, $callback, $iter $($rest)*);
    };
    (@callback, $callback:ident, $iter:expr $(,)*) => {};

    ($callback:ident; $iter:expr; ($($args:tt)*) => $body:expr) => {
        {
            #[allow(unused_mut)]
            let mut iter = $iter;
            match_iter_typed!(@collect,
                (iter, $body, $callback, last_error),
                ($($args)*), (), ($($args)*,)
            )
        }
    };
}

/* Extends match_iter and match_iter_typed with branching.
 * Returns `Result<_, IterMatchError<_>>`; errors returned by the callback will
 * get propagated using IterMatchError::Other.
 * Allows multiple branches. The passed iterator must be Clone.
 * Will check the branches in order, testing each branch using the callback macro provided.
 *
 * Example:
 * ```
 * macro_rules! callback {
 *     (@type_callback, positive, $x:expr) => {
 *         if $x >= 0 { Ok($x) } else { Err(()) }
 *     };
 *     (@type_callback, negative, $x:expr) => {
 *         if $x <= 0 { Ok($x) } else { Err(()) }
 *     };
 *     (@type_callback, any, $x:expr) => {
 *         Ok($x)
 *     };
 *     (@branch_callback, typed, $($args:tt)*) => {
 *         match_iter_typed!(callback; $($args)*)
 *     };
 *     (@branch_callback, untyped, $($args:tt)*) => {
 *         match_iter!($($args)*)
 *     };
 * }
 *
 * let vec = vec![-1, 2, 3];
 *
 * match_iter_branching!(branch_callback; vec.into_iter();
 *     typed!(x: positive, y?: negative, z: any) => { ... },
 *     untyped!(x, y, z) => { ... },
 * )
 * ```
 *
*/
macro_rules! match_iter_branching {
    (@noclone, $callback:ident; $arg:expr; $( $submac:ident!($($args:tt)*) => $body:expr ),* $(,)*) => {
        {
            #[allow(unused_assignments)]
            let mut last_error = IterMatchError::NoMatchFound;
            // Not a real loop; used for error handling
            // Would use loop labels but they create warnings
            #[allow(unreachable_code)]
            loop {
                $(
                    let matched: Result<_, IterMatchError<_>> =
                        $callback!(@branch_callback, $submac, $arg; ($($args)*) => $body);
                    #[allow(unused_assignments)]
                    match matched {
                        Ok(v) => break Ok(v),
                        Err(e) => last_error = e,
                    };
                )*
                break Err(last_error);
            }
        }
    };
    ($callback:ident; $iter:expr; $($args:tt)*) => {
        {
            #[allow(unused_mut)]
            let mut iter = $iter;
            match_iter_branching!(@noclone, $callback; iter.clone(); $($args)*)
        }
    };
}

macro_rules! match_pair {
    (@type_callback, $ty:ident, $x:expr) => {
        $ty($x)
    };
    (@branch_callback, children, $pair:expr; $($args:tt)*) => {
        {
            #[allow(unused_mut)]
            let mut pairs = $pair.clone().into_inner();
            match_iter_typed!(match_pair; pairs; $($args)*)
        }
    };
    (@branch_callback, self, $pair:expr; ($x:ident : $ty:ident) => $body:expr) => {
        {
            let $x = match_pair!(@type_callback, $ty, $pair.clone());
            match $x {
                Ok($x) => Ok($body),
                Err(e) => Err(IterMatchError::Other(e)),
            }
        }
    };
    (@branch_callback, raw_pair, $pair:expr; ($x:ident) => $body:expr) => {
        {
            let $x = $pair.clone();
            Ok($body)
        }
    };
    (@branch_callback, captured_str, $pair:expr; ($x:ident) => $body:expr) => {
        {
            let $x = $pair.as_str();
            Ok($body)
        }
    };

    ($pair:expr; $($args:tt)*) => {
        {
            let pair = $pair;
            let result = match_iter_branching!(@noclone, match_pair; pair; $($args)*);
            result.map_err(|e| match e {
                IterMatchError::Other(e) => e,
                _ => custom_parse_error(&pair, "No match found".to_owned()),
            })
        }
    };
}

macro_rules! make_pest_parse_function {
    ($name:ident<$o:ty>; $submac:ident!( $($args:tt)* )) => (
        #[allow(unused_variables)]
        #[allow(non_snake_case)]
        fn $name<'a>(pair: Pair<'a, Rule>) -> ParseResult<$o> {
            $submac!(pair; $($args)*)
        }
    );
}

macro_rules! named {
    ($name:ident<$o:ty>; $($args:tt)*) => (
        make_pest_parse_function!($name<$o>; match_pair!( $($args)* ));
    );
}

macro_rules! rule {
    ($name:ident<$o:ty>; $($args:tt)*) => (
        make_pest_parse_function!($name<$o>; match_rule!(
            Rule::$name => match_pair!( $($args)* ),
        ));
    );
}

macro_rules! rule_group {
    ($name:ident<$o:ty>; $($ty:ident),*) => (
        make_pest_parse_function!($name<$o>; match_rule!(
            $(
                Rule::$ty => match_pair!(raw_pair!(p) => $ty(p)?),
            )*
        ));
    );
}

macro_rules! match_rule {
    ($pair:expr; $($pat:pat => $submac:ident!( $($args:tt)* ),)*) => {
        {
            #[allow(unreachable_patterns)]
            match $pair.as_rule() {
                $(
                    $pat => $submac!($pair; $($args)*),
                )*
                r => Err(custom_parse_error(&$pair, format!("Unexpected {:?}", r))),
            }
        }
    };
}

rule!(EOI<()>; children!() => ());

named!(str<&'a str>; captured_str!(s) => s.trim());

named!(raw_str<&'a str>; captured_str!(s) => s);

rule!(escaped_quote_pair<&'a str>;
    children!() => "''"
);
rule!(escaped_interpolation<&'a str>;
    children!() => "${"
);

rule!(single_quote_continue<Vec<&'a str>>;
    // TODO: handle interpolation
    // children!(c: expression, rest: single_quote_continue) => {
    //     rest.push(c); rest
    // },
    children!(c: escaped_quote_pair, rest: single_quote_continue) => {
        rest.push(c); rest
    },
    children!(c: escaped_interpolation, rest: single_quote_continue) => {
        rest.push(c); rest
    },
    // capture interpolation as string
    children!(c: raw_str, rest: single_quote_continue) => {
        rest.push(c); rest
    },
    children!() => {
        vec![]
    },
);

rule!(let_binding<(&'a str, Option<BoxExpr<'a>>, BoxExpr<'a>)>;
    children!(name: str, annot?: expression, expr: expression) => (name, annot, expr)
);

named!(record_entry<(&'a str, BoxExpr<'a>)>;
    children!(name: str, expr: expression) => (name, expr)
);

named!(partial_record_entries<(BoxExpr<'a>, BTreeMap<&'a str, ParsedExpr<'a>>)>;
    children!(expr: expression, entries*: record_entry) => {
        let mut map: BTreeMap<&str, ParsedExpr> = BTreeMap::new();
        for (n, e) in entries {
            map.insert(n, *e);
        }
        (expr, map)
    }
);

rule!(non_empty_record_literal<(BoxExpr<'a>, BTreeMap<&'a str, ParsedExpr<'a>>)>;
    self!(x: partial_record_entries) => x
);

rule!(non_empty_record_type<(BoxExpr<'a>, BTreeMap<&'a str, ParsedExpr<'a>>)>;
    self!(x: partial_record_entries) => x
);

rule!(union_type_entry<(&'a str, BoxExpr<'a>)>;
    children!(name: str, expr: expression) => (name, expr)
);

rule!(union_type_entries<BTreeMap<&'a str, ParsedExpr<'a>>>;
    children!(entries*: union_type_entry) => {
        let mut map: BTreeMap<&str, ParsedExpr> = BTreeMap::new();
        for (n, e) in entries {
            map.insert(n, *e);
        }
        map
    }
);

rule!(non_empty_union_type_or_literal
      <(Option<(&'a str, BoxExpr<'a>)>, BTreeMap<&'a str, ParsedExpr<'a>>)>;
    children!(label: str, e: expression, entries: union_type_entries) => {
        (Some((label, e)), entries)
    },
    children!(l: str, e: expression, rest: non_empty_union_type_or_literal) => {
        let (x, mut entries) = rest;
        entries.insert(l, *e);
        (x, entries)
    },
    children!(l: str, e: expression) => {
        let mut entries = BTreeMap::new();
        entries.insert(l, *e);
        (None, entries)
    },
);

rule!(empty_union_type<()>; children!() => ());

rule_group!(expression<BoxExpr<'a>>;
    identifier_raw,
    lambda_expression,
    ifthenelse_expression,
    let_expression,
    forall_expression,
    arrow_expression,
    merge_expression,
    empty_collection,
    non_empty_optional,

    annotated_expression,
    import_alt_expression,
    or_expression,
    plus_expression,
    text_append_expression,
    list_append_expression,
    and_expression,
    combine_expression,
    prefer_expression,
    combine_types_expression,
    times_expression,
    equal_expression,
    not_equal_expression,
    application_expression,

    selector_expression_raw,
    literal_expression_raw,
    empty_record_type,
    empty_record_literal,
    non_empty_record_type_or_literal,
    union_type_or_literal,
    non_empty_list_literal_raw,
    final_expression
);

// TODO: parse escapes and interpolation
rule!(double_quote_literal<String>;
    children!(strs*: raw_str) => {
        strs.collect()
    }
);
rule!(single_quote_literal<String>;
    children!(eol: raw_str, contents: single_quote_continue) => {
        contents.push(eol);
        contents.into_iter().rev().collect()
    }
);

rule!(double_literal_raw<core::Double>;
    raw_pair!(pair) => {
        pair.as_str().trim()
            .parse()
            .map_err(|e: std::num::ParseFloatError| custom_parse_error(&pair, format!("{}", e)))?
    }
);

rule!(minus_infinity_literal<()>; children!() => ());
rule!(plus_infinity_literal<()>; children!() => ());
rule!(NaN_raw<()>; children!() => ());

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

rule!(identifier_raw<BoxExpr<'a>>;
    children!(name: str, idx?: natural_literal_raw) => {
        match Builtin::parse(name) {
            Some(b) => bx(Expr::Builtin(b)),
            None => match name {
                "True" => bx(Expr::BoolLit(true)),
                "False" => bx(Expr::BoolLit(false)),
                "Type" => bx(Expr::Const(Const::Type)),
                "Kind" => bx(Expr::Const(Const::Kind)),
                name => bx(Expr::Var(V(name, idx.unwrap_or(0)))),
            }
        }
    }
);

rule!(lambda_expression<BoxExpr<'a>>;
    children!(label: str, typ: expression, body: expression) => {
        bx(Expr::Lam(label, typ, body))
    }
);

rule!(ifthenelse_expression<BoxExpr<'a>>;
    children!(cond: expression, left: expression, right: expression) => {
        bx(Expr::BoolIf(cond, left, right))
    }
);

rule!(let_expression<BoxExpr<'a>>;
    children!(bindings*: let_binding, final_expr: expression) => {
        bindings.fold(final_expr, |acc, x| bx(Expr::Let(x.0, x.1, x.2, acc)))
    }
);

rule!(forall_expression<BoxExpr<'a>>;
    children!(label: str, typ: expression, body: expression) => {
        bx(Expr::Pi(label, typ, body))
    }
);

rule!(arrow_expression<BoxExpr<'a>>;
    children!(typ: expression, body: expression) => {
        bx(Expr::Pi("_", typ, body))
    }
);

rule!(merge_expression<BoxExpr<'a>>;
    children!(x: expression, y: expression, z?: expression) => {
        bx(Expr::Merge(x, y, z))
    }
);

rule!(empty_collection<BoxExpr<'a>>;
    children!(x: str, y: expression) => {
       match x {
          "Optional" => bx(Expr::OptionalLit(Some(y), vec![])),
          "List" => bx(Expr::ListLit(Some(y), vec![])),
          _ => unreachable!(),
       }
    }
);

rule!(non_empty_optional<BoxExpr<'a>>;
    children!(x: expression, _y: str, z: expression) => {
        bx(Expr::OptionalLit(Some(z), vec![*x]))
    }
);

macro_rules! binop {
    ($rule:ident, $op:ident) => {
        rule!($rule<BoxExpr<'a>>;
            children!(first: expression, rest*: expression) => {
                rest.fold(first, |acc, e| bx(Expr::BinOp(BinOp::$op, acc, e)))
            }
        );
    };
}

rule!(annotated_expression<BoxExpr<'a>>;
    children!(e: expression, annot: expression) => {
        bx(Expr::Annot(e, annot))
    },
    children!(e: expression) => e,
);

binop!(import_alt_expression, ImportAlt);
binop!(or_expression, BoolOr);
binop!(plus_expression, NaturalPlus);
binop!(text_append_expression, TextAppend);
binop!(list_append_expression, ListAppend);
binop!(and_expression, BoolAnd);
binop!(combine_expression, Combine);
binop!(prefer_expression, Prefer);
binop!(combine_types_expression, CombineTypes);
binop!(times_expression, NaturalTimes);
binop!(equal_expression, BoolEQ);
binop!(not_equal_expression, BoolNE);

rule!(application_expression<BoxExpr<'a>>;
    children!(first: expression, rest*: expression) => {
        rest.fold(first, |acc, e| bx(Expr::App(acc, e)))
    }
);

rule!(selector_expression_raw<BoxExpr<'a>>;
    children!(first: expression, rest*: str) => {
        rest.fold(first, |acc, e| bx(Expr::Field(acc, e)))
    }
);

rule!(literal_expression_raw<BoxExpr<'a>>;
    children!(n: double_literal_raw) => bx(Expr::DoubleLit(n)),
    children!(n: minus_infinity_literal) => bx(Expr::DoubleLit(std::f64::NEG_INFINITY)),
    children!(n: plus_infinity_literal) => bx(Expr::DoubleLit(std::f64::INFINITY)),
    children!(n: NaN_raw) => bx(Expr::DoubleLit(std::f64::NAN)),
    children!(n: natural_literal_raw) => bx(Expr::NaturalLit(n)),
    children!(n: integer_literal_raw) => bx(Expr::IntegerLit(n)),
    children!(s: double_quote_literal) => bx(Expr::TextLit(s)),
    children!(s: single_quote_literal) => bx(Expr::TextLit(s)),
    children!(e: expression) => e,
);

rule!(empty_record_type<BoxExpr<'a>>;
    children!() => bx(Expr::Record(BTreeMap::new()))
);
rule!(empty_record_literal<BoxExpr<'a>>;
    children!() => bx(Expr::RecordLit(BTreeMap::new()))
);
rule!(non_empty_record_type_or_literal<BoxExpr<'a>>;
    children!(first_label: str, rest: non_empty_record_type) => {
        let (first_expr, mut map) = rest;
        map.insert(first_label, *first_expr);
        bx(Expr::Record(map))
    },
    children!(first_label: str, rest: non_empty_record_literal) => {
        let (first_expr, mut map) = rest;
        map.insert(first_label, *first_expr);
        bx(Expr::RecordLit(map))
    },
);

rule!(union_type_or_literal<BoxExpr<'a>>;
    children!(_e: empty_union_type) => {
        bx(Expr::Union(BTreeMap::new()))
    },
    children!(x: non_empty_union_type_or_literal) => {
        match x {
            (Some((l, e)), entries) => bx(Expr::UnionLit(l, e, entries)),
            (None, entries) => bx(Expr::Union(entries)),
        }
    },
);

rule!(non_empty_list_literal_raw<BoxExpr<'a>>;
    children!(items*: expression) => {
        bx(Expr::ListLit(None, items.map(|x| *x).collect()))
    }
);

rule!(final_expression<BoxExpr<'a>>;
    children!(e: expression, _eoi: EOI) => e
);

pub fn parse_expr_pest(s: &str) -> ParseResult<BoxExpr> {
    let pairs = DhallParser::parse(Rule::final_expression, s)?;
    // Match the only item in the pairs iterator
    match_iter!(@panic; pairs; (p) => expression(p))
    // Ok(bx(Expr::BoolLit(false)))
}

#[test]
fn test_parse() {
    use crate::core::Expr::*;
    use crate::core::BinOp::*;
    // let expr = r#"{ x = "foo", y = 4 }.x"#;
    // let expr = r#"(1 + 2) * 3"#;
    let expr = r#"if True then 1 + 3 * 5 else 2"#;
    println!("{:?}", parse_expr_lalrpop(expr));
    use std::thread;
    // I don't understand why it stack overflows even on tiny expressions...
    thread::Builder::new()
        .stack_size(3 * 1024 * 1024)
        .spawn(move || match parse_expr_pest(expr) {
            Err(e) => {
                println!("{:?}", e);
                println!("{}", e);
            }
            ok => println!("{:?}", ok),
        })
        .unwrap()
        .join()
        .unwrap();
    // assert_eq!(parse_expr_pest(expr).unwrap(), parse_expr_lalrpop(expr).unwrap());
    // assert!(false);

    println!("test {:?}", parse_expr_lalrpop("3 + 5 * 10"));
    assert!(parse_expr_lalrpop("22").is_ok());
    assert!(parse_expr_lalrpop("(22)").is_ok());
    assert_eq!(
        parse_expr_lalrpop("3 + 5 * 10").ok(),
        Some(Box::new(BinOp(NaturalPlus,
            Box::new(NaturalLit(3)),
            Box::new(BinOp(NaturalTimes,
                Box::new(NaturalLit(5)),
                Box::new(NaturalLit(10))
            ))
        )))
    );
    // The original parser is apparently right-associative
    assert_eq!(
        parse_expr_lalrpop("2 * 3 * 4").ok(),
        Some(Box::new(BinOp(NaturalTimes,
            Box::new(NaturalLit(2)),
            Box::new(BinOp(NaturalTimes,
                Box::new(NaturalLit(3)),
                Box::new(NaturalLit(4))
            ))
        )))
    );
    assert!(parse_expr_lalrpop("((((22))))").is_ok());
    assert!(parse_expr_lalrpop("((22)").is_err());
    println!("{:?}", parse_expr_lalrpop("\\(b : Bool) -> b == False"));
    assert!(parse_expr_lalrpop("\\(b : Bool) -> b == False").is_ok());
    println!("{:?}", parse_expr_lalrpop("foo.bar"));
    assert!(parse_expr_lalrpop("foo.bar").is_ok());
    assert!(parse_expr_lalrpop("[] : List Bool").is_ok());

    // println!("{:?}", parse_expr_lalrpop("< Left = True | Right : Natural >"));
    // println!("{:?}", parse_expr_lalrpop(r#""bl${42}ah""#));
    // assert!(parse_expr_lalrpop("< Left = True | Right : Natural >").is_ok());
}
