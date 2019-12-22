#![doc(html_root_url = "https://docs.rs/abnf_to_pest/0.2.0")]

//! A tiny crate that helps convert ABNF grammars to [pest][pest].
//!
//! Example usage:
//! ```
//! let abnf_path = "src/grammar.abnf";
//! let pest_path = "src/grammar.pest";
//!
//! let mut file = File::open(abnf_path)?;
//! let mut data = Vec::new();
//! file.read_to_end(&mut data)?;
//! data.push('\n' as u8);
//!
//! let mut rules = abnf_to_pest::parse_abnf(&data)?;
//! rules.remove("some_inconvenient_rule");
//!
//! let mut file = File::create(pest_path)?;
//! writeln!(&mut file, "{}", render_rules_to_pest(rules).pretty(80))?;
//! ```
//!
//! [pest]: https://pest.rs

use abnf::types::{Node, NumVal, Repeat, Rule};
use indexmap::map::IndexMap;
use itertools::Itertools;
use pretty::{BoxDoc, Doc};

trait Pretty {
    fn pretty(&self) -> Doc<'static, BoxDoc<'static, ()>>;
}

impl Pretty for Node {
    fn pretty(&self) -> Doc<'static, BoxDoc<'static, ()>> {
        use Node::*;
        match self {
            Alternation(nodes) => Doc::intersperse(
                nodes.iter().map(|x| x.pretty().nest(2).group()),
                Doc::space().append(Doc::text("| ")),
            ),
            Concatenation(nodes) => Doc::intersperse(
                nodes.iter().map(|x| x.pretty()),
                Doc::space().append(Doc::text("~ ")),
            ),
            Repetition(rep) => {
                rep.get_node().pretty().append(rep.get_repeat().pretty())
            }
            Rulename(s) => Doc::text(escape_rulename(s)),
            Group(n) => Doc::text("(")
                .append(n.pretty().nest(4).group())
                .append(Doc::text(")")),
            Optional(n) => Doc::text("(")
                .append(n.pretty().nest(4).group())
                .append(Doc::text(")?")),
            CharVal(s) => Doc::text(format!(
                "^\"{}\"",
                s.replace("\"", "\\\"").replace("\\", "\\\\")
            )),
            NumVal(r) => r.pretty(),
            ProseVal(_) => unimplemented!(),
        }
    }
}

impl Pretty for Repeat {
    fn pretty(&self) -> Doc<'static, BoxDoc<'static, ()>> {
        Doc::text(match (self.get_min().unwrap_or(0), self.get_max()) {
            (0, None) => "*".into(),
            (1, None) => "+".into(),
            (0, Some(1)) => "?".into(),
            (min, None) => format!("{{{},}}", min),
            (min, Some(max)) if min == max => format!("{{{}}}", min),
            (min, Some(max)) => format!("{{{},{}}}", min, max),
        })
    }
}

impl Pretty for NumVal {
    fn pretty(&self) -> Doc<'static, BoxDoc<'static, ()>> {
        use NumVal::*;
        Doc::text(match self {
            Range(x, y) => {
                format!("'{}'..'{}'", format_char(*x), format_char(*y))
            }
            Terminal(v) => {
                format!("\"{}\"", v.iter().map(|x| format_char(*x)).join(""))
            }
        })
    }
}

/// Escape the rule name to be a valid Rust identifier.
///
/// Replaces e.g. `if` with `if_`, and `rule-name` with `rule_name`.
/// Also changes `whitespace` to `whitespace_` because of https://github.com/pest-parser/pest/pull/374
/// Also changes `Some` and `None` to `Some_` and `None_`, because it was such a pain to work around.
pub fn escape_rulename(x: &str) -> String {
    let x = x.replace("-", "_");
    if x == "if"
        || x == "else"
        || x == "as"
        || x == "let"
        || x == "in"
        || x == "fn"
        // Not required but such a pain
        || x == "Some"
        || x == "None"
        // TODO: remove when https://github.com/pest-parser/pest/pull/375 gets into a release
        || x == "whitespace"
    {
        x + "_"
    } else {
        x.clone()
    }
}

fn format_char(x: u32) -> String {
    if x <= u32::from(u8::max_value()) {
        let x: u8 = x as u8;
        if x.is_ascii_graphic() {
            let x: char = x as char;
            if x != '"' && x != '\'' && x != '\\' {
                return x.to_string();
            }
        }
    }
    format!("\\u{{{:02X}}}", x)
}

/// Allow control over some of the pest properties of the outputted rule
#[derive(Debug, Clone)]
pub struct PestyRule {
    pub silent: bool,
    pub node: Node,
}

impl Pretty for (String, PestyRule) {
    fn pretty(&self) -> Doc<'static, BoxDoc<'static, ()>> {
        let (name, rule) = self;
        Doc::nil()
            .append(Doc::text(name.clone()))
            .append(Doc::text(" = "))
            .append(Doc::text(if rule.silent { "_" } else { "" }))
            .append(Doc::text("{"))
            .append(Doc::space().append(rule.node.pretty()).nest(2))
            .append(Doc::space())
            .append(Doc::text("}"))
            .group()
    }
}

/// Parse an abnf file. Returns a map of rules.
pub fn parse_abnf(
    data: &str,
) -> Result<IndexMap<String, PestyRule>, std::io::Error> {
    let make_err =
        |e| std::io::Error::new(std::io::ErrorKind::Other, format!("{}", e));
    let rules: Vec<Rule> = abnf::rulelist(data).map_err(make_err)?;
    Ok(rules
        .into_iter()
        .map(|rule| {
            (
                escape_rulename(rule.get_name()),
                PestyRule {
                    silent: false,
                    node: rule.get_node().clone(),
                },
            )
        })
        .collect())
}

pub fn render_rules_to_pest<I>(
    rules: I,
) -> Doc<'static, BoxDoc<'static, ()>, ()>
where
    I: IntoIterator<Item = (String, PestyRule)>,
{
    let pretty_rules = rules.into_iter().map(|x| x.pretty());
    let doc: Doc<_> = Doc::intersperse(pretty_rules, Doc::newline());
    doc
}
