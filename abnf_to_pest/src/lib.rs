#![doc(html_root_url = "https://docs.rs/abnf_to_pest/0.5.0")]

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

use abnf::types::{Node, Repeat, Rule, TerminalValues};
use indexmap::map::IndexMap;
use itertools::Itertools;
use pretty::BoxDoc;

trait Pretty {
    fn pretty(&self) -> BoxDoc<'static>;
}

impl Pretty for Node {
    fn pretty(&self) -> BoxDoc<'static> {
        use Node::*;
        match self {
            Alternation(nodes) => BoxDoc::intersperse(
                nodes.iter().map(|x| x.pretty().nest(2).group()),
                BoxDoc::space().append(BoxDoc::text("| ")),
            ),
            Concatenation(nodes) => BoxDoc::intersperse(
                nodes.iter().map(|x| x.pretty()),
                BoxDoc::space().append(BoxDoc::text("~ ")),
            ),
            Repetition(rep) => {
                rep.node().pretty().append(rep.repeat().pretty())
            }
            Rulename(s) => BoxDoc::text(escape_rulename(s)),
            Group(n) => BoxDoc::text("(")
                .append(n.pretty().nest(4).group())
                .append(BoxDoc::text(")")),
            Optional(n) => BoxDoc::text("(")
                .append(n.pretty().nest(4).group())
                .append(BoxDoc::text(")?")),
            String(s) => BoxDoc::text(format!(
                "^\"{}\"",
                s.replace("\"", "\\\"").replace("\\", "\\\\")
            )),
            TerminalValues(r) => r.pretty(),
            Prose(_) => unimplemented!(),
        }
    }
}

impl Pretty for Repeat {
    fn pretty(&self) -> BoxDoc<'static> {
        BoxDoc::text(match (self.min().unwrap_or(0), self.max()) {
            (0, None) => "*".into(),
            (1, None) => "+".into(),
            (0, Some(1)) => "?".into(),
            (min, None) => format!("{{{},}}", min),
            (min, Some(max)) if min == max => format!("{{{}}}", min),
            (min, Some(max)) => format!("{{{},{}}}", min, max),
        })
    }
}

impl Pretty for TerminalValues {
    fn pretty(&self) -> BoxDoc<'static> {
        use TerminalValues::*;
        BoxDoc::text(match self {
            Range(x, y) => {
                format!("'{}'..'{}'", format_char(*x), format_char(*y))
            }
            Concatenation(v) => {
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
        x
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
    fn pretty(&self) -> BoxDoc<'static> {
        let (name, rule) = self;
        BoxDoc::nil()
            .append(BoxDoc::text(name.clone()))
            .append(BoxDoc::text(" = "))
            .append(BoxDoc::text(if rule.silent { "_" } else { "" }))
            .append(BoxDoc::text("{"))
            .append(BoxDoc::space().append(rule.node.pretty()).nest(2))
            .append(BoxDoc::space())
            .append(BoxDoc::text("}"))
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
                escape_rulename(rule.name()),
                PestyRule {
                    silent: false,
                    node: rule.node().clone(),
                },
            )
        })
        .collect())
}

pub fn render_rules_to_pest<I>(rules: I) -> BoxDoc<'static>
where
    I: IntoIterator<Item = (String, PestyRule)>,
{
    let pretty_rules = rules.into_iter().map(|x| x.pretty());
    BoxDoc::intersperse(pretty_rules, BoxDoc::hardline())
}
