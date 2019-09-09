use pest::error::{Error, ErrorVariant};
use pest::iterators::Pair;
use pest::Span;

pub use dhall_proc_macros::{make_parser, parse_children};

/// Carries a pest Pair alongside custom user data.
#[derive(Debug, Clone)]
pub struct ParseInput<'input, 'data, Rule, Data>
where
    Rule: pest::RuleType,
{
    pair: Pair<'input, Rule>,
    user_data: &'data Data,
}

impl<'input, 'data, Rule, Data> ParseInput<'input, 'data, Rule, Data>
where
    Rule: pest::RuleType,
{
    pub fn new(pair: Pair<'input, Rule>, user_data: &'data Data) -> Self {
        ParseInput { pair, user_data }
    }
    /// Create an error that points to the span of the input.
    pub fn error(&self, message: String) -> Error<Rule> {
        let message = format!(
            "{} while matching on:\n{}",
            message,
            debug_pair(self.pair.clone())
        );
        Error::new_from_span(
            ErrorVariant::CustomError { message },
            self.as_span(),
        )
    }
    /// Reconstruct the input with a new pair, passing the user data along.
    pub fn with_pair(&self, new_pair: Pair<'input, Rule>) -> Self {
        ParseInput {
            pair: new_pair,
            user_data: self.user_data,
        }
    }
    /// If the contained pair has exactly one child, return a new Self containing it.
    pub fn single_child(&self) -> Option<Self> {
        let mut children = self.pair.clone().into_inner();
        if let Some(child) = children.next() {
            if children.next().is_none() {
                return Some(self.with_pair(child));
            }
        }
        None
    }

    pub fn user_data(&self) -> &'data Data {
        self.user_data
    }
    pub fn as_pair(&self) -> &Pair<'input, Rule> {
        &self.pair
    }
    pub fn as_span(&self) -> Span<'input> {
        self.pair.as_span()
    }
    pub fn as_str(&self) -> &'input str {
        self.pair.as_str()
    }
    pub fn as_rule(&self) -> Rule {
        self.pair.as_rule()
    }
}

/// Used by the macros.
pub trait PestConsumer {
    type Rule: pest::RuleType;
    fn rule_alias(rule: Self::Rule) -> String;
    fn allows_shortcut(rule: Self::Rule) -> bool;
}

/// Pretty-print a pair and its nested children.
fn debug_pair<Rule: pest::RuleType>(pair: Pair<Rule>) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    fn aux<Rule: pest::RuleType>(
        s: &mut String,
        indent: usize,
        prefix: String,
        pair: Pair<Rule>,
    ) {
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
