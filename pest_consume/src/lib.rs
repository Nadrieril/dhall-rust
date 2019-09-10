use pest::error::{Error, ErrorVariant};
use pest::iterators::Pair;
use pest::Span;

pub use pest_consume_macros::{make_parser, match_inputs};

/// Carries a pest Pair alongside custom user data.
#[derive(Debug)]
pub struct ParseInput<'input, 'data, Rule, Data>
where
    Rule: pest::RuleType,
{
    pair: Pair<'input, Rule>,
    user_data: &'data Data,
}

/// Iterator over `ParseInput`s. It is created by `ParseInput::children`.
#[derive(Debug)]
pub struct ParseInputs<'input, 'data, Rule, Data>
where
    Rule: pest::RuleType,
{
    input: ParseInput<'input, 'data, Rule, Data>,
    pairs: pest::iterators::Pairs<'input, Rule>,
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
    /// Return an iterator over the children of this input
    // Can't use `-> impl Iterator` because of weird lifetime limitations
    // (see https://github.com/rust-lang/rust/issues/61997).
    pub fn children(&self) -> ParseInputs<'input, 'data, Rule, Data> {
        ParseInputs {
            input: self.clone(),
            pairs: self.as_pair().clone().into_inner(),
        }
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
    pub fn as_rule_alias<T>(&self) -> String
    where
        T: PestConsumer<Rule = Rule>,
    {
        T::rule_alias(self.as_rule())
    }
}

impl<'input, 'data, Rule, Data> ParseInputs<'input, 'data, Rule, Data>
where
    Rule: pest::RuleType,
{
    /// Create an error that points to the span of the input.
    pub fn error(&self, message: String) -> Error<Rule> {
        self.input.error(message)
    }
    pub fn aliased_rules<T>(&self) -> Vec<String>
    where
        T: PestConsumer<Rule = Rule>,
    {
        self.clone().map(|p| p.as_rule_alias::<T>()).collect()
    }
}

/// Used by the macros.
pub trait PestConsumer {
    type Rule: pest::RuleType;
    fn rule_alias(rule: Self::Rule) -> String;
    fn allows_shortcut(rule: Self::Rule) -> bool;
}

impl<'input, 'data, Rule, Data> Iterator
    for ParseInputs<'input, 'data, Rule, Data>
where
    Rule: pest::RuleType,
{
    type Item = ParseInput<'input, 'data, Rule, Data>;

    fn next(&mut self) -> Option<Self::Item> {
        let child_pair = self.pairs.next()?;
        let child = self.input.with_pair(child_pair);
        Some(child)
    }
}

impl<'input, 'data, Rule, Data> DoubleEndedIterator
    for ParseInputs<'input, 'data, Rule, Data>
where
    Rule: pest::RuleType,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        let child_pair = self.pairs.next_back()?;
        let child = self.input.with_pair(child_pair);
        Some(child)
    }
}

// Manual impl to avoid stupid `Data: Clone` trait bound
impl<'input, 'data, Rule, Data> Clone for ParseInput<'input, 'data, Rule, Data>
where
    Rule: pest::RuleType,
{
    fn clone(&self) -> Self {
        ParseInput {
            pair: self.pair.clone(),
            user_data: self.user_data,
        }
    }
}

// Manual impl to avoid stupid `Data: Clone` trait bound
impl<'input, 'data, Rule, Data> Clone for ParseInputs<'input, 'data, Rule, Data>
where
    Rule: pest::RuleType,
{
    fn clone(&self) -> Self {
        ParseInputs {
            input: self.input.clone(),
            pairs: self.pairs.clone(),
        }
    }
}
