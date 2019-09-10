use pest::error::{Error, ErrorVariant};
use pest::iterators::{Pair, Pairs};
use pest::Parser as PestParser;
use pest::{RuleType, Span};

pub use pest_consume_macros::{make_parser, match_inputs};

static UNIT: () = ();

/// Carries a pest Pair alongside custom user data.
#[derive(Debug)]
pub struct ParseInput<'input, 'data, Rule: RuleType, Data> {
    pair: Pair<'input, Rule>,
    user_data: &'data Data,
}

/// Iterator over `ParseInput`s. It is created by `ParseInput::children` or `ParseInputs::new`.
#[derive(Debug)]
pub struct ParseInputs<'input, 'data, Rule: RuleType, Data> {
    pairs: Pairs<'input, Rule>,
    span: Span<'input>,
    user_data: &'data Data,
}

impl<'i, 'd, R: RuleType, D> ParseInput<'i, 'd, R, D> {
    pub fn new(pair: Pair<'i, R>, user_data: &'d D) -> Self {
        ParseInput { pair, user_data }
    }
    /// Create an error that points to the span of the input.
    pub fn error(&self, message: String) -> Error<R> {
        Error::new_from_span(
            ErrorVariant::CustomError { message },
            self.as_span(),
        )
    }
    /// Reconstruct the input with a new pair, passing the user data along.
    pub fn with_pair(&self, new_pair: Pair<'i, R>) -> Self {
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
    pub fn children(&self) -> ParseInputs<'i, 'd, R, D> {
        ParseInputs {
            pairs: self.as_pair().clone().into_inner(),
            span: self.as_span(),
            user_data: self.user_data(),
        }
    }

    pub fn user_data(&self) -> &'d D {
        self.user_data
    }
    pub fn as_pair(&self) -> &Pair<'i, R> {
        &self.pair
    }
    pub fn as_span(&self) -> Span<'i> {
        self.pair.as_span()
    }
    pub fn as_str(&self) -> &'i str {
        self.pair.as_str()
    }
    pub fn as_rule(&self) -> R {
        self.pair.as_rule()
    }
    pub fn as_rule_alias<C>(&self) -> String
    where
        C: PestConsumer<Rule = R>,
        <C as PestConsumer>::Parser: PestParser<R>,
    {
        C::rule_alias(self.as_rule())
    }
}

impl<'i, 'd, R: RuleType, D> ParseInputs<'i, 'd, R, D> {
    /// `input` must be the _original_ input that `pairs` is pointing to.
    pub fn new(input: &'i str, pairs: Pairs<'i, R>, user_data: &'d D) -> Self {
        let span = Span::new(input, 0, input.len()).unwrap();
        ParseInputs {
            pairs,
            span,
            user_data,
        }
    }
    /// Create an error that points to the span of the input.
    pub fn error(&self, message: String) -> Error<R> {
        Error::new_from_span(
            ErrorVariant::CustomError { message },
            self.span.clone(),
        )
    }
    pub fn aliased_rules<C>(&self) -> Vec<String>
    where
        C: PestConsumer<Rule = R>,
        <C as PestConsumer>::Parser: PestParser<R>,
    {
        self.clone().map(|p| p.as_rule_alias::<C>()).collect()
    }
    /// Reconstruct the input with a new pair, passing the user data along.
    fn with_pair(&self, new_pair: Pair<'i, R>) -> ParseInput<'i, 'd, R, D> {
        ParseInput::new(new_pair, self.user_data)
    }
}

/// Used by the macros.
pub trait PestConsumer {
    type Rule: RuleType;
    type Parser: PestParser<Self::Rule>;
    fn rule_alias(rule: Self::Rule) -> String;
    fn allows_shortcut(rule: Self::Rule) -> bool;

    fn parse_with_userdata<'i, 'd, D>(
        rule: Self::Rule,
        input_str: &'i str,
        user_data: &'d D,
    ) -> Result<ParseInputs<'i, 'd, Self::Rule, D>, Error<Self::Rule>> {
        let pairs = Self::Parser::parse(rule, input_str)?;
        Ok(ParseInputs::new(input_str, pairs, user_data))
    }

    fn parse<'i>(
        rule: Self::Rule,
        input_str: &'i str,
    ) -> Result<ParseInputs<'i, 'static, Self::Rule, ()>, Error<Self::Rule>>
    {
        Self::parse_with_userdata(rule, input_str, &UNIT)
    }
}

impl<'i, 'd, R: RuleType, D> Iterator for ParseInputs<'i, 'd, R, D> {
    type Item = ParseInput<'i, 'd, R, D>;

    fn next(&mut self) -> Option<Self::Item> {
        let child_pair = self.pairs.next()?;
        let child = self.with_pair(child_pair);
        Some(child)
    }
}

impl<'i, 'd, R: RuleType, D> DoubleEndedIterator for ParseInputs<'i, 'd, R, D> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let child_pair = self.pairs.next_back()?;
        let child = self.with_pair(child_pair);
        Some(child)
    }
}

// Manual impl to avoid stupid `D: Clone` trait bound
impl<'i, 'd, R: RuleType, D> Clone for ParseInput<'i, 'd, R, D> {
    fn clone(&self) -> Self {
        ParseInput {
            pair: self.pair.clone(),
            user_data: self.user_data,
        }
    }
}

// Manual impl to avoid stupid `D: Clone` trait bound
impl<'i, 'd, R: RuleType, D> Clone for ParseInputs<'i, 'd, R, D> {
    fn clone(&self) -> Self {
        ParseInputs {
            pairs: self.pairs.clone(),
            span: self.span.clone(),
            user_data: self.user_data,
        }
    }
}
