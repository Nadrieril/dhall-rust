/// `pest_consume` extends [pest] to make it easy to consume the resulting pest parse tree.
/// Given a grammar file, pest generates a parser that outputs an untyped parse tree. Then that
/// parse tree needs to be transformed into whatever datastructures your application uses.
/// `pest_consume` provides two powerful macros to make this easy.
use pest::error::Error;

pub use pest::error::Error;
use pest::Parser as PestParser;
use pest::RuleType;
pub use pest_derive::Parser;

#[proc_macro_hack::proc_macro_hack]
pub use pest_consume_macros::match_nodes;
pub use pest_consume_macros::parser;

mod node {
    use super::Parser;
    use pest::error::{Error, ErrorVariant};
    use pest::iterators::{Pair, Pairs};
    use pest::Parser as PestParser;
    use pest::{RuleType, Span};

    /// Carries a pest Pair alongside custom user data.
    #[derive(Debug, Clone)]
    pub struct Node<'input, Rule: RuleType, Data> {
        pair: Pair<'input, Rule>,
        user_data: Data,
    }

    /// Iterator over `Node`s. It is created by `Node::children` or `Nodes::new`.
    #[derive(Debug, Clone)]
    pub struct Nodes<'input, Rule: RuleType, Data> {
        pairs: Pairs<'input, Rule>,
        span: Span<'input>,
        user_data: Data,
    }

    impl<'i, R: RuleType, D> Node<'i, R, D> {
        pub fn new(pair: Pair<'i, R>, user_data: D) -> Self {
            Node { pair, user_data }
        }
        /// Create an error that points to the span of the input.
        pub fn error(&self, message: String) -> Error<R> {
            Error::new_from_span(
                ErrorVariant::CustomError { message },
                self.as_span(),
            )
        }
        /// Reconstruct the input with a new pair, passing the user data along.
        pub fn with_pair(&self, new_pair: Pair<'i, R>) -> Self
        where
            D: Clone,
        {
            Node {
                pair: new_pair,
                user_data: self.user_data.clone(),
            }
        }
        /// If the contained pair has exactly one child, return a new Self containing it.
        pub fn single_child(&self) -> Option<Self>
        where
            D: Clone,
        {
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
        pub fn children(&self) -> Nodes<'i, R, D>
        where
            D: Clone,
        {
            Nodes {
                pairs: self.as_pair().clone().into_inner(),
                span: self.as_span(),
                user_data: self.user_data(),
            }
        }

        pub fn user_data(&self) -> D
        where
            D: Clone,
        {
            self.user_data.clone()
        }
        pub fn as_pair(&self) -> &Pair<'i, R> {
            &self.pair
        }
        pub fn into_pair(self) -> Pair<'i, R> {
            self.pair
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
        pub fn as_aliased_rule<C>(&self) -> C::AliasedRule
        where
            C: Parser<Rule = R>,
            <C as Parser>::Parser: PestParser<R>,
        {
            C::rule_alias(self.as_rule())
        }
    }

    impl<'i, R: RuleType, D> Nodes<'i, R, D> {
        /// `input` must be the _original_ input that `pairs` is pointing to.
        pub fn new(input: &'i str, pairs: Pairs<'i, R>, user_data: D) -> Self {
            let span = Span::new(input, 0, input.len()).unwrap();
            Nodes {
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
        pub fn aliased_rules<C>(&self) -> Vec<C::AliasedRule>
        where
            D: Clone,
            C: Parser<Rule = R>,
            <C as Parser>::Parser: PestParser<R>,
        {
            self.clone().map(|p| p.as_aliased_rule::<C>()).collect()
        }
        /// Reconstruct the input with a new pair, passing the user data along.
        fn with_pair(&self, new_pair: Pair<'i, R>) -> Node<'i, R, D>
        where
            D: Clone,
        {
            Node::new(new_pair, self.user_data.clone())
        }

        pub fn as_pairs(&self) -> &Pairs<'i, R> {
            &self.pairs
        }
        pub fn into_pairs(self) -> Pairs<'i, R> {
            self.pairs
        }
    }

    impl<'i, R, D> Iterator for Nodes<'i, R, D>
    where
        R: RuleType,
        D: Clone,
    {
        type Item = Node<'i, R, D>;

        fn next(&mut self) -> Option<Self::Item> {
            let child_pair = self.pairs.next()?;
            let child = self.with_pair(child_pair);
            Some(child)
        }
    }

    impl<'i, R, D> DoubleEndedIterator for Nodes<'i, R, D>
    where
        R: RuleType,
        D: Clone,
    {
        fn next_back(&mut self) -> Option<Self::Item> {
            let child_pair = self.pairs.next_back()?;
            let child = self.with_pair(child_pair);
            Some(child)
        }
    }
}

pub use node::{Node, Nodes};

/// Used by the macros.
/// Do not implement manually.
pub trait Parser {
    type Rule: RuleType;
    type AliasedRule: RuleType;
    type Parser: PestParser<Self::Rule>;

    fn rule_alias(rule: Self::Rule) -> Self::AliasedRule;
    fn allows_shortcut(rule: Self::Rule) -> bool;

    /// Parses a `&str` starting from `rule`
    fn parse<'i>(
        rule: Self::Rule,
        input_str: &'i str,
    ) -> Result<Nodes<'i, Self::Rule, ()>, Error<Self::Rule>> {
        Self::parse_with_userdata(rule, input_str, ())
    }

    /// Parses a `&str` starting from `rule`, carrying `user_data` through the parser methods.
    fn parse_with_userdata<'i, D>(
        rule: Self::Rule,
        input_str: &'i str,
        user_data: D,
    ) -> Result<Nodes<'i, Self::Rule, D>, Error<Self::Rule>> {
        let pairs = Self::Parser::parse(rule, input_str)?;
        Ok(Nodes::new(input_str, pairs, user_data))
    }
}
