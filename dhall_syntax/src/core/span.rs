use std::rc::Rc;

/// A location in the source text
#[derive(Debug, Clone)]
pub struct ParsedSpan {
    input: Rc<str>,
    /// # Safety
    ///
    /// Must be a valid character boundary index into `input`.
    start: usize,
    /// # Safety
    ///
    /// Must be a valid character boundary index into `input`.
    end: usize,
}

#[derive(Debug, Clone)]
pub enum Span {
    /// A location in the source text
    Parsed(ParsedSpan),
    /// For expressions obtained from decoding binary
    Decoded,
    /// For expressions constructed during normalization/typecheck
    Artificial,
    /// For when there should be a span but it's not done yet
    /// TODO: properly handle spans
    PlaceHolder,
}

impl Span {
    pub(crate) fn make(input: Rc<str>, sp: pest::Span) -> Self {
        Span::Parsed(ParsedSpan {
            input,
            start: sp.start(),
            end: sp.end(),
        })
    }

    /// Takes the union of the two spans. Assumes that the spans come from the same input.
    /// This will also capture any input between the spans.
    pub fn union(&self, other: &Span) -> Self {
        use std::cmp::{max, min};
        use Span::*;
        match (self, other) {
            (Parsed(x), Parsed(y)) => Parsed(ParsedSpan {
                input: x.input.clone(),
                start: min(x.start, y.start),
                end: max(x.end, y.end),
            }),
            _ => panic!(
                "Tried to union incompatible spans: {:?} and {:?}",
                self, other
            ),
        }
    }
}
