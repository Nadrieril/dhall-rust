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

/// A location in the source text
#[derive(Debug, Clone)]
pub enum Span {
    Parsed(ParsedSpan),
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
            (Parsed(x), Parsed(y)) => Span::Parsed(ParsedSpan {
                input: x.input.clone(),
                start: min(x.start, y.start),
                end: max(x.start, y.start),
            }),
        }
    }
}
