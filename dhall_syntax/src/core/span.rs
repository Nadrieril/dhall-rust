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

    pub fn error(&self, message: impl Into<String>) -> String {
        use pest::error::{Error, ErrorVariant};
        use pest::Span;
        let message: String = message.into();
        let span = match self {
            self::Span::Parsed(span) => span,
            _ => return format!("Unknown location: {}", message),
        };
        let span = Span::new(&*span.input, span.start, span.end).unwrap();
        let err: ErrorVariant<!> = ErrorVariant::CustomError { message };
        let err = Error::new_from_span(err, span);
        format!("{}", err)
    }
}
