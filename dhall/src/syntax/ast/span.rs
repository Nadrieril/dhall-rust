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

impl ParsedSpan {
    pub(crate) fn to_input(&self) -> String {
        self.input.to_string()
    }
    /// Convert to a char range for consumption by annotate_snippets.
    /// This compensates for  https://github.com/rust-lang/annotate-snippets-rs/issues/24
    pub(crate) fn as_char_range(&self) -> (usize, usize) {
        (
            char_idx_from_byte_idx(&self.input, self.start),
            char_idx_from_byte_idx(&self.input, self.end),
        )
    }
}

impl Span {
    pub(crate) fn make(input: Rc<str>, sp: pest::Span) -> Self {
        Span::Parsed(ParsedSpan {
            input,
            start: sp.start(),
            end: sp.end(),
        })
    }

    /// Takes the union of the two spans, i.e. the range of input covered by the two spans plus any
    /// input between them. Assumes that the spans come from the same input. Fails if one of the
    /// spans does not point to an input location.
    pub fn union(&self, other: &Span) -> Self {
        use std::cmp::{max, min};
        use Span::*;
        match (self, other) {
            (Parsed(x), Parsed(y)) if Rc::ptr_eq(&x.input, &y.input) => {
                Parsed(ParsedSpan {
                    input: x.input.clone(),
                    start: min(x.start, y.start),
                    end: max(x.end, y.end),
                })
            }
            _ => panic!(
                "Tried to union incompatible spans: {:?} and {:?}",
                self, other
            ),
        }
    }

    /// Merges two spans assumed to point to a similar thing. If only one of them points to an
    /// input location, use that one.
    pub fn merge(&self, other: &Span) -> Self {
        use Span::*;
        match (self, other) {
            (Parsed(x), _) | (_, Parsed(x)) => Parsed(x.clone()),
            (Artificial, _) | (_, Artificial) => Artificial,
            (Decoded, Decoded) => Decoded,
        }
    }

    pub fn error(&self, message: impl Into<String>) -> String {
        use pest::error::{Error, ErrorVariant};
        use pest::Span;
        let message: String = message.into();
        let span = match self {
            self::Span::Parsed(span) => span,
            _ => return format!("[unknown location] {}", message),
        };
        let span = Span::new(&*span.input, span.start, span.end).unwrap();
        let err: ErrorVariant<!> = ErrorVariant::CustomError { message };
        let err = Error::new_from_span(err, span);
        format!("{}", err)
    }
}

/// Convert a byte idx into a string into a char idx for consumption by annotate_snippets.
fn char_idx_from_byte_idx(input: &str, idx: usize) -> usize {
    let char_idx = input
        .char_indices()
        .enumerate()
        .find(|(_, (i, _))| *i == idx)
        .map(|(i, (_, _))| i)
        // We should be able to unwrap() here, but somehow it panics on an example from
        // serde_dhall/lib.rs...
        .unwrap_or(0);
    // Unix-style newlines are counted as two chars (see
    // https://github.com/rust-lang/annotate-snippets-rs/issues/24).
    let nbr_newlines = input[..idx].chars().filter(|c| *c == '\n').count();
    let nbr_carriage_returns =
        input[..idx].chars().filter(|c| *c == '\r').count();
    char_idx + nbr_newlines - nbr_carriage_returns
}
