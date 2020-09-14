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
    /// Desugarings
    DuplicateRecordFieldsSugar,
    DottedFieldSugar,
    RecordPunSugar,
    /// For expressions obtained from decoding binary
    Decoded,
    /// For expressions constructed during normalization/typecheck
    Artificial,
}

impl ParsedSpan {
    pub fn to_input(&self) -> String {
        self.input.to_string()
    }
    /// Convert to a char range for consumption by annotate_snippets.
    /// This compensates for  https://github.com/rust-lang/annotate-snippets-rs/issues/24
    pub fn as_char_range(&self) -> (usize, usize) {
        (
            char_idx_from_byte_idx(&self.input, self.start),
            char_idx_from_byte_idx(&self.input, self.end),
        )
    }
}

impl Span {
    pub fn make(input: Rc<str>, sp: pest::Span) -> Self {
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
            (Parsed(_), Parsed(_)) => panic!(
                "Tried to union incompatible spans: {:?} and {:?}",
                self, other
            ),
            (Parsed(x), _) => Parsed(x.clone()),
            (_, Parsed(x)) => Parsed(x.clone()),
            _ => panic!(
                "Tried to union incompatible spans: {:?} and {:?}",
                self, other
            ),
        }
    }
}

/// Convert a byte idx into a string into a char idx for consumption by annotate_snippets.
/// The byte idx must be at a char boundary.
fn char_idx_from_byte_idx(input: &str, idx: usize) -> usize {
    use std::iter::once;
    input
        .char_indices()
        .map(|(byte_i, _)| byte_i) // We don't care about the char
        .chain(once(input.len())) // In case the idx points to the end of the string
        .enumerate()
        .find(|(_, byte_i)| *byte_i == idx)
        .map(|(char_i, _)| char_i)
        .unwrap()
}
