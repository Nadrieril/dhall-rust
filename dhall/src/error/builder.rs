use annotate_snippets::{
    display_list::DisplayList,
    formatter::DisplayListFormatter,
    snippet::{Annotation, AnnotationType, Slice, Snippet, SourceAnnotation},
};

use crate::syntax::Span;

#[derive(Debug, Clone)]
pub struct ErrorBuilder {
    message: String,
    annotation_type: AnnotationType,
    annotations: Vec<BuilderAnnotation>,
}

#[derive(Debug, Clone)]
struct BuilderAnnotation {
    span: Span,
    message: String,
    annotation_type: AnnotationType,
}

/// A builder that uses the annotate_snippets library to display nice error messages about source
/// code locations.
impl ErrorBuilder {
    pub fn new(message: String) -> Self {
        ErrorBuilder {
            message,
            annotation_type: AnnotationType::Error,
            annotations: Vec::new(),
        }
    }
    pub fn span_err(span: &Span, message: String) -> Self {
        let mut builder = Self::new(message.clone());
        builder.annotate_err(span, message);
        builder
    }

    pub fn annotate_err(&mut self, span: &Span, message: String) {
        self.annotations.push(BuilderAnnotation {
            span: span.clone(),
            message,
            annotation_type: AnnotationType::Error,
        })
    }
    pub fn annotate_info(&mut self, span: &Span, message: String) {
        self.annotations.push(BuilderAnnotation {
            span: span.clone(),
            message,
            annotation_type: AnnotationType::Help,
        })
    }

    // TODO: handle multiple files
    pub fn format(self) -> String {
        let mut input = None;
        let annotations = self
            .annotations
            .into_iter()
            .filter_map(|annot| {
                let span = match annot.span {
                    Span::Parsed(span) => span,
                    _ => return None,
                };
                if input.is_none() {
                    input = Some(span.to_input());
                }
                Some(SourceAnnotation {
                    label: annot.message,
                    annotation_type: annot.annotation_type,
                    range: span.as_char_range(),
                })
            })
            .collect();

        let input = match input {
            Some(input) => input,
            None => return format!("[unknown location] {}", self.message),
        };

        let snippet = Snippet {
            title: Some(Annotation {
                label: Some(self.message),
                id: None,
                annotation_type: self.annotation_type,
            }),
            footer: vec![],
            slices: vec![Slice {
                source: input,
                line_start: 1, // TODO
                origin: Some("<current file>".to_string()),
                fold: true,
                annotations,
            }],
        };
        let dl = DisplayList::from(snippet);
        let dlf = DisplayListFormatter::new(true, false);
        format!("{}", dlf.format(&dl))
    }
}
