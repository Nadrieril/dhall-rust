use annotate_snippets::{
    display_list::DisplayList,
    snippet::{Annotation, AnnotationType, Slice, Snippet, SourceAnnotation},
};

use crate::syntax::{ParsedSpan, Span};

#[derive(Debug, Clone, Default)]
pub struct ErrorBuilder {
    title: FreeAnnotation,
    annotations: Vec<SpannedAnnotation>,
    footer: Vec<FreeAnnotation>,
    /// Inducate that the current builder has already been consumed and consuming it again should
    /// panic.
    consumed: bool,
}

#[derive(Debug, Clone)]
struct SpannedAnnotation {
    span: ParsedSpan,
    message: String,
    annotation_type: AnnotationType,
}

#[derive(Debug, Clone)]
struct FreeAnnotation {
    message: String,
    annotation_type: AnnotationType,
}

impl SpannedAnnotation {
    fn to_annotation(&self) -> SourceAnnotation<'_> {
        SourceAnnotation {
            label: &self.message,
            annotation_type: self.annotation_type,
            range: self.span.as_char_range(),
        }
    }
}

impl FreeAnnotation {
    fn to_annotation(&self) -> Annotation<'_> {
        Annotation {
            label: Some(&self.message),
            id: None,
            annotation_type: self.annotation_type,
        }
    }
}

/// A builder that uses the annotate_snippets library to display nice error messages about source
/// code locations.
impl ErrorBuilder {
    pub fn new(message: impl ToString) -> Self {
        ErrorBuilder {
            title: FreeAnnotation {
                message: message.to_string(),
                annotation_type: AnnotationType::Error,
            },
            annotations: Vec::new(),
            footer: Vec::new(),
            consumed: false,
        }
    }

    pub fn span_annot(
        &mut self,
        span: Span,
        message: impl ToString,
        annotation_type: AnnotationType,
    ) -> &mut Self {
        // Ignore spans not coming from a source file
        let span = match span {
            Span::Parsed(span) => span,
            _ => return self,
        };
        self.annotations.push(SpannedAnnotation {
            span,
            message: message.to_string(),
            annotation_type,
        });
        self
    }
    pub fn footer_annot(
        &mut self,
        message: impl ToString,
        annotation_type: AnnotationType,
    ) -> &mut Self {
        self.footer.push(FreeAnnotation {
            message: message.to_string(),
            annotation_type,
        });
        self
    }

    pub fn span_err(
        &mut self,
        span: Span,
        message: impl ToString,
    ) -> &mut Self {
        self.span_annot(span, message, AnnotationType::Error)
    }
    pub fn span_help(
        &mut self,
        span: Span,
        message: impl ToString,
    ) -> &mut Self {
        self.span_annot(span, message, AnnotationType::Help)
    }
    pub fn help(&mut self, message: impl ToString) -> &mut Self {
        self.footer_annot(message, AnnotationType::Help)
    }
    pub fn note(&mut self, message: impl ToString) -> &mut Self {
        self.footer_annot(message, AnnotationType::Note)
    }

    // TODO: handle multiple files
    #[allow(clippy::drop_ref)]
    pub fn format(&mut self) -> String {
        if self.consumed {
            panic!("tried to format the same ErrorBuilder twice")
        }
        let this = std::mem::take(self);
        self.consumed = true;
        drop(self); // Get rid of the self reference so we don't use it by mistake.

        let input;
        let slices = if this.annotations.is_empty() {
            Vec::new()
        } else {
            input = this.annotations[0].span.to_input();
            let annotations = this
                .annotations
                .iter()
                .map(|annot| annot.to_annotation())
                .collect();
            vec![Slice {
                source: &input,
                line_start: 1, // TODO
                origin: Some("<current file>"),
                fold: true,
                annotations,
            }]
        };
        let footer = this
            .footer
            .iter()
            .map(|annot| annot.to_annotation())
            .collect();

        let snippet = Snippet {
            title: Some(this.title.to_annotation()),
            slices,
            footer,
            opt: Default::default(),
        };
        DisplayList::from(snippet).to_string()
    }
}

impl Default for FreeAnnotation {
    fn default() -> Self {
        FreeAnnotation {
            message: String::new(),
            annotation_type: AnnotationType::Error,
        }
    }
}
