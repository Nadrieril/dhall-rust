use annotate_snippets::{
    display_list::DisplayList,
    formatter::DisplayListFormatter,
    snippet::{Annotation, AnnotationType, Slice, Snippet, SourceAnnotation},
};

use crate::syntax::{ParsedSpan, Span};

#[derive(Debug, Clone, Default)]
pub(crate) struct ErrorBuilder {
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
    fn into_annotation(self) -> SourceAnnotation {
        SourceAnnotation {
            label: self.message,
            annotation_type: self.annotation_type,
            range: self.span.as_char_range(),
        }
    }
}

impl FreeAnnotation {
    fn into_annotation(self) -> Annotation {
        Annotation {
            label: Some(self.message),
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
    pub fn format(&mut self) -> String {
        if self.consumed {
            panic!("tried to format the same ErrorBuilder twice")
        }
        let this = std::mem::replace(self, ErrorBuilder::default());
        self.consumed = true;
        drop(self); // Get rid of the self reference so we don't use it by mistake.

        let slices = if this.annotations.is_empty() {
            Vec::new()
        } else {
            let input = this.annotations[0].span.to_input();
            let annotations = this
                .annotations
                .into_iter()
                .map(|annot| annot.into_annotation())
                .collect();
            vec![Slice {
                source: input,
                line_start: 1, // TODO
                origin: Some("<current file>".to_string()),
                fold: true,
                annotations,
            }]
        };
        let footer = this
            .footer
            .into_iter()
            .map(|annot| annot.into_annotation())
            .collect();

        let snippet = Snippet {
            title: Some(this.title.into_annotation()),
            slices,
            footer,
        };
        let dl = DisplayList::from(snippet);
        let dlf = DisplayListFormatter::new(true, false);
        format!("{}", dlf.format(&dl))
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
