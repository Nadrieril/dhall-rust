use std::rc::Rc;

// The type for labels throughout the AST
// It owns the data because otherwise lifetimes would make recursive imports impossible
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Label(Rc<str>);

impl From<String> for Label {
    fn from(s: String) -> Self {
        let s: &str = &s;
        Label(s.into())
    }
}

impl<'a> From<&'a str> for Label {
    fn from(s: &'a str) -> Self {
        Label(Rc::from(s))
    }
}

impl From<&Label> for String {
    fn from(x: &Label) -> String {
        x.0.as_ref().to_owned()
    }
}

impl std::borrow::Borrow<str> for Label {
    fn borrow(&self) -> &str {
        self.0.as_ref()
    }
}

impl Label {
    pub fn from_str(s: &str) -> Label {
        Label(s.into())
    }
    pub fn as_ref(&self) -> &str {
        self.0.as_ref()
    }
}
