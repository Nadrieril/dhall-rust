use std::iter::FromIterator;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterpolatedText<SubExpr> {
    head: String,
    tail: Vec<(SubExpr, String)>,
}

impl<SubExpr> From<(String, Vec<(SubExpr, String)>)>
    for InterpolatedText<SubExpr>
{
    fn from(x: (String, Vec<(SubExpr, String)>)) -> Self {
        InterpolatedText {
            head: x.0,
            tail: x.1,
        }
    }
}

impl<SubExpr> From<String> for InterpolatedText<SubExpr> {
    fn from(s: String) -> Self {
        InterpolatedText {
            head: s,
            tail: vec![],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InterpolatedTextContents<SubExpr> {
    Text(String),
    Expr(SubExpr),
}

impl<SubExpr> InterpolatedTextContents<SubExpr> {
    pub fn is_empty(&self) -> bool {
        use InterpolatedTextContents::{Expr, Text};
        match self {
            Expr(_) => false,
            Text(s) => s.is_empty(),
        }
    }
}

impl<SubExpr> InterpolatedText<SubExpr> {
    pub fn head(&self) -> &str {
        &self.head
    }

    pub fn head_mut(&mut self) -> &mut String {
        &mut self.head
    }

    pub fn is_empty(&self) -> bool {
        self.head.is_empty() && self.tail.is_empty()
    }

    pub fn traverse_ref<'a, SubExpr2, E, F>(
        &'a self,
        mut f: F,
    ) -> Result<InterpolatedText<SubExpr2>, E>
    where
        F: FnMut(&'a SubExpr) -> Result<SubExpr2, E>,
    {
        Ok(InterpolatedText {
            head: self.head.clone(),
            tail: self
                .tail
                .iter()
                .map(|(e, s)| Ok((f(e)?, s.clone())))
                .collect::<Result<_, _>>()?,
        })
    }

    pub fn iter<'a>(
        &'a self,
    ) -> impl Iterator<Item = InterpolatedTextContents<SubExpr>> + 'a
    where
        SubExpr: Clone,
    {
        use std::iter::once;
        use InterpolatedTextContents::{Expr, Text};
        once(Text(self.head.clone()))
            .chain(self.tail.iter().flat_map(|(e, s)| {
                once(Expr(SubExpr::clone(e))).chain(once(Text(s.clone())))
            }))
            .filter(|c| !c.is_empty())
    }

    pub fn into_iter(
        self,
    ) -> impl Iterator<Item = InterpolatedTextContents<SubExpr>> {
        use std::iter::once;
        use InterpolatedTextContents::{Expr, Text};
        once(Text(self.head))
            .chain(
                self.tail
                    .into_iter()
                    .flat_map(|(e, s)| once(Expr(e)).chain(once(Text(s)))),
            )
            .filter(|c| !c.is_empty())
    }
}

impl<SubExpr> FromIterator<InterpolatedTextContents<SubExpr>>
    for InterpolatedText<SubExpr>
{
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = InterpolatedTextContents<SubExpr>>,
    {
        let mut res = InterpolatedText {
            head: String::new(),
            tail: Vec::new(),
        };
        let mut crnt_str = &mut res.head;
        for x in iter.into_iter() {
            match x {
                InterpolatedTextContents::Text(s) => crnt_str.push_str(&s),
                InterpolatedTextContents::Expr(e) => {
                    res.tail.push((e, String::new()));
                    crnt_str = &mut res.tail.last_mut().unwrap().1;
                }
            }
        }
        res
    }
}
