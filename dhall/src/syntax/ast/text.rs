use std::iter::FromIterator;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

    pub fn traverse_ref<'a, SubExpr2, E, F>(
        &'a self,
        mut f: F,
    ) -> Result<InterpolatedTextContents<SubExpr2>, E>
    where
        F: FnMut(&'a SubExpr) -> Result<SubExpr2, E>,
    {
        use InterpolatedTextContents::{Expr, Text};
        Ok(match self {
            Expr(e) => Expr(f(e)?),
            Text(s) => Text(s.clone()),
        })
    }
    pub fn traverse_mut<'a, E, F>(&'a mut self, mut f: F) -> Result<(), E>
    where
        F: FnMut(&'a mut SubExpr) -> Result<(), E>,
    {
        use InterpolatedTextContents::Expr;
        if let Expr(e) = self {
            f(e)?;
        }
        Ok(())
    }
    pub fn map_ref<'a, SubExpr2, F>(
        &'a self,
        mut f: F,
    ) -> InterpolatedTextContents<SubExpr2>
    where
        F: FnMut(&'a SubExpr) -> SubExpr2,
    {
        use InterpolatedTextContents::{Expr, Text};
        match self {
            Expr(e) => Expr(f(e)),
            Text(s) => Text(s.clone()),
        }
    }
    pub fn map_mut<'a, F>(&'a mut self, mut f: F)
    where
        F: FnMut(&'a mut SubExpr),
    {
        use InterpolatedTextContents::Expr;
        if let Expr(e) = self {
            f(e);
        }
    }
}

impl<SubExpr> InterpolatedText<SubExpr> {
    pub fn len(&self) -> usize {
        1 + 2 * self.tail.len()
    }

    pub fn head(&self) -> &str {
        &self.head
    }

    pub fn tail(&self) -> &Vec<(SubExpr, String)> {
        &self.tail
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

    pub fn traverse_mut<'a, E, F>(&'a mut self, mut f: F) -> Result<(), E>
    where
        F: FnMut(&'a mut SubExpr) -> Result<(), E>,
    {
        for (e, _) in &mut self.tail {
            f(e)?
        }
        Ok(())
    }

    pub fn iter<'a>(
        &'a self,
    ) -> impl Iterator<Item = InterpolatedTextContents<&'a SubExpr>> + 'a {
        use std::iter::once;
        use InterpolatedTextContents::{Expr, Text};
        let exprs = self.tail.iter().map(|(e, _)| Expr(e));
        let texts = self.tail.iter().map(|(_, s)| Text(s.clone()));
        once(Text(self.head.clone())).chain(itertools::interleave(exprs, texts))
    }

    pub fn into_iter(
        self,
    ) -> impl Iterator<Item = InterpolatedTextContents<SubExpr>> {
        use std::iter::once;
        use InterpolatedTextContents::{Expr, Text};
        once(Text(self.head)).chain(
            self.tail
                .into_iter()
                .flat_map(|(e, s)| once(Expr(e)).chain(once(Text(s)))),
        )
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
