use std::iter::FromIterator;
use std::ops::Add;

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

impl<SubExpr: Clone> InterpolatedText<SubExpr> {
    pub fn map<SubExpr2, F>(&self, mut f: F) -> InterpolatedText<SubExpr2>
    where
        F: FnMut(&SubExpr) -> SubExpr2,
    {
        InterpolatedText {
            head: self.head.clone(),
            tail: self.tail.iter().map(|(e, s)| (f(e), s.clone())).collect(),
        }
    }

    pub fn iter<'a>(
        &'a self,
    ) -> impl Iterator<Item = InterpolatedTextContents<SubExpr>> + 'a {
        use std::iter::once;
        once(InterpolatedTextContents::Text(self.head.clone())).chain(
            self.tail.iter().flat_map(|(e, s)| {
                once(InterpolatedTextContents::Expr(SubExpr::clone(e)))
                    .chain(once(InterpolatedTextContents::Text(s.clone())))
            }),
        )
    }
}

impl<'a, SubExpr: Clone + 'a> FromIterator<InterpolatedTextContents<SubExpr>>
    for InterpolatedText<SubExpr>
{
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = InterpolatedTextContents<SubExpr>>,
    {
        let mut res = InterpolatedText {
            head: "".to_owned(),
            tail: vec![],
        };
        let mut crnt_str = &mut res.head;
        for x in iter.into_iter() {
            match x {
                InterpolatedTextContents::Text(s) => crnt_str.push_str(&s),
                InterpolatedTextContents::Expr(e) => {
                    res.tail.push((e.clone(), "".to_owned()));
                    crnt_str = &mut res.tail.last_mut().unwrap().1;
                }
            }
        }
        res
    }
}

impl<SubExpr: Clone> Add for &InterpolatedText<SubExpr> {
    type Output = InterpolatedText<SubExpr>;
    fn add(self, rhs: &InterpolatedText<SubExpr>) -> Self::Output {
        self.iter().chain(rhs.iter()).collect()
    }
}
