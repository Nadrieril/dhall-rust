use crate::*;
use std::iter::FromIterator;
use std::ops::Add;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterpolatedText<Note, Embed> {
    head: String,
    tail: Vec<(Rc<Expr<Note, Embed>>, String)>,
}

impl<N, E> From<(String, Vec<(Rc<Expr<N, E>>, String)>)>
    for InterpolatedText<N, E>
{
    fn from(x: (String, Vec<(Rc<Expr<N, E>>, String)>)) -> Self {
        InterpolatedText {
            head: x.0,
            tail: x.1,
        }
    }
}

impl<N, E> From<String> for InterpolatedText<N, E> {
    fn from(s: String) -> Self {
        InterpolatedText {
            head: s,
            tail: vec![],
        }
    }
}

#[derive(Debug, Clone)]
pub enum InterpolatedTextContents<'a, Note, Embed> {
    Text(&'a str),
    Expr(SubExpr<Note, Embed>),
}

impl<N, E> InterpolatedText<N, E> {
    pub fn map<N2, E2, F>(&self, mut f: F) -> InterpolatedText<N2, E2>
    where
        F: FnMut(&Rc<Expr<N, E>>) -> Rc<Expr<N2, E2>>,
    {
        InterpolatedText {
            head: self.head.clone(),
            tail: self.tail.iter().map(|(e, s)| (f(e), s.clone())).collect(),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = InterpolatedTextContents<N, E>> {
        use std::iter::once;
        once(InterpolatedTextContents::Text(self.head.as_ref())).chain(
            self.tail.iter().flat_map(|(e, s)| {
                once(InterpolatedTextContents::Expr(Rc::clone(e)))
                    .chain(once(InterpolatedTextContents::Text(s)))
            }),
        )
    }
}

impl<'a, N: 'a, E: 'a> FromIterator<InterpolatedTextContents<'a, N, E>>
    for InterpolatedText<N, E>
{
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = InterpolatedTextContents<'a, N, E>>,
    {
        let mut res = InterpolatedText {
            head: "".to_owned(),
            tail: vec![],
        };
        // let mut empty_string = "".to_owned();
        let mut crnt_str = &mut res.head;
        for x in iter.into_iter() {
            match x {
                InterpolatedTextContents::Text(s) => crnt_str.push_str(s),
                InterpolatedTextContents::Expr(e) => {
                    // crnt_str = &mut empty_string;
                    res.tail.push((e.clone(), "".to_owned()));
                    crnt_str = &mut res.tail.last_mut().unwrap().1;
                }
            }
        }
        res
    }
}

impl<N, E> Add for &InterpolatedText<N, E> {
    type Output = InterpolatedText<N, E>;
    fn add(self, rhs: &InterpolatedText<N, E>) -> Self::Output {
        self.iter().chain(rhs.iter()).collect()
    }
}
