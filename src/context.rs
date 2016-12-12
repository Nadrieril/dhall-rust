use std::collections::HashMap;

/// A `(Context a)` associates `Text` labels with values of type `a`
///
/// The `Context` is used for type-checking when `(a = Expr X)`
///
/// * You create a `Context` using `empty` and `insert`
/// * You transform a `Context` using `fmap`
/// * You consume a `Context` using `lookup` and `toList`
///
/// The difference between a `Context` and a `Map` is that a `Context` lets you
/// have multiple ordered occurrences of the same key and you can query for the
/// `n`th occurrence of a given key.
///
#[derive(Debug, Clone)]
pub struct Context<'i, T>(HashMap<&'i str, Vec<T>>);

impl<'i, T> Context<'i, T> {
    /// An empty context with no key-value pairs
    pub fn new() -> Self {
        Context(HashMap::new())
    }

    /// Look up a key by name and index
    ///
    /// ```c
    /// lookup _ _         empty  = Nothing
    /// lookup k 0 (insert k v c) = Just v
    /// lookup k n (insert k v c) = lookup k (n - 1) c  -- 1 <= n
    /// lookup k n (insert j v c) = lookup k  n      c  -- k /= j
    /// ```
    pub fn lookup<'a>(&'a self, k: &str, n: usize) -> Option<&'a T> {
        self.0.get(k).and_then(|v| v.get(v.len() - 1 - n))
    }

    pub fn map<U, F: Fn(&T) -> U>(&self, f: F) -> Context<'i, U> {
        Context(self.0.iter().map(|(k, v)| (k.clone(), v.iter().map(&f).collect())).collect())
    }
}

impl<'i, T: Clone> Context<'i, T> {
    /// Add a key-value pair to the `Context`
    pub fn insert(&self, k: &'i str, v: T) -> Self {
        let mut ctx = (*self).clone();
        {
            let m = ctx.0.entry(k).or_insert(vec![]);
            m.push(v);
        }
        ctx
    }
}
