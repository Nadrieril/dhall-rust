/// A sorted map that allows multiple values for each key.
pub use dup_tree_map::DupTreeMap;
pub use dup_tree_set::DupTreeSet;

mod one_or_more {
    use either::Either;
    use std::{iter, slice, vec};

    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum OneOrMore<T> {
        One(T),
        More(Vec<T>),
    }

    pub type Iter<'a, T> = Either<slice::Iter<'a, T>, iter::Once<&'a T>>;
    pub type IterMut<'a, T> =
        Either<slice::IterMut<'a, T>, iter::Once<&'a mut T>>;
    pub type IntoIter<T> = Either<vec::IntoIter<T>, iter::Once<T>>;

    impl<T> OneOrMore<T> {
        pub fn new(x: T) -> Self {
            OneOrMore::One(x)
        }

        pub fn push(&mut self, x: T) {
            take_mut::take(self, |sef| match sef {
                OneOrMore::More(mut vec) => {
                    vec.push(x);
                    OneOrMore::More(vec)
                }
                OneOrMore::One(one) => OneOrMore::More(vec![one, x]),
            })
        }

        pub fn iter(&self) -> Iter<'_, T> {
            match self {
                OneOrMore::More(vec) => Either::Left(vec.iter()),
                OneOrMore::One(x) => Either::Right(iter::once(x)),
            }
        }

        pub fn iter_mut(&mut self) -> IterMut<'_, T> {
            match self {
                OneOrMore::More(vec) => Either::Left(vec.iter_mut()),
                OneOrMore::One(x) => Either::Right(iter::once(x)),
            }
        }
    }

    impl<T> IntoIterator for OneOrMore<T> {
        type Item = T;
        type IntoIter = IntoIter<T>;

        fn into_iter(self) -> Self::IntoIter {
            match self {
                OneOrMore::More(vec) => Either::Left(vec.into_iter()),
                OneOrMore::One(x) => Either::Right(iter::once(x)),
            }
        }
    }
}

mod dup_tree_map {
    use super::one_or_more;
    use super::one_or_more::OneOrMore;
    use std::collections::{btree_map, BTreeMap};
    use std::iter;

    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct DupTreeMap<K, V> {
        map: BTreeMap<K, OneOrMore<V>>,
        size: usize,
    }

    pub type IterInternalIntermediate<'a, K, V> =
        iter::Zip<iter::Repeat<&'a K>, one_or_more::Iter<'a, V>>;
    pub type IterInternal<'a, K, V> = iter::FlatMap<
        btree_map::Iter<'a, K, OneOrMore<V>>,
        IterInternalIntermediate<'a, K, V>,
        for<'b> fn(
            (&'b K, &'b OneOrMore<V>),
        ) -> IterInternalIntermediate<'b, K, V>,
    >;
    pub struct Iter<'a, K, V> {
        iter: IterInternal<'a, K, V>,
        size: usize,
    }
    pub type IterMutInternalIntermediate<'a, K, V> =
        iter::Zip<iter::Repeat<&'a K>, one_or_more::IterMut<'a, V>>;
    pub type IterMutInternal<'a, K, V> = iter::FlatMap<
        btree_map::IterMut<'a, K, OneOrMore<V>>,
        IterMutInternalIntermediate<'a, K, V>,
        for<'b> fn(
            (&'b K, &'b mut OneOrMore<V>),
        ) -> IterMutInternalIntermediate<'b, K, V>,
    >;
    pub struct IterMut<'a, K, V> {
        iter: IterMutInternal<'a, K, V>,
        size: usize,
    }
    pub type IntoIterInternalIntermediate<K, V> =
        iter::Zip<iter::Repeat<K>, one_or_more::IntoIter<V>>;
    pub type IntoIterInternal<K, V> = iter::FlatMap<
        btree_map::IntoIter<K, OneOrMore<V>>,
        IntoIterInternalIntermediate<K, V>,
        fn((K, OneOrMore<V>)) -> IntoIterInternalIntermediate<K, V>,
    >;
    pub struct IntoIter<K: Clone, V> {
        iter: IntoIterInternal<K, V>,
        size: usize,
    }

    impl<K, V> DupTreeMap<K, V> {
        pub fn new() -> Self
        where
            K: Ord,
        {
            DupTreeMap {
                map: BTreeMap::new(),
                size: 0,
            }
        }

        pub fn insert(&mut self, key: K, value: V)
        where
            K: Ord,
        {
            use std::collections::btree_map::Entry;
            match self.map.entry(key) {
                Entry::Vacant(e) => {
                    e.insert(OneOrMore::new(value));
                }
                Entry::Occupied(mut e) => e.get_mut().push(value),
            }
            self.size += 1;
        }

        pub fn len(&self) -> usize {
            self.size
        }
        pub fn is_empty(&self) -> bool {
            self.size == 0
        }

        pub fn iter(&self) -> Iter<'_, K, V>
        where
            K: Ord,
        {
            fn foo<'a, K, V>(
                (k, oom): (&'a K, &'a OneOrMore<V>),
            ) -> IterInternalIntermediate<'a, K, V> {
                iter::repeat(k).zip(oom.iter())
            }
            Iter {
                iter: self.map.iter().flat_map(foo),
                size: self.size,
            }
        }

        pub fn iter_mut(&mut self) -> IterMut<'_, K, V>
        where
            K: Ord,
        {
            fn foo<'a, K, V>(
                (k, oom): (&'a K, &'a mut OneOrMore<V>),
            ) -> IterMutInternalIntermediate<'a, K, V> {
                iter::repeat(k).zip(oom.iter_mut())
            }
            IterMut {
                iter: self.map.iter_mut().flat_map(foo),
                size: self.size,
            }
        }
    }

    impl<K, V> Default for DupTreeMap<K, V>
    where
        K: Ord,
    {
        fn default() -> Self {
            Self::new()
        }
    }

    impl<K, V> IntoIterator for DupTreeMap<K, V>
    where
        K: Ord + Clone,
    {
        type Item = (K, V);
        type IntoIter = IntoIter<K, V>;

        fn into_iter(self) -> Self::IntoIter {
            fn foo<K, V>(
                (k, oom): (K, OneOrMore<V>),
            ) -> IntoIterInternalIntermediate<K, V>
            where
                K: Clone,
            {
                iter::repeat(k).zip(oom.into_iter())
            }
            IntoIter {
                iter: self.map.into_iter().flat_map(foo),
                size: self.size,
            }
        }
    }

    impl<'a, K, V> IntoIterator for &'a DupTreeMap<K, V>
    where
        K: Ord,
    {
        type Item = (&'a K, &'a V);
        type IntoIter = Iter<'a, K, V>;

        fn into_iter(self) -> Self::IntoIter {
            self.iter()
        }
    }

    impl<'a, K, V> IntoIterator for &'a mut DupTreeMap<K, V>
    where
        K: Ord,
    {
        type Item = (&'a K, &'a mut V);
        type IntoIter = IterMut<'a, K, V>;

        fn into_iter(self) -> Self::IntoIter {
            self.iter_mut()
        }
    }

    impl<K, V> iter::FromIterator<(K, V)> for DupTreeMap<K, V>
    where
        K: Ord,
    {
        fn from_iter<T>(iter: T) -> Self
        where
            T: IntoIterator<Item = (K, V)>,
        {
            let mut map = DupTreeMap::new();
            for (k, v) in iter {
                map.insert(k, v);
            }
            map
        }
    }

    impl<'a, K, V> Iterator for Iter<'a, K, V> {
        type Item = (&'a K, &'a V);

        fn next(&mut self) -> Option<Self::Item> {
            let next = self.iter.next();
            if next.is_some() {
                self.size -= 1;
            }
            next
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            (self.size, Some(self.size))
        }
    }

    impl<'a, K, V> Iterator for IterMut<'a, K, V> {
        type Item = (&'a K, &'a mut V);

        fn next(&mut self) -> Option<Self::Item> {
            let next = self.iter.next();
            if next.is_some() {
                self.size -= 1;
            }
            next
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            (self.size, Some(self.size))
        }
    }

    impl<K, V> Iterator for IntoIter<K, V>
    where
        K: Clone,
    {
        type Item = (K, V);

        fn next(&mut self) -> Option<Self::Item> {
            let next = self.iter.next();
            if next.is_some() {
                self.size -= 1;
            }
            next
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            (self.size, Some(self.size))
        }
    }

    // unsafe impl<K, V> iter::TrustedLen for IntoIter<K, V> {}
}

mod dup_tree_set {
    use super::DupTreeMap;
    use std::iter;

    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct DupTreeSet<K> {
        map: DupTreeMap<K, ()>,
    }

    pub type Iter<'a, K> = iter::Map<
        super::dup_tree_map::Iter<'a, K, ()>,
        for<'b> fn((&'b K, &'b ())) -> &'b K,
    >;
    pub type IntoIter<K> =
        iter::Map<super::dup_tree_map::IntoIter<K, ()>, fn((K, ())) -> K>;

    impl<K> DupTreeSet<K> {
        pub fn new() -> Self
        where
            K: Ord,
        {
            DupTreeSet {
                map: DupTreeMap::new(),
            }
        }

        pub fn len(&self) -> usize {
            self.map.len()
        }
        pub fn is_empty(&self) -> bool {
            self.map.is_empty()
        }

        pub fn iter(&self) -> Iter<'_, K>
        where
            K: Ord,
        {
            fn foo<'a, K>((k, ()): (&'a K, &'a ())) -> &'a K {
                k
            }
            self.map.iter().map(foo)
        }
    }

    impl<K> Default for DupTreeSet<K>
    where
        K: Ord,
    {
        fn default() -> Self {
            Self::new()
        }
    }

    impl<K> IntoIterator for DupTreeSet<K>
    where
        K: Ord + Clone,
    {
        type Item = K;
        type IntoIter = IntoIter<K>;

        fn into_iter(self) -> Self::IntoIter {
            fn foo<K>((k, ()): (K, ())) -> K {
                k
            }
            self.map.into_iter().map(foo)
        }
    }

    impl<'a, K> IntoIterator for &'a DupTreeSet<K>
    where
        K: Ord,
    {
        type Item = &'a K;
        type IntoIter = Iter<'a, K>;

        fn into_iter(self) -> Self::IntoIter {
            self.iter()
        }
    }

    impl<K> iter::FromIterator<K> for DupTreeSet<K>
    where
        K: Ord,
    {
        fn from_iter<T>(iter: T) -> Self
        where
            T: IntoIterator<Item = K>,
        {
            let map = iter.into_iter().map(|k| (k, ())).collect();
            DupTreeSet { map }
        }
    }
}
