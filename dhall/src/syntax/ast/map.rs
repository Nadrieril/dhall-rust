/// A sorted map that allows multiple values for each key.
pub use dup_tree_map::DupTreeMap;
pub use dup_tree_set::DupTreeSet;

mod known_size_iter {
    pub struct KnownSizeIterator<I> {
        pub iter: I,
        pub size: usize,
    }

    impl<I: Iterator> Iterator for KnownSizeIterator<I> {
        type Item = I::Item;

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

    // unsafe impl<I: Iterator> iter::TrustedLen for KnownSizeIterator<I> {}
}

mod tuple {
    mod sealed {
        pub trait Sealed {}
    }
    pub trait Tuple: sealed::Sealed {
        type First;
        type Second;
    }
    impl<A, B> sealed::Sealed for (A, B) {}
    impl<A, B> Tuple for (A, B) {
        type First = A;
        type Second = B;
    }
}

mod dup_tree_map {
    use super::known_size_iter::KnownSizeIterator;
    use super::tuple::Tuple;
    use smallvec::SmallVec;
    use std::collections::BTreeMap;
    use std::iter;

    type OneOrMore<V> = SmallVec<[V; 1]>;
    type DupTreeMapInternal<K, V> = BTreeMap<K, OneOrMore<V>>;

    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct DupTreeMap<K, V> {
        map: DupTreeMapInternal<K, V>,
        size: usize,
    }

    // Generic types and functions to construct the iterators for this struct.
    type ZipRepeatIter<T> = iter::Zip<
        iter::Repeat<<T as Tuple>::First>,
        <<T as Tuple>::Second as IntoIterator>::IntoIter,
    >;
    type DupTreeMapIter<M> = KnownSizeIterator<
        iter::FlatMap<
            <M as IntoIterator>::IntoIter,
            ZipRepeatIter<<M as IntoIterator>::Item>,
            fn(
                <M as IntoIterator>::Item,
            ) -> ZipRepeatIter<<M as IntoIterator>::Item>,
        >,
    >;

    fn zip_repeat<K, I>((k, iter): (K, I)) -> ZipRepeatIter<(K, I)>
    where
        K: Clone,
        I: IntoIterator,
    {
        iter::repeat(k).zip(iter.into_iter())
    }

    fn make_map_iter<M, K, I>(map: M, size: usize) -> DupTreeMapIter<M>
    where
        M: IntoIterator<Item = (K, I)>,
        K: Clone,
        I: IntoIterator,
    {
        KnownSizeIterator {
            iter: map.into_iter().flat_map(zip_repeat),
            size,
        }
    }

    pub type IterMut<'a, K, V> =
        DupTreeMapIter<&'a mut DupTreeMapInternal<K, V>>;
    pub type Iter<'a, K, V> = DupTreeMapIter<&'a DupTreeMapInternal<K, V>>;
    pub type IntoIter<K, V> = DupTreeMapIter<DupTreeMapInternal<K, V>>;

    impl<K: Ord, V> DupTreeMap<K, V> {
        pub fn new() -> Self {
            DupTreeMap {
                map: BTreeMap::new(),
                size: 0,
            }
        }

        pub fn insert(&mut self, key: K, value: V) {
            self.map.entry(key).or_default().push(value);
            self.size += 1;
        }

        pub fn len(&self) -> usize {
            self.size
        }
        pub fn is_empty(&self) -> bool {
            self.size == 0
        }

        pub fn iter(&self) -> Iter<'_, K, V> {
            make_map_iter(&self.map, self.size)
        }

        pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
            make_map_iter(&mut self.map, self.size)
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
            make_map_iter(self.map, self.size)
        }
    }

    impl<'a, K, V> IntoIterator for &'a DupTreeMap<K, V>
    where
        K: Ord + 'a,
        V: 'a,
    {
        type Item = (&'a K, &'a V);
        type IntoIter = Iter<'a, K, V>;

        fn into_iter(self) -> Self::IntoIter {
            self.iter()
        }
    }

    impl<'a, K, V> IntoIterator for &'a mut DupTreeMap<K, V>
    where
        K: Ord + 'a,
        V: 'a,
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
}

mod dup_tree_set {
    use super::tuple::Tuple;
    use super::DupTreeMap;
    use std::iter;

    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct DupTreeSet<K> {
        map: DupTreeMap<K, ()>,
    }

    type DupTreeSetIter<M> = iter::Map<
        <M as IntoIterator>::IntoIter,
        fn(
            <M as IntoIterator>::Item,
        ) -> <<M as IntoIterator>::Item as Tuple>::First,
    >;

    pub type Iter<'a, K> = DupTreeSetIter<&'a DupTreeMap<K, ()>>;
    pub type IntoIter<K> = DupTreeSetIter<DupTreeMap<K, ()>>;

    fn drop_second<A, B>((a, _): (A, B)) -> A {
        a
    }

    impl<K: Ord> DupTreeSet<K> {
        pub fn new() -> Self {
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

        pub fn iter(&self) -> Iter<'_, K> {
            self.map.iter().map(drop_second)
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
            self.map.into_iter().map(drop_second)
        }
    }

    impl<'a, K> IntoIterator for &'a DupTreeSet<K>
    where
        K: Ord + 'a,
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
