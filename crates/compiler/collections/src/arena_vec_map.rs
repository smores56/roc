use bumpalo::{
    collections::{FromIteratorIn, Vec},
    Bump,
};

// TODO: this is prefixed with Arena and should have that prefix
// removed once we remove the heap-allocated [VecMap].
//
/// A map built on [bumpalo::collections::Vec] that does not
/// hash its keys, useful for small collections.
#[derive(Debug, Clone)]
pub struct ArenaVecMap<'a, K, V> {
    keys: Vec<'a, K>,
    values: Vec<'a, V>,
}

impl<'a, K, V> ArenaVecMap<'a, K, V> {
    pub fn new_in(arena: &'a Bump) -> Self {
        Self {
            keys: Vec::new_in(arena),
            values: Vec::new_in(arena),
        }
    }

    pub fn reserve(&mut self, additional: usize) {
        self.keys.reserve(additional);
        self.values.reserve(additional);
    }

    pub fn is_empty(&self) -> bool {
        debug_assert_eq!(self.keys.len(), self.values.len());
        self.keys.is_empty()
    }

    pub fn len(&self) -> usize {
        debug_assert_eq!(self.keys.len(), self.values.len());
        self.keys.len()
    }

    pub fn swap_remove(&mut self, index: usize) -> (K, V) {
        let k = self.keys.swap_remove(index);
        let v = self.values.swap_remove(index);

        (k, v)
    }

    pub fn unzip(self) -> (Vec<'a, K>, Vec<'a, V>) {
        (self.keys, self.values)
    }

    pub fn unzip_slices(&self) -> (&[K], &[V]) {
        (&self.keys, &self.values)
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = (&K, &V)> {
        self.keys.iter().zip(self.values.iter())
    }

    pub fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = (&K, &mut V)> {
        self.keys.iter().zip(self.values.iter_mut())
    }

    pub fn keys(&self) -> impl ExactSizeIterator<Item = &K> {
        self.keys.iter()
    }

    pub fn values(&self) -> impl ExactSizeIterator<Item = &V> {
        self.values.iter()
    }

    pub fn truncate(&mut self, len: usize) {
        self.keys.truncate(len);
        self.values.truncate(len);
    }

    /// # Safety
    ///
    /// keys and values must have the same length, and there must not
    /// be any duplicates in the keys vector
    pub unsafe fn zip(keys: Vec<'a, K>, values: Vec<'a, V>) -> Self {
        Self { keys, values }
    }

    pub fn drain_filter<F>(&mut self, predicate: F) -> DrainFilter<'_, 'a, K, V, F>
    where
        F: Fn(&K, &V) -> bool,
    {
        DrainFilter {
            vec_map: self,
            predicate,
            cur_idx: 0,
        }
    }

    /// Removes all key/value pairs from the map, without affecting its allocated capacity.
    pub fn clear(&mut self) {
        self.keys.clear();
        self.values.clear();
    }
}

impl<'a, K: PartialEq, V> ArenaVecMap<'a, K, V> {
    pub fn with_capacity_in(capacity: usize, arena: &'a Bump) -> Self {
        Self {
            keys: Vec::with_capacity_in(capacity, arena),
            values: Vec::with_capacity_in(capacity, arena),
        }
    }

    pub fn insert(&mut self, key: K, mut value: V) -> Option<V> {
        match self.keys.iter().position(|x| x == &key) {
            Some(index) => {
                std::mem::swap(&mut value, &mut self.values[index]);

                Some(value)
            }
            None => {
                self.keys.push(key);
                self.values.push(value);

                None
            }
        }
    }

    pub fn contains_key(&self, key: &K) -> bool {
        self.keys.contains(key)
    }

    pub fn remove(&mut self, key: &K) -> Option<(K, V)> {
        let index = self.keys.iter().position(|x| x == key)?;
        Some(self.swap_remove(index))
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        match self.keys.iter().position(|x| x == key) {
            None => None,
            Some(index) => Some(&self.values[index]),
        }
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        match self.keys.iter().position(|x| x == key) {
            None => None,
            Some(index) => Some(&mut self.values[index]),
        }
    }

    pub fn get_or_insert(&mut self, key: K, default_value: impl FnOnce() -> V) -> &mut V {
        match self.keys.iter().position(|x| x == &key) {
            Some(index) => &mut self.values[index],
            None => {
                let value = default_value();

                self.keys.push(key);
                self.values.push(value);

                self.values.last_mut().unwrap()
            }
        }
    }
}

impl<'a, K: PartialEq, V> Extend<(K, V)> for ArenaVecMap<'a, K, V> {
    #[inline(always)]
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        let it = iter.into_iter();
        let hint = it.size_hint();

        match hint {
            (0, Some(0)) => {
                // done, do nothing
            }
            (1, Some(1)) | (2, Some(2)) => {
                for (k, v) in it {
                    self.insert(k, v);
                }
            }
            (_min, _opt_max) => {
                // TODO do this with sorting and dedup?
                for (k, v) in it {
                    self.insert(k, v);
                }
            }
        }
    }
}

impl<'a, K, V> IntoIterator for ArenaVecMap<'a, K, V> {
    type Item = (K, V);

    type IntoIter = IntoIter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            len: self.len(),
            keys: self.keys.into_iter(),
            values: self.values.into_iter(),
        }
    }
}

pub struct IntoIter<'a, K, V> {
    len: usize,
    keys: bumpalo::collections::vec::IntoIter<'a, K>,
    values: bumpalo::collections::vec::IntoIter<'a, V>,
}

impl<'a, K, V> Iterator for IntoIter<'a, K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        match (self.keys.next(), self.values.next()) {
            (Some(k), Some(v)) => Some((k, v)),
            _ => None,
        }
    }
}

impl<'a, K, V> ExactSizeIterator for IntoIter<'a, K, V> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<'a, K: PartialEq, V> FromIteratorIn<(K, V)> for ArenaVecMap<'a, K, V> {
    type Alloc = &'a Bump;

    fn from_iter_in<I>(iter: I, alloc: Self::Alloc) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
    {
        let mut this = Self::new_in(alloc);
        this.extend(iter);

        this
    }
}

pub struct DrainFilter<'d, 'a: 'd, K, V, F>
where
    F: Fn(&'d K, &'d V) -> bool,
{
    vec_map: &'d mut ArenaVecMap<'a, K, V>,
    predicate: F,
    cur_idx: usize,
}

impl<'d, 'a, K, V, F> Iterator for DrainFilter<'d, 'a, K, V, F>
where
    F: Fn(&K, &V) -> bool,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        while self.cur_idx < self.vec_map.len() {
            let drain = {
                let key = &self.vec_map.keys[self.cur_idx];
                let value = &self.vec_map.values[self.cur_idx];

                (self.predicate)(key, value)
            };

            if drain {
                let kv = self.vec_map.swap_remove(self.cur_idx);
                return Some(kv);
            } else {
                self.cur_idx += 1;
            }
        }
        None
    }
}

impl<'a, K, V> PartialEq for ArenaVecMap<'a, K, V>
where
    K: PartialEq,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        for (k, v) in self.iter() {
            match other.get(k) {
                Some(v1) => {
                    if v != v1 {
                        return false;
                    }
                }
                None => return false,
            }
        }

        true
    }
}

impl<'a, K, V> Eq for ArenaVecMap<'a, K, V>
where
    K: Eq,
    V: Eq,
{
}

#[cfg(test)]
mod test_drain_filter {
    use bumpalo::Bump;

    use crate::ArenaVecMap;

    #[test]
    fn test_nothing() {
        let arena = Bump::default();
        let mut map = ArenaVecMap::new_in(&arena);

        map.extend(vec![(1, 2), (2, 4)]);
        let mut iter = map.drain_filter(|k, _| *k == 0);
        assert!(iter.next().is_none());
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn test_drain() {
        let arena = Bump::default();
        let mut map = ArenaVecMap::new_in(&arena);

        map.extend(vec![(1, 2), (2, 4), (3, 6), (4, 8), (5, 10)]);

        let mut drained: Vec<_> = map.drain_filter(|k, _| k % 2 == 0).collect();
        drained.sort_unstable();
        assert_eq!(drained, vec![(2, 4), (4, 8)]);

        assert_eq!(map.len(), 3);
        let mut rest: Vec<_> = map.into_iter().collect();
        rest.sort_unstable();
        assert_eq!(rest, vec![(1, 2), (3, 6), (5, 10)]);
    }
}
