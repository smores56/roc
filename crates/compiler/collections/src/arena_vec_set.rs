use bumpalo::{
    collections::{FromIteratorIn, Vec},
    vec, Bump,
};

use std::borrow::Borrow;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArenaVecSet<'a, T> {
    elements: Vec<'a, T>,
}

impl<'a, T> ArenaVecSet<'a, T> {
    pub fn new_in(arena: &'a Bump) -> Self {
        Self {
            elements: Vec::new_in(arena),
        }
    }

    pub fn with_capacity_in(capacity: usize, arena: &'a Bump) -> Self {
        Self {
            elements: Vec::with_capacity_in(capacity, arena),
        }
    }

    pub fn into_vec(self) -> Vec<'a, T> {
        self.elements
    }

    pub fn reserve(&mut self, additional: usize) {
        self.elements.reserve(additional);
    }

    pub fn len(&self) -> usize {
        self.elements.len()
    }

    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    pub fn singleton_in(value: T, arena: &'a Bump) -> Self {
        Self {
            elements: vec![in arena; value],
        }
    }

    pub fn swap_remove(&mut self, index: usize) -> T {
        self.elements.swap_remove(index)
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.elements.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.elements.iter_mut()
    }

    /// Removes all elements from the set, without affecting its allocated capacity.
    pub fn clear(&mut self) {
        self.elements.clear()
    }

    /// Retains only the elements specified by the predicate.
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.elements.retain(f)
    }
}

impl<'a, T: PartialEq> ArenaVecSet<'a, T> {
    pub fn insert(&mut self, value: T) -> bool {
        if self.elements.contains(&value) {
            true
        } else {
            self.elements.push(value);

            false
        }
    }

    /// Returns true iff any of the given elements previoously existed in the set.
    pub fn insert_all<I: Iterator<Item = T>>(&mut self, values: I) -> bool {
        let mut any_existed = false;

        for value in values {
            any_existed = any_existed || self.insert(value);
        }

        any_existed
    }

    pub fn contains(&self, value: &T) -> bool {
        self.elements.contains(value)
    }

    /// Performs a swap_remove if the element was present in the set,
    /// then returns whether the value was present in the set.
    pub fn remove(&mut self, value: &T) -> bool {
        match self.elements.iter().position(|x| x == value) {
            None => false,
            Some(index) => {
                self.elements.swap_remove(index);

                true
            }
        }
    }
}

impl<'a, A: Ord> Extend<A> for ArenaVecSet<'a, A> {
    fn extend<T: IntoIterator<Item = A>>(&mut self, iter: T) {
        let it = iter.into_iter();
        let hint = it.size_hint();

        match hint {
            (0, Some(0)) => {
                // done, do nothing
            }
            (1, Some(1)) | (2, Some(2)) => {
                for value in it {
                    self.insert(value);
                }
            }
            _ => {
                self.elements.extend(it);

                self.elements.sort();
                self.elements.dedup();
            }
        }
    }
}

impl<'a, T: Ord> FromIteratorIn<T> for ArenaVecSet<'a, T> {
    type Alloc = &'a Bump;

    fn from_iter_in<I>(iter: I, alloc: Self::Alloc) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut this = Self::new_in(alloc);
        this.extend(iter);

        this
    }
}

impl<'a, T> IntoIterator for ArenaVecSet<'a, T> {
    type Item = T;

    type IntoIter = bumpalo::collections::vec::IntoIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.elements.into_iter()
    }
}

impl<'a, T> Borrow<[T]> for ArenaVecSet<'a, T> {
    fn borrow(&self) -> &[T] {
        &self.elements
    }
}

impl<'a, T> From<Vec<'a, T>> for ArenaVecSet<'a, T> {
    fn from(elements: Vec<'a, T>) -> Self {
        // Not totally safe, but good enough for our purposes - also, duplicates in the ArenaVecSet are
        // fine, just inefficient.
        Self { elements }
    }
}
