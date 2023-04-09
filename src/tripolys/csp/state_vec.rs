use std::ops::{Index, IndexMut};

/// A wrapper around a vector with an additional virtual length.
///
/// The virtual length is used to indicate the number of elements in
/// the vector that should be considered part of the domain. Elements
/// beyond the virtual length are ignored, which allows for efficient
/// removal of elements by swapping them with the last element and
/// decrementing the virtual length.
///
/// The `StateVec` struct is useful for backtracking algorithms, as it
/// provides the ability to remove elements, save and restore its state
/// efficiently.
#[derive(Clone, Debug)]
pub struct StateVec<T> {
    data: Vec<T>,
    vlen: usize,
    states: Vec<usize>,
    modified: bool,
}

impl<T> StateVec<T> {
    /// Creates a new, empty vector.
    pub fn new() -> StateVec<T> {
        StateVec {
            data: Vec::new(),
            vlen: 0,
            states: Vec::new(),
            modified: false,
        }
    }

    /// Returns the virtual length of the vector.
    pub fn vlen(&self) -> usize {
        self.vlen
    }

    /// Returns true if the vector is empty.
    pub fn is_empty(&self) -> bool {
        self.vlen == 0
    }

    /// Assigns a single value at index `index`to the vector by swapping it with
    /// index 0 and setting the virtual length to 1.
    pub fn set(&mut self, index: usize) {
        self.vlen = 1;
        self.data.swap(index, 0);
    }

    /// Resets the virtual length of the vector to its actual length.
    pub fn reset(&mut self) {
        self.vlen = self.data.len();
    }

    /// Removes a single value from the vector by swapping it with the last
    /// value, effectively decreasing the virtual length of the vector by 1.
    pub fn remove(&mut self, index: usize) {
        self.vlen -= 1;
        self.data.swap(index, self.vlen);
    }

    /// Returns true if the vector has been modified since the last save.
    pub fn is_modified(&self) -> bool {
        self.modified
    }

    /// Saves the current state of the vector.
    pub fn save_state(&mut self) {
        self.states.push(self.vlen);
        self.modified = true;
    }

    /// Restores the previous state of the vector.
    pub fn restore_state(&mut self) {
        self.vlen = self.states.pop().unwrap();
        self.modified = false;
    }

    /// Returns an iterator over the elements of the vector.
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            vec: self.data.iter(),
            count: self.vlen,
        }
    }
}

impl<T> FromIterator<T> for StateVec<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let vec = Vec::from_iter(iter);

        StateVec {
            vlen: vec.len(),
            data: vec,
            states: Vec::new(),
            modified: false,
        }
    }
}

pub struct Iter<'a, T> {
    vec: std::slice::Iter<'a, T>,
    count: usize,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.count == 0 {
            None
        } else {
            self.count -= 1;
            self.vec.next()
        }
    }
}

impl<'a, T> IntoIterator for &'a StateVec<T> {
    type Item = &'a T;

    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T> Index<usize> for StateVec<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.data.index(index)
    }
}

impl<T> IndexMut<usize> for StateVec<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.data.index_mut(index)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_domain_new() {
        let domain = StateVec::<i32>::new();
        assert_eq!(domain.vlen(), 0);
        assert!(domain.is_empty());
    }

    #[test]
    fn test_domain_assign_and_reset() {
        let mut domain = StateVec::from_iter(vec![1, 2, 3]);
        assert_eq!(domain.vlen(), 3);
        assert!(!domain.is_empty());

        domain.set(1);
        assert_eq!(domain.vlen(), 1);
        assert_eq!(domain[0], 2);

        domain.reset();
        assert_eq!(domain.vlen(), 3);
        assert_eq!(domain[0], 2);
    }

    #[test]
    fn test_domain_remove() {
        let mut domain = StateVec::from_iter(vec![1, 2, 3]);
        domain.remove(1);
        assert_eq!(domain.vlen(), 2);
        assert_eq!(domain[0], 1);
        assert_eq!(domain[1], 3);
    }

    #[test]
    fn test_domain_iter() {
        let domain = StateVec::from_iter(vec![1, 2, 3]);
        let mut iter = domain.iter();

        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), None);
    }
}
