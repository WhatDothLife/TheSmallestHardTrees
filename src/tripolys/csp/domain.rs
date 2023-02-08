use std::ops::{Index, IndexMut};

#[derive(Clone, Debug)]
pub struct Domain<T> {
    domain: Vec<T>,
    size: usize,
    states: Vec<usize>,
    modified: bool,
}

impl<T> Domain<T> {
    pub fn new() -> Domain<T> {
        Domain {
            domain: Vec::new(),
            size: 0,
            states: Vec::new(),
            modified: false,
        }
    }

    pub fn size(&self) -> usize {
        self.size
    }

    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    pub fn assign(&mut self, index: usize) {
        self.size = 1;
        self.domain.swap(index, 0);
    }

    pub fn reset(&mut self) {
        self.size = self.domain.len();
    }

    pub fn remove(&mut self, index: usize) {
        self.size -= 1;
        self.domain.swap(index, self.size);
    }

    pub fn is_modified(&self) -> bool {
        self.modified
    }

    pub fn push_state(&mut self) {
        self.states.push(self.size);
        self.modified = true;
    }

    pub fn pop_state(&mut self) {
        self.size = self.states.pop().unwrap();
        self.modified = false;
    }

    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            domain: self.domain.iter(),
            count: self.size,
        }
    }
}

impl<T> FromIterator<T> for Domain<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let domain = Vec::from_iter(iter);

        Domain {
            size: domain.len(),
            domain,
            states: Vec::new(),
            modified: false,
        }
    }
}

pub struct Iter<'a, T> {
    domain: std::slice::Iter<'a, T>,
    count: usize,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.count == 0 {
            None
        } else {
            self.count -= 1;
            self.domain.next()
        }
    }
}

impl<'a, T> IntoIterator for &'a Domain<T> {
    type Item = &'a T;

    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T> Index<usize> for Domain<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.domain.index(index)
    }
}

impl<T> IndexMut<usize> for Domain<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.domain.index_mut(index)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_domain_new() {
        let domain = Domain::<i32>::new();
        assert_eq!(domain.size(), 0);
        assert!(domain.is_empty());
    }

    #[test]
    fn test_domain_assign_and_reset() {
        let mut domain = Domain::from_iter(vec![1, 2, 3]);
        assert_eq!(domain.size(), 3);
        assert!(!domain.is_empty());

        domain.assign(1);
        assert_eq!(domain.size(), 1);
        assert_eq!(domain[0], 2);

        domain.reset();
        assert_eq!(domain.size(), 3);
        assert_eq!(domain[0], 2);
    }

    #[test]
    fn test_domain_remove() {
        let mut domain = Domain::from_iter(vec![1, 2, 3]);
        domain.remove(1);
        assert_eq!(domain.size(), 2);
        assert_eq!(domain[0], 1);
        assert_eq!(domain[1], 3);
    }

    // #[test]
    // fn test_domain_push_and_pop_state() {
    //     let mut domain = Domain::from_iter(vec![1, 2, 3]);
    //     domain.push_state();
    //     domain.assign(2);
    //     assert_eq!(domain.size(), 1);

    //     domain.pop_state();
    //     assert_eq!(domain.size(), 3);
    //     assert_eq!(domain[0], 3);
    // }

    #[test]
    fn test_domain_iter() {
        let domain = Domain::from_iter(vec![1, 2, 3]);
        let mut iter = domain.iter();

        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_domain_index() {
        let domain = Domain::from_iter(vec![1, 2, 3]);
        assert_eq!(domain[0], 1);
        assert_eq!(domain[1], 2);
        assert_eq!(domain[2], 3);
    }

    #[test]
    fn test_domain_index_mut() {
        let mut domain = Domain::from_iter(vec![1, 2, 3]);
        domain[0] = 4;
        assert_eq!(domain[0], 4);
    }
}
