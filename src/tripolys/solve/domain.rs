use std::ops::{Index, IndexMut};

#[derive(Clone, Debug)]
pub struct Domain<T> {
    domain: Vec<T>,
    size: usize,
    states: Vec<usize>,
}

impl<T> Domain<T> {
    pub fn new() -> Domain<T> {
        Domain {
            domain: Vec::new(),
            size: 0,
            states: Vec::new(),
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

    pub fn push_state(&mut self) {
        self.states.push(self.size)
    }

    pub fn pop_state(&mut self) {
        self.size = self.states.pop().unwrap();
    }

    pub fn iter<'a>(&'a self) -> Iter<'a, T> {
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
    fn test_name() {
    }
}
