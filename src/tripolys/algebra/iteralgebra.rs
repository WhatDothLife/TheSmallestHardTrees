use itertools::{Itertools, MultiProduct};
use std::hash::Hash;

use crate::graph::traits::{Digraph, Edges, VertexType};

impl<I> IterAlgebra for I where I: Iterator {}

pub trait IterAlgebra: Iterator {
    fn kproduct(self, k: usize) -> KProduct<Self>
    where
        Self: Sized + Clone,
        Self::Item: Clone,
    {
        KProduct {
            once: if k == 0 {
                Some(std::iter::once(vec![]))
            } else {
                None
            },
            iter: (0..k).map(|_| self.clone()).multi_cartesian_product(),
        }
    }

    fn kproduct_tuples<A, B>(self, k: usize) -> KProductTuples<A, B, Self>
    where
        Self: Iterator<Item = (A, B)> + Clone,
        A: Clone,
        B: Clone,
    {
        KProductTuples {
            iter: self.kproduct(k),
        }
    }
}

#[derive(Clone)]
pub struct KProduct<I>
where
    I: Iterator + Clone,
    I::Item: Clone,
{
    once: Option<std::iter::Once<Vec<I::Item>>>,
    iter: MultiProduct<I>,
}

impl<I> Iterator for KProduct<I>
where
    I: Iterator + Clone,
    I::Item: Clone,
{
    type Item = Vec<I::Item>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(ref mut once) = &mut self.once {
            once.next()
        } else {
            self.iter.next()
        }
    }
}

impl<A, I> VertexType for KProductTuples<A, A, I>
where
    I: Iterator<Item = (A, A)> + Clone,
    A: Clone + Eq + Hash,
{
    type Vertex = Vec<A>;
}

impl<A, I> Edges for KProductTuples<A, A, I>
where
    I: Iterator<Item = (A, A)> + Clone,
    A: Clone + Eq + Hash,
{
    type EdgeIter<'a>
     = Self where Self: 'a;

    fn edges(&self) -> Self::EdgeIter<'_> {
        self.clone()
    }

    fn edge_count(&self) -> usize {
        todo!()
    }
}

// impl<A, I> Digraph for KProductTuples<A, A, I>
// where
//     I: Iterator<Item = (A, A)> + Clone,
//     A: Clone,
// {
// }

#[derive(Clone)]
pub struct KProductTuples<A, B, I>
where
    I: Iterator<Item = (A, B)> + Clone,
    A: Clone,
    B: Clone,
{
    iter: KProduct<I>,
}

impl<A, B, I> Iterator for KProductTuples<A, B, I>
where
    I: Iterator<Item = (A, B)> + Clone,
    A: Clone,
    B: Clone,
{
    type Item = (Vec<A>, Vec<B>);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let perm = self.iter.next()?;
        Some(perm.into_iter().unzip())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_kproduct() {
        let elements = [0, 1, 2];
        let mut it = elements.iter().copied().kproduct(0);
        assert_eq!(it.next(), Some(vec![]));
        assert_eq!(it.next(), None);

        let mut it = elements.iter().copied().kproduct(1);
        assert_eq!(it.next(), Some(vec![0]));
        assert_eq!(it.next(), Some(vec![1]));
        assert_eq!(it.next(), Some(vec![2]));
        assert_eq!(it.next(), None);

        let mut it = elements.iter().copied().kproduct(2);
        assert_eq!(it.next(), Some(vec![0, 0]));
        assert_eq!(it.next(), Some(vec![0, 1]));
        assert_eq!(it.next(), Some(vec![0, 2]));
        assert_eq!(it.next(), Some(vec![1, 0]));
        assert_eq!(it.next(), Some(vec![1, 1]));
        assert_eq!(it.next(), Some(vec![1, 2]));
        assert_eq!(it.next(), Some(vec![2, 0]));
        assert_eq!(it.next(), Some(vec![2, 1]));
        assert_eq!(it.next(), Some(vec![2, 2]));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_kproduct_tuples() {
        let elements = [('a', 0), ('b', 1), ('c', 2)];
        let mut it = elements.iter().copied().kproduct_tuples(0);
        assert_eq!(it.next(), Some((vec![], vec![])));
        assert_eq!(it.next(), None);

        let mut it = elements.iter().copied().kproduct_tuples(1);
        assert_eq!(it.next(), Some((vec!['a'], vec![0])));
        assert_eq!(it.next(), Some((vec!['b'], vec![1])));
        assert_eq!(it.next(), Some((vec!['c'], vec![2])));
        assert_eq!(it.next(), None);

        let mut it = elements.iter().copied().kproduct_tuples(2);
        assert_eq!(it.next(), Some((vec!['a', 'a'], vec![0, 0])));
        assert_eq!(it.next(), Some((vec!['a', 'b'], vec![0, 1])));
        assert_eq!(it.next(), Some((vec!['a', 'c'], vec![0, 2])));
        assert_eq!(it.next(), Some((vec!['b', 'a'], vec![1, 0])));
        assert_eq!(it.next(), Some((vec!['b', 'b'], vec![1, 1])));
        assert_eq!(it.next(), Some((vec!['b', 'c'], vec![1, 2])));
        assert_eq!(it.next(), Some((vec!['c', 'a'], vec![2, 0])));
        assert_eq!(it.next(), Some((vec!['c', 'b'], vec![2, 1])));
        assert_eq!(it.next(), Some((vec!['c', 'c'], vec![2, 2])));
        assert_eq!(it.next(), None);
    }
}
