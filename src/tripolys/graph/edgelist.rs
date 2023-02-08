use std::hash::Hash;

use super::traits::*;

pub struct EdgeList<V> {
    edges: Vec<(V, V)>,
}

impl<V: Clone + Hash + Eq> Base for EdgeList<V> {
    type Vertex = V;
}

impl<V: Clone + Hash + Eq> Edges for EdgeList<V> {
    type EdgeIter<'a> = std::iter::Cloned<std::slice::Iter<'a, (V, V)>> where V: 'a;

    fn edges(&self) -> Self::EdgeIter<'_> {
        self.edges.iter().cloned()
    }

    fn edge_count(&self) -> usize {
        self.edges.len()
    }
}

impl<V> FromIterator<(V, V)> for EdgeList<V> {
    fn from_iter<T: IntoIterator<Item = (V, V)>>(iter: T) -> Self {
        EdgeList {
            edges: Vec::from_iter(iter),
        }
    }
}
