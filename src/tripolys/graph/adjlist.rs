use std::{hash::Hash, iter::Cloned};

use indexmap::{map::Keys, IndexMap, IndexSet};

use super::traits::*;

#[derive(Clone, Debug)]
pub struct Neighbors<V> {
    outgoing: IndexSet<V>,
    incoming: IndexSet<V>,
}

impl<V> Default for Neighbors<V> {
    fn default() -> Self {
        Self {
            outgoing: Default::default(),
            incoming: Default::default(),
        }
    }
}

/// `AdjList<V>` is a graph using an adjacency list representation.
///
/// Each vertex is identified by a value of type V. The graph is stored as an
/// adjacency list, where each vertex is associated with two lists: one for
/// outgoing edges and one for incoming edges.
///
/// The vertices in the graph must implement the Hash, Clone, and Eq traits.  We
/// allow non-Copy types like `Vec` because it represents a tuple of any arity
/// which we need to build the indicator graph of a metaproblem. It also
/// implements fast contraction of vertices.
#[derive(Clone, Debug)]
pub struct AdjList<V> {
    lists: IndexMap<V, Neighbors<V>>,
}

impl<V> Default for AdjList<V> {
    fn default() -> Self {
        Self {
            lists: Default::default(),
        }
    }
}

impl<V: Hash + Clone + Eq> AdjList<V> {
    pub fn new() -> AdjList<V> {
        Self::default()
    }

    pub fn add_vertex(&mut self, v: V) {
        self.lists.entry(v).or_default();
    }

    pub fn add_edge(&mut self, u: &V, v: &V) {
        self.lists
            .entry(u.clone())
            .or_default()
            .outgoing
            .insert(v.clone());
        self.lists
            .entry(v.clone())
            .or_default()
            .incoming
            .insert(u.clone());
    }

    pub fn has_vertex(&self, v: &V) -> bool {
        self.lists.contains_key(v)
    }

    pub fn has_edge(&self, u: &V, v: &V) -> bool {
        if let Some(neighbors) = self.lists.get(u) {
            neighbors.outgoing.contains(v)
        } else {
            false
        }
    }

    pub fn contract_vertex(&mut self, u: &V, v: &V) -> bool {
        if u == v {
            return true;
        }
        if !self.lists.contains_key(u) || !self.lists.contains_key(v) {
            return false;
        }
        let neighbors = self.lists.remove(v).unwrap();

        for w in neighbors.outgoing {
            self.lists.get_mut(&w).unwrap().incoming.remove(v);
            if &w != u {
                self.add_edge(u, &w);
            }
        }
        for w in neighbors.incoming {
            self.lists.get_mut(&w).unwrap().outgoing.remove(v);
            if &w != u {
                self.add_edge(&w, u);
            }
        }
        true
    }

    pub fn from_edges<I: IntoIterator<Item = (V, V)>>(edges: I) -> AdjList<V> {
        let mut g = AdjList::new();
        for (u, v) in edges {
            g.add_vertex(u.clone());
            g.add_vertex(v.clone());
            g.add_edge(&u, &v);
        }
        g
    }
}

impl<V: Hash + Clone + Eq> VertexType for AdjList<V> {
    type Vertex = V;
}

impl<V: Hash + Clone + Eq> Vertices for AdjList<V> {
    type VertexIter<'a> = VertexIter<'a, V> where V: 'a;

    fn vertex_count(&self) -> usize {
        self.lists.len()
    }

    fn vertices(&self) -> Self::VertexIter<'_> {
        VertexIter(self.lists.keys().cloned())
    }
}

impl<V: Hash + Clone + Eq> Edges for AdjList<V> {
    type EdgeIter<'a> = EdgeIter<'a, V> where V: 'a;

    fn edges(&self) -> Self::EdgeIter<'_> {
        EdgeIter {
            adjacency_list: &self,
            current_vertex: 0,
            current_edge: 0,
        }
    }

    fn edge_count(&self) -> usize {
        self.lists
            .values()
            .map(|neighbors| neighbors.outgoing.len())
            .sum()
    }
}

impl<V: Hash + Clone + Eq> HasEdge for AdjList<V> {
    fn has_edge(&self, u: &Self::Vertex, v: &Self::Vertex) -> bool {
        if let Some(neighbors) = self.lists.get(u) {
            neighbors.outgoing.contains(v)
        } else {
            false
        }
    }
}

impl<V: Hash + Clone + Eq> FromIterator<(V, V)> for AdjList<V> {
    fn from_iter<T: IntoIterator<Item = (V, V)>>(iter: T) -> Self {
        Self::from_edges(iter)
    }
}

#[derive(Clone)]
pub struct VertexIter<'a, V>(Cloned<Keys<'a, V, Neighbors<V>>>);

impl<'a, V: Clone> Iterator for VertexIter<'a, V> {
    type Item = V;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

#[derive(Clone, Debug)]
pub struct EdgeIter<'a, V> {
    adjacency_list: &'a AdjList<V>,
    current_vertex: usize,
    current_edge: usize,
}

impl<'a, V: Clone> Iterator for EdgeIter<'a, V> {
    type Item = (V, V);

    fn next(&mut self) -> Option<Self::Item> {
        let lists = &self.adjacency_list.lists;

        while self.current_vertex < lists.len() {
            if self.current_edge < lists[self.current_vertex].outgoing.len() {
                let next = lists[self.current_vertex].outgoing[self.current_edge].clone();
                self.current_edge += 1;
                return Some((
                    (*lists.get_index(self.current_vertex).unwrap().0).clone(),
                    next,
                ));
            } else {
                self.current_vertex += 1;
                self.current_edge = 0;
            }
        }
        None
    }
}

impl<V: Eq + Hash + Copy> Build for AdjList<V> {
    type Vertex = V;

    fn with_capacities(nvertices: usize, _nedges: usize) -> Self {
        Self {
            lists: IndexMap::with_capacity(nvertices),
        }
    }

    fn add_vertex(&mut self, v: Self::Vertex) {
        self.add_vertex(v)
    }

    fn add_edge(&mut self, u: Self::Vertex, v: Self::Vertex) {
        self.add_edge(&u, &v)
    }
}

#[cfg(test)]
mod tests {
    use super::AdjList;
    use crate::graph::traits::*;

    #[test]
    fn test_adjlist() {
        let graph = AdjList::from_edges([(0, 1), (1, 2), (0, 2), (2, 3)]);

        assert_eq!(graph.vertex_count(), 4);
        assert_eq!(graph.edge_count(), 4);

        assert!(graph.has_vertex(&0));
        assert!(!graph.has_vertex(&4));

        assert!(graph.has_edge(&0, &1));
        assert!(!graph.has_edge(&1, &0));
    }

    #[test]
    fn test_contract_vertex() {
        let mut graph = AdjList::from_edges([(0, 1), (1, 2), (2, 3), (3, 4), (2, 4)]);

        assert_eq!(graph.vertex_count(), 5);
        assert_eq!(graph.edge_count(), 5);

        assert_eq!(graph.has_edge(&1, &4), false);

        assert_eq!(graph.contract_vertex(&1, &2), true);
        assert_eq!(graph.contract_vertex(&0, &5), false);
        assert_eq!(graph.contract_vertex(&0, &0), true);

        assert_eq!(graph.vertex_count(), 4);
        assert_eq!(graph.edge_count(), 4);

        assert_eq!(graph.has_edge(&1, &4), true);
        assert_eq!(graph.has_edge(&1, &2), false);
        assert_eq!(graph.has_edge(&2, &3), false);
    }
}
