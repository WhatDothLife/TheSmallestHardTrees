use std::cmp;

use bitvec::bitvec;
use bitvec::vec::BitVec;

use super::traits::{VertexType, HasEdge};

/// AdjMatrix is a graph using a matrix representation.
///
/// It is used in the backtracking algorithm, because of frequent edge-lookup
/// which it implements in O(1).
#[derive(Clone, Debug)]
pub struct AdjMatrix {
    adjacencies: BitVec,
    num_vertices: usize,
}

impl AdjMatrix {
    pub fn new() -> AdjMatrix {
        AdjMatrix {
            adjacencies: BitVec::new(),
            num_vertices: 0,
        }
    }

    pub fn from_edges<I>(edges: I) -> Self
    where
        I: IntoIterator<Item = (usize, usize)>,
    {
        let edges = Vec::from_iter(edges);

        let mut num_vertices = 0;
        for &(u, v) in &edges {
            num_vertices = cmp::max(num_vertices, cmp::max(u, v) + 1);
        }

        let mut adjacencies = bitvec![0; num_vertices * num_vertices];

        for &(u, v) in &edges {
            adjacencies.set(u * num_vertices + v, true);
        }

        AdjMatrix {
            adjacencies,
            num_vertices,
        }
    }
}

impl VertexType for AdjMatrix {
    type Vertex = usize;
}

impl HasEdge for AdjMatrix {
    fn has_edge(&self, u: usize, v: usize) -> bool {
        if u >= self.num_vertices || v >= self.num_vertices {
            panic!("Vertices out of bounds");
        }

        *self.adjacencies.get(u * self.num_vertices + v).unwrap()
    }
}

impl FromIterator<(usize, usize)> for AdjMatrix {
    fn from_iter<T: IntoIterator<Item = (usize, usize)>>(iter: T) -> Self {
        Self::from_edges(iter)
    }
}

#[cfg(test)]
mod tests {
    use super::AdjMatrix;
    use crate::graph::traits::HasEdge;

    #[test]
    fn test_new_adj_matrix() {
        let adj_matrix = AdjMatrix::new();

        assert_eq!(adj_matrix.num_vertices, 0);
        assert_eq!(adj_matrix.adjacencies.len(), 0);
    }

    #[test]
    fn test_from_edges_adj_matrix() {
        let edges = vec![(0, 1), (1, 2), (2, 3)];
        let adj_matrix = AdjMatrix::from_edges(edges);

        assert_eq!(adj_matrix.num_vertices, 4);
        assert_eq!(adj_matrix.adjacencies.len(), 16);
        assert_eq!(adj_matrix.has_edge(0, 1), true);
        assert_eq!(adj_matrix.has_edge(1, 2), true);
        assert_eq!(adj_matrix.has_edge(2, 3), true);
        assert_eq!(adj_matrix.has_edge(3, 0), false);
    }

    #[test]
    #[should_panic]
    fn test_has_edge_out_of_bounds() {
        let edges = vec![(0, 1), (1, 2), (2, 3)];
        let adj_matrix = AdjMatrix::from_edges(edges);

        adj_matrix.has_edge(4, 5);
    }
}
