use std::{cmp, ops::Range};

use bitvec::bitvec;
use bitvec::vec::BitVec;

use super::traits::{Edges, Vertices};

#[derive(Clone, Debug)]
pub struct AdjMatrix {
    adjacencies: BitVec,
    edges: Vec<(usize, usize)>,
    num_vertices: usize,
}

impl AdjMatrix {
    pub fn new() -> AdjMatrix {
        AdjMatrix {
            adjacencies: BitVec::new(),
            edges: Vec::new(),
            num_vertices: 0,
        }
    }

    pub fn from_edges<I>(edges: I) -> Self
    where
        I: IntoIterator<Item = (usize, usize)>,
    {
        let edges = Vec::from_iter(edges);

        let mut max = 0;
        for &(u, v) in &edges {
            max = cmp::max(max, cmp::max(u, v));
        }

        let mut adjacencies = bitvec![0; max * max];
        for &(u, v) in &edges {
            adjacencies.set(u * max + v, true);
        }

        AdjMatrix {
            adjacencies: BitVec::new(),
            edges,
            num_vertices: max,
        }
    }
}

impl Vertices for AdjMatrix {
    type VertexIter = Range<usize>;

    fn vertex_count(&self) -> usize {
        self.num_vertices
    }

    fn vertices(&self) -> Self::VertexIter {
        0..self.num_vertices
    }

    fn has_vertex(&self, v: usize) -> bool {
        v < self.num_vertices
    }
}

impl Edges for AdjMatrix {
    type EdgeIter = std::vec::IntoIter<(usize, usize)>;

    fn edges(&self) -> Self::EdgeIter {
        self.edges.clone().into_iter()
    }

    fn edge_count(&self) -> usize {
        self.edges.len()
    }

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
