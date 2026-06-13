//! Traits for digraph.

use std::hash::Hash;

/// A directed graph.
pub trait Digraph {
    type Vertex: Hash + Clone + Eq;

    type VertexIter<'a>: Iterator<Item = Self::Vertex>
    where
        Self: 'a;

    type EdgeIter<'a>: Iterator<Item = (Self::Vertex, Self::Vertex)>
    where
        Self: 'a;

    fn vertices(&self) -> Self::VertexIter<'_>;
    fn vertex_count(&self) -> usize;
    fn edges(&self) -> Self::EdgeIter<'_>;
    fn edge_count(&self) -> usize;
}

impl<G: Digraph> Digraph for &G {
    type Vertex = G::Vertex;
    type VertexIter<'a> = G::VertexIter<'a> where Self: 'a;
    type EdgeIter<'a> = G::EdgeIter<'a> where Self: 'a;

    fn vertices(&self) -> Self::VertexIter<'_> {
        (**self).vertices()
    }

    fn vertex_count(&self) -> usize {
        (*self).vertex_count()
    }

    fn edges(&self) -> Self::EdgeIter<'_> {
        (**self).edges()
    }

    fn edge_count(&self) -> usize {
        (*self).edge_count()
    }
}

/// A trait for building digraphs.
pub trait Build: Default {
    type Vertex: Copy + Eq;

    fn with_capacities(nvertices: usize, nedges: usize) -> Self;

    /// Adds a new vertex to the graph.
    fn add_vertex(&mut self, v: Self::Vertex);

    /// Adds a new edge to the graph, connecting vertices `u` and `v`.
    fn add_edge(&mut self, u: Self::Vertex, v: Self::Vertex);
}
