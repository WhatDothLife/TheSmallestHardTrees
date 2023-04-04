//! Traits for digraph.

use std::hash::Hash;

/// Defines the type of vertex of a graph.
pub trait VertexType {
    /// Type of vertex.
    type Vertex: Hash + Clone + Eq;
}

/// Access the vertices of a digraph.
pub trait Vertices: VertexType {
    /// Iterator over the vertices of the graph.
    type VertexIter<'a>: Iterator<Item = Self::Vertex>
    where
        Self: 'a;

    /// Returns an iterator over the vertices of the graph.
    fn vertices(&self) -> Self::VertexIter<'_>;

    /// Returns the number of vertices in the graph.
    fn vertex_count(&self) -> usize;
}

/// Access the edges of a digraph.
pub trait Edges: VertexType {
    /// Iterator over the edges of the graph.
    type EdgeIter<'a>: Iterator<Item = (Self::Vertex, Self::Vertex)>
    where
        Self: 'a;

    /// Returns an iterator over the edges of the graph.
    fn edges(&self) -> Self::EdgeIter<'_>;

    /// Returns the number of edges in the graph.
    fn edge_count(&self) -> usize;
}

/// Check if a graph has a specific edge.
pub trait HasEdge: VertexType {
    /// Returns true if the graph contains an edge from `u` to `v`.
    fn has_edge(&self, u: &Self::Vertex, v: &Self::Vertex) -> bool;
}

/// A directed graph.
pub trait Digraph: Vertices + Edges {}

impl<G> Digraph for G where G: Vertices + Edges {}

impl<G> VertexType for &G
where
    G: VertexType,
{
    type Vertex = G::Vertex;
}

impl<G> Vertices for &G
where
    G: Vertices,
{
    type VertexIter<'a> = G::VertexIter<'a> where Self: 'a;

    fn vertex_count(&self) -> usize {
        (*self).vertex_count()
    }

    fn vertices(&self) -> Self::VertexIter<'_> {
        (**self).vertices()
    }
}

impl<G> Edges for &G
where
    G: Edges,
{
    type EdgeIter<'a> = G::EdgeIter<'a> where Self: 'a;

    fn edges(&self) -> Self::EdgeIter<'_> {
        (**self).edges()
    }

    fn edge_count(&self) -> usize {
        (**self).edge_count()
    }
}

impl<G> HasEdge for &G
where
    G: HasEdge,
{
    fn has_edge(&self, u: &Self::Vertex, v: &Self::Vertex) -> bool {
        (*self).has_edge(u, v)
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

    fn from_edges<I>(edges: I) -> Self
    where
        I: IntoIterator<Item = (Self::Vertex, Self::Vertex)>,
    {
        let mut g = Self::default();
        for (u, v) in edges {
            g.add_edge(u, v);
        }
        g
    }
}
