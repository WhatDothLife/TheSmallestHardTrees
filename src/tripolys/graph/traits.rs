//! Traits for graph data structures.

use std::hash::Hash;

pub trait Base {
    type Vertex: Hash + Clone + Eq;
}

pub trait Build: Base {
    fn add_vertex(&mut self, v: Self::Vertex);

    fn add_edge(&mut self, u: Self::Vertex, v: Self::Vertex);
}

pub trait Vertices: Base {
    type VertexIter<'a>: Iterator<Item = Self::Vertex>
    where
        Self: 'a;

    fn vertices(&self) -> Self::VertexIter<'_>;

    fn vertex_count(&self) -> usize;
}

pub trait HasVertex: Base {
    fn has_vertex(&self, v: Self::Vertex) -> bool;
}

pub trait Edges: Base {
    type EdgeIter<'a>: Iterator<Item = (Self::Vertex, Self::Vertex)>
    where
        Self: 'a;

    fn edges(&self) -> Self::EdgeIter<'_>;

    fn edge_count(&self) -> usize;
}

pub trait HasEdge: Base {
    fn has_edge(&self, u: Self::Vertex, v: Self::Vertex) -> bool;
}

pub trait Contract: Base {
    fn contract_vertex(&mut self, u: Self::Vertex, v: Self::Vertex) -> bool;

    fn contract_vertices<I>(&mut self, vertices: I)
    where
        I: IntoIterator<Item = Self::Vertex>,
    {
        let mut iter = vertices.into_iter();

        if let Some(u) = iter.next() {
            for v in iter {
                self.contract_vertex(u.clone(), v);
            }
        }
    }
}

pub trait Digraph: Vertices + Edges {}

impl<G> Digraph for G where G: Vertices + Edges {}

impl<G> Base for &G
where
    G: Base,
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

// fn has_vertex(&self, v: Self::Vertex) -> bool {
//     (*self).has_vertex(v)
// }
// }

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

//     fn has_edge(&self, u: Self::Vertex, v: Self::Vertex) -> bool {
//         (*self).has_edge(u, v)
//     }
// }
