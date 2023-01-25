pub type Vertex = usize;
pub type Edge = (Vertex, Vertex);

pub trait Vertices {
    type VertexIter: Iterator<Item = Vertex>;

    fn vertex_count(&self) -> usize;

    fn vertices(&self) -> Self::VertexIter;

    fn has_vertex(&self, v: Vertex) -> bool;
}

pub trait Edges {
    type EdgeIter: Iterator<Item = Edge>;

    fn edges(&self) -> Self::EdgeIter;

    fn edge_count(&self) -> usize;

    fn has_edge(&self, u: usize, v: usize) -> bool;
}

pub trait Digraph: Vertices + Edges {}

impl<G> Digraph for G where G: Vertices + Edges {}

impl<G: Edges> Edges for &G {
    type EdgeIter = G::EdgeIter;

    fn edges(&self) -> Self::EdgeIter {
        (*self).edges()
    }

    fn edge_count(&self) -> usize {
        (*self).edge_count()
    }

    fn has_edge(&self, u: usize, v: usize) -> bool {
        (*self).has_edge(u, v)
    }
}

impl<G: Vertices> Vertices for &G {
    type VertexIter = G::VertexIter;

    fn vertex_count(&self) -> usize {
        (*self).vertex_count()
    }

    fn vertices(&self) -> Self::VertexIter {
        (*self).vertices()
    }

    fn has_vertex(&self, v: Vertex) -> bool {
        (*self).has_vertex(v)
    }
}

impl Edges for Vec<(usize, usize)> {
    type EdgeIter = std::vec::IntoIter<(usize, usize)>;

    fn edges(&self) -> Self::EdgeIter {
        self.clone().into_iter()
    }

    fn edge_count(&self) -> usize {
        self.len()
    }

    fn has_edge(&self, u: usize, v: usize) -> bool {
        self.contains(&(u, v))
    }
}

pub trait IntoEdges {
    type EdgeIter: Iterator<Item = (usize, usize)>;

    fn into_edges(self) -> Self::EdgeIter;
}

impl IntoEdges for Vec<(usize, usize)> {
    type EdgeIter = std::vec::IntoIter<(usize, usize)>;

    fn into_edges(self) -> Self::EdgeIter {
        self.into_iter()
    }
}
