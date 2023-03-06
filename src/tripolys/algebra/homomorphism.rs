use crate::{
    csp::Problem,
    graph::traits::{Build, Digraph, Edges, HasEdge},
};

/// A homomorphism from G to H is a mapping h: V(G) → V(H) such that
/// (h(u),h(v)) ∈ E(H) if (u,v) ∈ E(G).
///
/// This property cannot be checked by the compiler.
pub trait Homomorphism<VG, VH>: FnMut(&VG) -> VH {}

/// An endomorphism of a digraph H is a homomorphism from H to H.
pub trait Endomorphism<V>: Homomorphism<V, V> {}

/// A polymorphism of H is a homomorphism from H<sup>k</sup> to H where H
/// is a digraph and k ≥ 1.
pub trait Polymorphism<V>: Homomorphism<Vec<V>, V> {}

pub fn is_homomorphism<G, H, F>(mut f: F, g: &G, h: &H) -> bool
where
    G: Edges,
    H: HasEdge,
    F: FnMut(&G::Vertex) -> H::Vertex,
{
    for (u, v) in g.edges() {
        if !h.has_edge(f(&u), f(&v)) {
            return false;
        }
    }
    true
}

pub fn is_endomorphism<H, F>(f: F, h: &H) -> bool
where
    H: Edges + HasEdge,
    F: FnMut(&H::Vertex) -> H::Vertex,
{
    is_homomorphism(f, h, h)
}

use super::IterAlgebra;

// pub fn is_polymorphism<'a, H, F>(f: F, h: &H, k: usize) -> bool
// where
//     H: Edges + HasEdge + 'a,
//     H::EdgeIter<'a>: Clone,
//     F: FnMut(Vec<H::Vertex>) -> H::Vertex,
// {
//     is_homomorphism(f, &h.edges().kproduct(k), h)
// }

pub fn is_homomorphically_equivalent<G, H>(g: &G, h: &H) -> bool
where
    G: Digraph,
    H: Digraph,
{
    Problem::new(g, h).solution_exists() && Problem::new(h, g).solution_exists()
}
