use crate::csp::Problem;
use crate::graph::traits::{Digraph, Edges, HasEdge};

use super::iteralgebra::IterAlgebra;

/// Determines whether a given mapping function `f` is a homomorphism from graph
/// `g` to graph `h`.
///
/// A homomorphism is a function between two graphs that preserves edges,
/// meaning that if there is an edge between two vertices in `g`, there must be
/// an edge between their corresponding vertices in `h`. The mapping function
/// `f` maps the vertices of `g` to the vertices of `h`.
///
/// # Examples
///
/// ```
/// # use crate::graph::AdjList;
/// # use crate::algebra::is_homomorphism;
/// let g = AdjList::from_edges([(0, 1), (0, 2), (1, 3), (2, 3)]);
/// let h = AdjList::from_edges([(0, 1), (1, 2)]);
///
/// // Define a function that maps vertices of `g` to vertices of `h`
/// let f = |v| match v {
///     0 => 0,
///     1 => 1,
///     2 => 1,
///     3 => 2,
///     _ => unreachable!(),
/// };
///
/// assert!(is_homomorphism(f, &g, &h));
/// ```
pub fn is_homomorphism<G, H, F>(mut f: F, g: &G, h: &H) -> bool
where
    G: Edges,
    H: HasEdge,
    F: FnMut(G::Vertex) -> H::Vertex,
{
    for (u, v) in g.edges() {
        if !h.has_edge(f(u), f(v)) {
            return false;
        }
    }
    true
}

/// Determines whether a given mapping function `f` is an endomorphism of graph `h`.
///
/// An endomorphism is a homomorphism from a graph to itself. In other words,
/// the mapping function `f` maps the vertices of `h` to the vertices of `h`
/// while preserving edges.
///
/// # Examples
///
/// ```
/// # use crate::graph::AdjList;
/// # use crate::algebra::is_endomorphism;
/// let h = AdjList::from_edges([(0, 1), (0, 2), (1, 3), (2, 3)]);
///
/// // Define a function that maps vertices of `h` to themselves
/// let f = |v| v;
///
/// assert!(is_endomorphism(f, &h));
/// ```
pub fn is_endomorphism<H, F>(f: F, h: &H) -> bool
where
    H: Edges + HasEdge,
    F: FnMut(H::Vertex) -> H::Vertex,
{
    is_homomorphism(f, h, h)
}

pub fn is_homomorphic<G, H>(g: &G, h: &H) -> bool
where
    G: Digraph,
    H: Digraph,
{
    Problem::new(g, h).solution_exists()
}

pub fn is_homomorphically_equivalent<G, H>(g: &G, h: &H) -> bool
where
    G: Digraph,
    H: Digraph,
{
    is_homomorphic(g, h) && is_homomorphic(h, g)
}

// pub fn is_polymorphism<H, F>(f: F, h: &H, k: usize) -> bool
// where
//     H: Edges + HasEdge,
//     // H::EdgeIter: Clone,
//     F: FnMut(Vec<H::Vertex>) -> H::Vertex,
//     H::EdgeIter<'_>: Clone,
// {
//     is_homomorphism(f, h.edges().kproduct_tuples(k), h)
// }
