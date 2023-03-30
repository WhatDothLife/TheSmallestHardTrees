use std::collections::HashMap;

use crate::csp::Problem;
use crate::graph::AdjList;
use crate::graph::classes::directed_path;
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
/// # use tripolys::graph::AdjList;
/// # use tripolys::algebra::is_homomorphism;
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
/// # use tripolys::graph::AdjList;
/// # use tripolys::algebra::is_endomorphism;
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

/// Returns `true` if the input graph `g` is balanced, `false` otherwise.
///
/// A digraph is considered balanced if its vertices can be organized into levels
/// such that there exists a function lvl : H → N such that lvl(v) = lvl(u) + 1
/// for all (u, v) ∈ E(H) and the smallest level is 0. The height of a balanced
/// digraph is defined as the maximum level.
///
/// # Examples
///
/// ```
/// use tripolys::graph::AdjList;
/// use tripolys::algebra::is_balanced;
///
/// let mut g = AdjList::from_edges([(0, 1), (1, 2), (2, 3), (1, 4)]);
/// assert!(is_balanced(&g));
/// g.add_edge(0, 2);
/// assert!(!is_balanced(&g));
/// ```
pub fn is_balanced<G>(g: &G) -> bool
where
    G: Digraph,
{
    let h: AdjList<_> = directed_path(g.vertex_count());
    Problem::new(g, h).solution_exists()
}

/// Computes the levels of a digraph `g`.
///
/// Returns a `HashMap` where the keys are the vertices of `g` and the values
/// are their levels, or `None` if `g` is not balanced.
///
/// # Examples
///
/// ```
/// use tripolys::graph::AdjList;
/// use tripolys::algebra::levels;
///
/// let mut g = AdjList::from_edges([("a", "b"), ("b", "c"), ("c", "d"), ("b", "e")]);
/// assert_eq!(levels(&g), Some([("a", 0), ("b", 1), ("c", 2), ("d", 3), ("e", 2)].into_iter().collect()));
/// ```
pub fn levels<G>(g: &G) -> Option<HashMap<G::Vertex, usize>>
where
    G: Digraph,
{
    for k in 0..g.vertex_count() {
        let h: AdjList<_> = directed_path(k + 1);
        let res = Problem::new(g, h).solve();

        if res.is_some() {
            return res;
        }
    }
    None
}
