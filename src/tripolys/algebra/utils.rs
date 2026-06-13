use std::collections::HashMap;

use crate::csp::Problem;
use crate::graph::AdjList;
use crate::graph::generators::directed_path;
use crate::graph::traits::Digraph;

/// Checks whether the digraph `g` homomorphically maps to the digraph `h`.
pub fn is_homomorphic<G, H>(g: &G, h: &H) -> bool
where
    G: Digraph,
    H: Digraph<Vertex = usize>,
{
    Problem::new(g, h).solution_exists()
}

/// Checks whether two digraphs `g` and `h` are homomorphically equivalent.
pub fn is_homomorphically_equivalent<G, H>(g: &G, h: &H) -> bool
where
    G: Digraph<Vertex = usize>,
    H: Digraph<Vertex = usize>,
{
    is_homomorphic(g, h) && is_homomorphic(h, g)
}

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
/// g.add_edge(&0, &2);
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
        let (res, _) = Problem::new(g, h).solve_first();

        if res.is_some() {
            return res;
        }
    }
    None
}
