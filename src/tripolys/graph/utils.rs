use crate::csp::Problem;
use crate::graph::traits::{Build, Edges};
use itertools::Itertools;
use std::collections::HashMap;
use std::fmt::Debug;
use std::str::FromStr;

use super::classes::directed_path;
use super::traits::Digraph;
use super::AdjList;

/// Parses a string representing an edge list into a graph.
///
/// The edge list should be in the format `[(u1,v1),(u2,v2),...]`.
pub fn parse_edge_list<G>(edge_list: &str) -> Result<G, String>
where
    G: Build,
    G::Vertex: FromStr,
{
    let edge_list = edge_list.trim_start_matches('[').trim_end_matches(']');

    let vertices = edge_list
        .split(&[',', '(', ')'])
        .filter(|&x| !x.is_empty())
        .map(|v| {
            v.parse::<G::Vertex>()
                .map_err(|_| format!("Invalid character: {}", v))
        })
        .collect::<Result<Vec<G::Vertex>, String>>()?;

    // Ensure that the number of vertices is even, i.e., the edge list is well-formed.
    if vertices.len() % 2 != 0 {
        return Err("Invalid edge list: odd number of vertices".to_owned());
    }
    let g = G::from_edges(vertices.into_iter().tuples());

    Ok(g)
}

/// Converts a graph to a string representing an edge list.
///
/// The edge list is in the format `[(u1,v1),(u2,v2),...]`.
pub fn edge_list<G>(g: G) -> String
where
    G::Vertex: Debug,
    G: Edges,
{
    let mut s = String::from("[");
    for (i, (u, v)) in g.edges().enumerate() {
        if i != 0 {
            s.push(',');
        }
        s.push_str(&format!("({u:?},{v:?})"));
    }
    s.push(']');

    s
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
/// use tripolys::graph::utils::is_balanced;
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
    let h: AdjList<_> = directed_path(g.edge_count());
    Problem::new(g, h).solution_exists()
}

/// Computes the levels of a balanced digraph `g`,
///
/// Returns a `HashMap` where the keys are the vertices of `g` and the values
/// are their levels, or `None` if `g` is not balanced.
///
/// # Examples
///
/// ```
/// use tripolys::graph::AdjList;
/// use tripolys::graph::utils::levels;
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
        let mut problem = Problem::new(g, h);

        if let Some(sol) = problem.solve() {
            let levels: HashMap<_, _> = g.vertices().map(|v| (v.clone(), *sol.value(&v))).collect();
            return Some(levels);
        }
    }
    None
}
