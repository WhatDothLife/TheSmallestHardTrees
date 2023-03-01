use crate::graph::traits::{Build, Edges};
use itertools::Itertools;
use std::fmt::Debug;
use std::str::FromStr;

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
