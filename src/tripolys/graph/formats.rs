//! Reading and writing of graph formats.

use super::traits::{Digraph, Edges};
use itertools::Itertools;
use std::{fmt, io};

/// Prints the graph in dot format.
pub fn to_dot<G, W>(g: G, output: &mut W) -> Result<(), io::Error>
where
    G: Digraph,
    W: io::Write,
    G::Vertex: fmt::Debug,
{
    let mut s = String::from("digraph {\n");
    for v in g.vertices() {
        s.push_str(&format!("\"{v:?}\";\n"));
    }
    for (u, v) in g.edges() {
        s.push_str(&format!("\"{u:?}\" -> \"{v:?}\";\n"));
    }
    s.push('}');
    output.write_all(s.as_bytes())?;

    Ok(())
}

/// Prints the graph in csv format.
pub fn to_csv<G, W>(g: G, output: &mut W) -> Result<(), io::Error>
where
    G: Edges,
    W: io::Write,
    G::Vertex: fmt::Debug,
{
    let bytes = g
        .edges()
        .flat_map(|(u, v)| format!("{u:?};{v:?}\n").into_bytes())
        .collect_vec();
    output.write_all(&bytes)?;

    Ok(())
}
