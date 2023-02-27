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

// /// Reads a graph from csv format.
// pub fn from_csv<G, R>(input: R) -> Result<G, CsvError>
// where
//     G: Build,
//     R: io::Read,
//     G::Vertex: FromStr,
// {
//     let reader = io::BufReader::new(input);
//     let mut g = G::default();

//     for (i, line) in reader.lines().enumerate() {
//         let line = line?;
//         if let Some((v, w)) = line.split(&[',', ';', '|', ' ']).next_tuple() {
//             g.add_edge(v.parse()?, w.parse()?);
//         } else {
//             return Err(CsvError::MissingSeparator(i + 1));
//         }
//     }
//     Ok(g)
// }

// #[derive(Error, Debug)]
// pub enum CsvError {
//     #[error("Separator missing in line {0}")]
//     MissingSeparator(usize),
//     #[error("{0}")]
//     Io(#[from] io::Error),
//     #[error("{0}")]
//     Parse(#[from] num::ParseIntError),
// }
