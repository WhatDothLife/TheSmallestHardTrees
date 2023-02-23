//! Reading and writing of graph formats.

use std::{fmt, io, num};

use itertools::Itertools;
use thiserror::Error;

use super::traits::{Digraph, Edges};

/// Prints the graph in dot format.
pub fn to_dot<G, W>(g: G, output: &mut W) -> Result<(), io::Error>
where
    G: Digraph,
    W: io::Write,
    G::Vertex: fmt::Display,
{
    let mut s = String::from("digraph {\n");
    for v in g.vertices() {
        s.push_str(&format!("\"{v}\";\n"));
    }
    for (u, v) in g.edges() {
        s.push_str(&format!("\"{u}\" -> \"{v}\";\n"));
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
    G::Vertex: fmt::Display,
{
    let bytes = g
        .edges()
        .flat_map(|(u, v)| format!("{u};{v}\n").into_bytes())
        .collect_vec();
    output.write_all(&bytes)?;

    Ok(())
}

/// Reads a graph from csv format.
pub fn from_csv<G, R>(mut read: R) -> Result<G, CsvError>
where
    G: FromIterator<(usize, usize)>,
    R: io::Read,
{
    let mut content = String::new();
    read.read_to_string(&mut content)?;
    let mut edges = Vec::new();

    for (i, line) in content.lines().enumerate() {
        if let Some((v, w)) = line.split(&[',', ';', '|', ' ']).next_tuple() {
            edges.push((v.parse()?, w.parse()?));
        } else {
            return Err(CsvError::MissingSeparator(i + 1));
        }
    }
    Ok(G::from_iter(edges))
}

pub fn from_edge_list<G>(s: &str) -> G
where
    G: FromIterator<(usize, usize)>,
{
    s.split(&['[', ']', ',', '(', ')', '"', ';'])
        .filter(|&x| !x.is_empty())
        .tuples()
        .map(|(u, v)| (u.parse().unwrap(), v.parse().unwrap()))
        .collect()
}

#[derive(Error, Debug)]
pub enum CsvError {
    #[error("Separator missing in line {0}")]
    MissingSeparator(usize),
    #[error("{0}")]
    Io(#[from] io::Error),
    #[error("{0}")]
    Parse(#[from] num::ParseIntError),
}

pub fn from_triad<G>(s: &str) -> Result<G, ParseTriadError>
where
    G: FromIterator<(usize, usize)>,
{
    if s.matches(',').count() != 2 {
        return Err(ParseTriadError::NumArms);
    }

    let mut edges = Vec::new();
    let mut j = 1;

    for arm in s.split(',') {
        for (i, c) in arm.chars().enumerate() {
            match c {
                '1' => {
                    if i == 0 {
                        edges.push((j, 0));
                    } else {
                        edges.push((j, j - 1));
                    }
                }
                '0' => {
                    if i == 0 {
                        edges.push((0, j));
                    } else {
                        edges.push((j - 1, j));
                    }
                }
                c => {
                    return Err(ParseTriadError::InvalidCharacter(c));
                }
            }
            j += 1;
        }
    }

    Ok(G::from_iter(edges))
}

#[derive(Debug)]
pub enum ParseTriadError {
    NumArms,
    InvalidCharacter(char),
}

impl std::fmt::Display for ParseTriadError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            ParseTriadError::NumArms => write!(f, "A triad must have exactly 3 arms!"),
            ParseTriadError::InvalidCharacter(c) => write!(f, "Could not parse: {c}"),
        }
    }
}

impl std::error::Error for ParseTriadError {}


pub fn edge_list<G>(g: G) -> String
where
    G::Vertex: std::fmt::Display,
    G: Edges,
{
    let mut s = String::from("[");
    for (i, (u, v)) in g.edges().enumerate() {
        if i != 0 {
            s.push(',');
        }
        s.push_str(&format!("({u},{v})"));
    }
    s.push(']');

    s
}
