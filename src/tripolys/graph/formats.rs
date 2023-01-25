use std::io::{Read, Write};
use std::{io, num};

use itertools::Itertools;
use thiserror::Error;

use super::traits::{Digraph, Edges};

/// Prints the graph in dot format.
pub fn to_dot<G, W>(g: &G, output: &mut W) -> Result<(), io::Error>
where
    G: Digraph,
    W: Write,
{
    let mut s = String::from("digraph {\n");
    for v in g.vertices() {
        s.push_str(&format!("\"{}\";\n", v));
    }
    for (u, v) in g.edges() {
        s.push_str(&format!("\"{}\" -> \"{}\";\n", u, v));
    }
    s.push('}');
    output.write_all(s.as_bytes())?;

    Ok(())
}

/// Prints the graph in dot format.
pub fn to_edge_list<G, W>(g: &G, output: &mut W) -> Result<(), io::Error>
where
    G: Digraph,
    W: Write,
{
    let mut s = String::from("[");
    for (u, v) in g.edges() {
        s.push_str(&format!("({},{})", u, v));
    }
    s.push(']');
    output.write_all(s.as_bytes())?;

    Ok(())
}

/// Prints the graph in csv format.
pub fn to_csv<G, W>(g: &G, output: &mut W) -> Result<(), io::Error>
where
    G: Edges,
    W: std::io::Write,
{
    let bytes = g
        .edges()
        .flat_map(|(u, v)| format!("{};{}\n", u, v).into_bytes())
        .collect_vec();
    output.write_all(&bytes)?;

    Ok(())
}

/// Reads a graph from csv format.
pub fn from_csv<G, R>(mut read: R) -> Result<G, CsvError>
where
    G: FromIterator<(usize, usize)>,
    R: Read,
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
        .map(|(u, v)| (u.parse::<usize>().unwrap(), v.parse::<usize>().unwrap()))
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
    // let nvertices = s.len() - 1;
    // let mut g = G::with_capacities(nvertices, nvertices - 1);
    // let vertices: Vec<_> = (0..nvertices).map(|_| g.add_vertex()).collect();
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
            ParseTriadError::InvalidCharacter(c) => write!(f, "Could not parse: {}", c),
        }
    }
}

impl std::error::Error for ParseTriadError {}
