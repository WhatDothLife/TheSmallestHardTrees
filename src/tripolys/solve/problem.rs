use crate::graph::traits::{Edge, Vertex};
use std::cmp;

use crate::graph::traits::{Edges, Vertices};
use crate::graph::AdjMatrix;

use super::domain::Domain;
use super::solver::{mac3, solve, SolveConfig, SolveStats};

/// An instance of the H-Colouring problem
pub struct Problem {
    domains: Vec<Domain<Vertex>>,
    arcs: Vec<Edge>,
    neighbors: Vec<Vec<Edge>>,
    h: AdjMatrix,
    stats: SolveStats,
}

impl Problem {
    pub fn new<G, H>(g: G, h: H) -> Problem
    where
        G: Edges,
        H: Edges,
    {
        let h = AdjMatrix::from_edges(h.edges());
        let arcs = Vec::from_iter(g.edges());
        let mut max = 0;

        for &(u, v) in &arcs {
            max = cmp::max(max, cmp::max(u, v));
        }
        let domains = (0..max).map(|_| Domain::from_iter(h.vertices())).collect();
        let mut neighbors: Vec<Vec<Edge>> = (0..max).map(|_| Vec::new()).collect();

        for &(u, v) in &arcs {
            neighbors[v].push((u, v));
        }

        Problem {
            domains,
            arcs,
            neighbors,
            h,
            stats: SolveStats::default(),
        }
    }

    pub fn set_value(&mut self, vertex: usize, value: usize) {
        self.domains[vertex] = Domain::from_iter([value]);
    }

    pub fn set_domain<I>(&mut self, vertex: usize, domain: I)
    where
        I: IntoIterator<Item = usize>,
    {
        self.domains[vertex] = Domain::from_iter(domain);
    }

    pub fn stats(&self) -> &SolveStats {
        &self.stats
    }

    pub fn make_arc_consistent(&mut self) -> bool {
        mac3(
            &mut self.domains,
            self.arcs.clone(),
            &self.neighbors,
            &self.h,
            &mut self.stats,
        )
    }

    /// Returns true, if the there exists a solution to the problem.
    pub fn solution_exists(&mut self) -> bool {
        self.solve_first().is_some()
    }

    pub fn domains(&self) -> impl Iterator<Item = &Domain<usize>> + '_ {
        self.domains.iter()
    }

    /// Get the first found solution to the problem
    ///
    /// This is faster than `solve_all`, also in the case where there only is
    /// one solution: the extra work in solve all is the part needed to know
    /// that the solution is unique, in that case. This method can not say if
    /// the solution is unique or not.
    pub fn solve_first(&mut self) -> Option<Vec<usize>> {
        let mut config = SolveConfig::default();
        config.stop_at_first = true;
        let mut solution = None;
        self.solve(&mut config, |s| solution = Some(s));
        solution
    }

    /// Get all solutions to the sudoku problem
    ///
    /// The problem is unmodified after the end of this method, and could be solved
    /// the same way again.
    pub fn solve_all(&mut self, out: impl FnMut(Vec<usize>)) {
        let mut config = SolveConfig::default();
        self.solve(&mut config, out);
    }

    fn solve(&mut self, config: &mut SolveConfig, out: impl FnMut(Vec<usize>)) {
        solve(
            &mut self.domains,
            self.arcs.clone(),
            &self.neighbors,
            &self.h,
            out,
            config,
        )
    }
}
