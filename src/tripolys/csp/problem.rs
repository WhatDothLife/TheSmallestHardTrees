use indexmap::IndexSet;
use std::hash::Hash;

use crate::graph::traits::Digraph;
use crate::graph::AdjMatrix;

use super::domain::Domain;
use super::solve::{ac3, solve, Arc, Direction, SolveConfig, SolveStats};

/// An instance of the H-Colouring problem.
#[derive(Clone)]
pub struct Problem<X, A> {
    domains: Vec<Domain<usize>>,
    template: AdjMatrix,
    arcs: Vec<Arc>,
    variable_indices: IndexSet<X>,
    value_indices: IndexSet<A>,
    stats: Option<SolveStats>,
}

impl<X, A> Problem<X, A>
where
    X: Clone + Hash + Eq,
    A: Clone + Hash + Eq,
{
    pub fn new<G, H>(g: G, h: H) -> Problem<X, A>
    where
        G: Digraph<Vertex = X>,
        H: Digraph<Vertex = A>,
    {
        let variable_indices: IndexSet<_> = g.vertices().collect();
        let value_indices: IndexSet<_> = h.vertices().collect();

        let domains = (0..g.vertex_count())
            .map(|_| Domain::from_iter(0..value_indices.len()))
            .collect();
        let template = AdjMatrix::from_edges(h.edges().map(|(u, v)| {
            (
                value_indices.get_index_of(&u).unwrap(),
                value_indices.get_index_of(&v).unwrap(),
            )
        }));
        let arcs: Vec<_> = g
            .edges()
            .map(|(u, v)| {
                (
                    variable_indices.get_index_of(&u).unwrap(),
                    variable_indices.get_index_of(&v).unwrap(),
                )
            })
            .flat_map(|(u, v)| [(u, v, Direction::Forward), (v, u, Direction::Backward)])
            .collect();

        Problem {
            domains,
            template,
            value_indices,
            variable_indices,
            arcs,
            stats: None,
        }
    }

    pub fn set_value(&mut self, x: X, a: A) {
        let var_index = self.variable_indices.get_index_of(&x).unwrap();
        let val_index = self.value_indices.get_index_of(&a).unwrap();
        self.domains[var_index] = Domain::from_iter([val_index]);
    }

    pub fn set_domain<D>(&mut self, x: X, domain: D)
    where
        D: IntoIterator<Item = A>,
    {
        let var_index = self.variable_indices.get_index_of(&x).unwrap();
        let val_index = |a| self.value_indices.get_index_of(&a).unwrap();
        let domain = Domain::from_iter(domain.into_iter().map(val_index));
        self.domains[var_index] = domain;
    }

    pub fn stats(&self) -> Option<SolveStats> {
        self.stats
    }

    pub fn make_arc_consistent(&mut self) -> bool {
        let neighbors = self.neighbors();
        ac3(
            &mut self.domains,
            self.arcs.clone(),
            &neighbors,
            &self.template,
            &mut SolveConfig::default(),
        )
    }

    /// Returns true, if the there exists a solution to the problem.
    pub fn solution_exists(&mut self) -> bool {
        self.solve_first().is_some()
    }

    pub fn domains(&self) -> impl Iterator<Item = &Domain<usize>> {
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
        self.stats = Some(config.stats);
        solution
    }

    /// Get all solutions to the sudoku problem
    ///
    /// The problem is unmodified after the end of this method, and could be solved
    /// the same way again.
    pub fn solve_all(&mut self, out: impl FnMut(Vec<usize>)) {
        let mut config = SolveConfig::default();
        self.solve(&mut config, out);
        self.stats = Some(config.stats);
    }

    fn solve(&mut self, config: &mut SolveConfig, out: impl FnMut(Vec<usize>)) {
        let neighbors = self.neighbors();

        solve(
            &mut self.domains,
            self.arcs.clone(),
            &neighbors,
            &self.template,
            out,
            config,
        );
    }

    fn neighbors(&self) -> Vec<Vec<Arc>> {
        let mut neighbors = vec![Vec::new(); self.domains.len()];
        for &(u, v, dir) in &self.arcs {
            neighbors[v].push((u, v, dir));
        }
        neighbors
    }
}
