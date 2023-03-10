use indexmap::IndexSet;
use std::hash::Hash;

use crate::graph::traits::Digraph;
use crate::graph::AdjMatrix;

use super::{
    domain::Domain,
    solve::{ac_3, solve, Stats},
};

pub type Var = usize;
pub type Value = usize;
pub type Arc = (Var, Var);
pub type Assignment = (Var, Value);

/// An instance of the H-Colouring problem.
#[derive(Clone)]
pub struct Problem<X, A> {
    domains: Vec<Domain<usize>>,
    constraint: HomomorphismConstraint,
    variable_indices: IndexSet<X>,
    value_indices: IndexSet<A>,
    stats: Stats,
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
        let g_index = |x: &X| variable_indices.get_index_of(x).unwrap();
        let h_index = |a: &A| value_indices.get_index_of(a).unwrap();

        let domains: Vec<_> = (0..g.vertex_count())
            .map(|_| Domain::from_iter(0..value_indices.len()))
            .collect();
        let arcs: Vec<_> = g
            .edges()
            .map(|(u, v)| (g_index(&u), g_index(&v)))
            .flat_map(|(u, v)| [(u, v), (v, u)])
            .collect();
        let neighbors = group_neighbors(domains.len(), arcs.clone());
        let constraint = HomomorphismConstraint {
            arcs,
            neighbors,
            g: AdjMatrix::from_edges(g.edges().map(|(u, v)| (g_index(&u), g_index(&v)))),
            h: AdjMatrix::from_edges(h.edges().map(|(u, v)| (h_index(&u), h_index(&v)))),
        };

        Problem {
            domains,
            constraint,
            variable_indices,
            value_indices,
            stats: Stats::default(),
        }
    }

    pub fn precolor(&mut self, x: X, a: A) {
        let var_index = self.variable_indices.get_index_of(&x).unwrap();
        let val_index = self.value_indices.get_index_of(&a).unwrap();
        self.domains[var_index] = Domain::from_iter([val_index]);
    }

    pub fn set_list<I>(&mut self, x: X, list: I)
    where
        I: IntoIterator<Item = A>,
    {
        let var_index = self.variable_indices.get_index_of(&x).unwrap();
        let val_index = |a| self.value_indices.get_index_of(&a).unwrap();
        self.domains[var_index] = Domain::from_iter(list.into_iter().map(val_index));
    }

    pub fn stats(&self) -> Stats {
        self.stats
    }

    pub fn all_singleton(&self) -> bool {
        self.domains.iter().all(|d| d.size() == 1)
    }

    pub fn make_arc_consistent(&mut self) -> bool {
        ac_3(&mut self.domains, &self.constraint, &mut self.stats)
    }

    /// Returns true, if the there exists a solution to the problem.
    pub fn solution_exists(&mut self) -> bool {
        solve(&mut self.domains, &self.constraint, &mut self.stats)
    }

    /// Get the first found solution to the problem
    ///
    /// This is faster than `solve_all`, also in the case where there only is
    /// one solution: the extra work in solve all is the part needed to know
    /// that the solution is unique, in that case. This method can not say if
    /// the solution is unique or not.
    pub fn solve<'a>(&'a mut self) -> Option<Solution<'a, X, A>> {
        if self.solution_exists() {
            Some(Solution {
                raw_solution: (0..self.domains.len())
                    .map(|i| self.domains[i][0])
                    .collect(),
                variable_indices: &self.variable_indices,
                value_indices: &self.value_indices,
            })
        } else {
            None
        }
    }
}

pub struct Solution<'a, X, A> {
    raw_solution: Vec<usize>,
    variable_indices: &'a IndexSet<X>,
    value_indices: &'a IndexSet<A>,
}

impl<X: Hash + Eq + Clone, A> Solution<'_, X, A> {
    pub fn value(&self, x: &X) -> &A {
        let var_index = self.variable_indices.get_index_of(x).unwrap();
        let val_index = self.raw_solution[var_index];
        self.value_indices.get_index(val_index).unwrap()
    }
}

fn group_neighbors<I>(num_vars: usize, arcs: I) -> Vec<Vec<Arc>>
where
    I: IntoIterator<Item = Arc>,
{
    let mut neighbors = vec![Vec::new(); num_vars];
    for (u, v) in arcs {
        neighbors[v].push((u, v));
    }
    neighbors
}

#[derive(Clone, Debug)]
pub struct HomomorphismConstraint {
    arcs: Vec<(usize, usize)>,
    neighbors: Vec<Vec<(usize, usize)>>,
    g: AdjMatrix,
    h: AdjMatrix,
}

pub trait Constraints {
    type ArcIter: Iterator<Item = Arc>;

    /// Returns a vector of arcs, where each arc is a tuple of two variables
    /// `(x, y)` representing a constraint between the two variables.
    fn arcs(&self) -> Self::ArcIter;

    fn neighbors(&self, x: Var) -> Vec<Arc>;

    /// Returns a boolean indicating whether a given assignment `a1` is
    /// consistent with another assignment `a2` with respect to the constraints
    /// defined by the arcs.
    fn check_arc(&self, a1: Assignment, a2: Assignment) -> bool;
}

impl Constraints for HomomorphismConstraint {
    type ArcIter = std::vec::IntoIter<(usize, usize)>;

    fn arcs(&self) -> Self::ArcIter {
        self.arcs.clone().into_iter()
    }

    fn neighbors(&self, x: Var) -> Vec<Arc> {
        self.neighbors[x].clone()
    }

    fn check_arc(&self, (i, ai): Assignment, (j, aj): Assignment) -> bool {
        if self.g.has_edge(i, j) {
            self.h.has_edge(ai, aj)
        } else {
            self.h.has_edge(aj, ai)
        }
    }
}
