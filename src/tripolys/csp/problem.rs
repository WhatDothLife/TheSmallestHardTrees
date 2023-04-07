use indexmap::IndexSet;
use std::{collections::HashMap, hash::Hash};

use crate::graph::{traits::Digraph, AdjList};

use super::{
    solve::{ac_3, solve, Stats},
    state_vec::StateVec,
};

pub type Var = usize;
pub type Value = usize;
pub type Arc = (Var, Var);
pub type Assignment = (Var, Value);

/// A graph homomorphism problem.
#[derive(Clone)]
pub struct Problem<X, A> {
    domains: Vec<StateVec<usize>>,
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
            .map(|_| StateVec::from_iter(0..value_indices.len()))
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
            g: AdjList::from_edges(g.edges().map(|(u, v)| (g_index(&u), g_index(&v)))),
            h: matrix::Matrix::from_edges(h.edges().map(|(u, v)| (h_index(&u), h_index(&v)))),
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
        self.domains[var_index] = StateVec::from_iter([val_index]);
    }

    pub fn set_list<I>(&mut self, x: X, list: I)
    where
        I: IntoIterator<Item = A>,
    {
        let var_index = self.variable_indices.get_index_of(&x).unwrap();
        let val_index = |a| self.value_indices.get_index_of(&a).unwrap();
        self.domains[var_index] = StateVec::from_iter(list.into_iter().map(val_index));
    }

    pub fn stats(&self) -> Stats {
        self.stats
    }

    pub fn all_singleton(&self) -> bool {
        self.domains.iter().all(|d| d.vlen() == 1)
    }

    pub fn make_arc_consistent(&mut self) -> bool {
        ac_3(&mut self.domains, &self.constraint, &mut self.stats)
    }

    /// Returns true, if the there exists a solution to the problem.
    pub fn solution_exists(&mut self) -> bool {
        self.solve_first().is_some()
    }

    /// Get the first found solution to the problem
    ///
    /// This is faster than `solve_all`, also in the case where there only is
    /// one solution: the extra work in solve all is the part needed to know
    /// that the solution is unique, in that case. This method can not say if
    /// the solution is unique or not.
    pub fn solve_first(&mut self) -> Option<HashMap<X, A>> {
        let mut res = None;
        solve(
            &mut self.domains,
            &self.constraint,
            &mut self.stats,
            |sol| {
                res = Some(solution(&sol, &self.variable_indices, &self.value_indices));
            },
            true,
        );
        res
    }

    pub fn solve_all(&mut self) -> Vec<HashMap<X, A>> {
        let mut sols = Vec::new();
        solve(
            &mut self.domains,
            &self.constraint,
            &mut self.stats,
            |sol| {
                sols.push(solution(&sol, &self.variable_indices, &self.value_indices));
            },
            true,
        );
        sols
    }
}

fn solution<X: Hash + Eq + Clone, A: Clone>(
    raw: &[usize],
    variables_indices: &IndexSet<X>,
    value_indices: &IndexSet<A>,
) -> HashMap<X, A> {
    raw.iter()
        .enumerate()
        .map(|(x, a)| (variables_indices[x].clone(), value_indices[*a].clone()))
        .collect()
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
    g: AdjList<usize>,
    h: matrix::Matrix,
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
        if self.g.has_edge(&i, &j) {
            self.h.has_edge(ai, aj)
        } else {
            self.h.has_edge(aj, ai)
        }
    }
}

mod matrix {
    use std::cmp;

    use bitvec::bitvec;
    use bitvec::vec::BitVec;

    /// AdjMatrix is a graph using a matrix representation.
    ///
    /// It is used in the backtracking algorithm, because of frequent edge-lookup
    /// which it implements in O(1).
    #[derive(Clone, Debug, Default)]
    pub struct Matrix {
        adjacencies: BitVec,
        num_vertices: usize,
    }

    impl Matrix {
        pub fn from_edges<I: IntoIterator<Item = (usize, usize)>>(edges: I) -> Self {
            let edges = Vec::from_iter(edges);

            let mut num_vertices = 0;
            for &(u, v) in &edges {
                num_vertices = cmp::max(num_vertices, cmp::max(u, v) + 1);
            }

            let mut adjacencies = bitvec![0; num_vertices * num_vertices];

            for &(u, v) in &edges {
                adjacencies.set(u * num_vertices + v, true);
            }

            Matrix {
                adjacencies,
                num_vertices,
            }
        }

        pub fn has_edge(&self, u: usize, v: usize) -> bool {
            if u >= self.num_vertices || v >= self.num_vertices {
                return false;
            }

            *self.adjacencies.get(u * self.num_vertices + v).unwrap()
        }
    }

    impl FromIterator<(usize, usize)> for Matrix {
        fn from_iter<T: IntoIterator<Item = (usize, usize)>>(iter: T) -> Self {
            Self::from_edges(iter)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::Matrix;

        #[test]
        fn test_from_edges_adj_matrix() {
            let edges = vec![(0, 1), (1, 2), (2, 3)];
            let adj_matrix = Matrix::from_edges(edges);

            assert_eq!(adj_matrix.num_vertices, 4);
            assert_eq!(adj_matrix.adjacencies.len(), 16);
            assert_eq!(adj_matrix.has_edge(0, 1), true);
            assert_eq!(adj_matrix.has_edge(1, 2), true);
            assert_eq!(adj_matrix.has_edge(2, 3), true);
            assert_eq!(adj_matrix.has_edge(3, 0), false);
        }
    }
}
