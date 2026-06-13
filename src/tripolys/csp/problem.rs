use std::{cmp, collections::HashMap, hash::Hash};

use bitvec::{bitvec, vec::BitVec};
use indexmap::IndexSet;

use crate::graph::{
    traits::Digraph,
    AdjList,
};

use super::solve::{Solver, Stats};
use super::state_vec::StateVec;

pub type Var = usize;
pub type Value = usize;
pub type Arc = (Var, Var);

/// Adjacency matrix for O(1) edge lookup during constraint checking.
#[derive(Clone, Debug, Default)]
pub(super) struct Matrix {
    adjacencies: BitVec,
    pub(super) num_vertices: usize,
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


/// A graph homomorphism problem.
#[derive(Clone)]
pub struct Problem<V> {
    pub(super) lists: Vec<StateVec<usize>>,
    pub(super) g: AdjList<usize>,
    pub(super) h: Matrix,
    pub(super) vertex_order: IndexSet<V>,
}

impl<V> Problem<V>
where
    V: Clone + Hash + Eq,
{
    pub fn new<G, H>(g: G, h: H) -> Problem<V>
    where
        G: Digraph<Vertex = V>,
        H: Digraph<Vertex = usize>,
    {
        let vertex_order: IndexSet<_> = g.vertices().collect();
        let g_index = |x: &V| vertex_order.get_index_of(x).unwrap();

        let lists = (0..g.vertex_count())
            .map(|_| StateVec::from_iter(0..h.vertex_count()))
            .collect();

        let g_indexed =
            AdjList::from_edges(g.edges().map(|(u, v)| (g_index(&u), g_index(&v))));
        let h_matrix = Matrix::from_edges(h.edges());

        Problem {
            lists,
            g: g_indexed,
            h: h_matrix,
            vertex_order,
        }
    }

    pub fn precolor(&mut self, v: V, a: usize) {
        let var_index = self.vertex_order.get_index_of(&v).unwrap();
        self.lists[var_index] = StateVec::from_iter([a]);
    }

    pub fn set_list<I>(&mut self, v: V, list: I)
    where
        I: IntoIterator<Item = usize>,
    {
        let var_index = self.vertex_order.get_index_of(&v).unwrap();
        self.lists[var_index] = StateVec::from_iter(list);
    }

    pub fn all_singleton(&self) -> bool {
        self.lists.iter().all(|d| d.vlen() == 1)
    }

    pub fn make_arc_consistent(&mut self) -> bool {
        let mut solver = Solver::new(&mut self.lists, &self.g, &self.h);
        let mut work_list = solver.arcs.clone();
        solver.propagate(&mut work_list, None)
    }

    pub fn solution_exists(&mut self) -> bool {
        self.solve_first().0.is_some()
    }

    pub fn solve_first(&mut self) -> (Option<HashMap<V, usize>>, Stats) {
        let mut solver = Solver::new(&mut self.lists, &self.g, &self.h);
        let result = solver.solve().map(|sol| decode(&sol, &self.vertex_order));
        (result, solver.stats)
    }
}

fn decode<V: Clone + Hash + Eq>(raw: &[usize], vertex_order: &IndexSet<V>) -> HashMap<V, usize> {
    raw.iter()
        .enumerate()
        .map(|(var, &val)| (vertex_order[var].clone(), val))
        .collect()
}


#[cfg(test)]
mod tests {
    use super::Matrix;

    #[test]
    fn test_matrix() {
        let edges = vec![(0, 1), (1, 2), (2, 3)];
        let m = Matrix::from_edges(edges);

        assert_eq!(m.num_vertices, 4);
        assert_eq!(m.adjacencies.len(), 16);
        assert!(m.has_edge(0, 1));
        assert!(m.has_edge(1, 2));
        assert!(m.has_edge(2, 3));
        assert!(!m.has_edge(3, 0));
    }
}
