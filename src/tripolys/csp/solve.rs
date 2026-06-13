use std::time::{Duration, Instant};

use itertools::Itertools;

use crate::graph::{traits::Digraph, AdjList};

use super::{
    problem::{Arc, Matrix, Value, Var},
    state_vec::StateVec,
};

#[cfg(feature = "trace")]
macro_rules! if_trace {
    ($($t:tt)*) => { $($t)* }
}

#[cfg(not(feature = "trace"))]
macro_rules! if_trace {
    ($($t:tt)*) => {};
}

macro_rules! trace {
    ($($t:tt)*) => { if_trace!(eprintln!($($t)*)) }
}

/// Statistics from the execution of the backtracking search.
#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    /// Number of consistency checks
    pub ccks: u32,
    /// Number of backtracks from dead ends
    pub backtracks: u32,
    /// Number of assignments
    pub assignments: u32,
    /// Duration of the arc-consistency preprocessing
    pub ac3_time: Duration,
    /// Duration of the backtracking
    pub mac3_time: Duration,
}

#[derive(Copy, Clone, Debug)]
enum Revision {
    Unchanged,
    Changed,
    Empty,
}

#[inline]
fn check_arc(g: &AdjList<usize>, h: &Matrix, (i, ai): (Var, Value), (j, aj): (Var, Value)) -> bool {
    if g.has_edge(&i, &j) {
        h.has_edge(ai, aj)
    } else {
        h.has_edge(aj, ai)
    }
}

pub(super) struct Solver<'a> {
    lists: &'a mut Vec<StateVec<Value>>,
    g: &'a AdjList<usize>,
    h: &'a Matrix,
    pub(super) arcs: Vec<Arc>,
    neighbors: Vec<Vec<Arc>>,
    pub(super) stats: Stats,
}

impl<'a> Solver<'a> {
    pub(super) fn new(
        lists: &'a mut Vec<StateVec<Value>>,
        g: &'a AdjList<usize>,
        h: &'a Matrix,
    ) -> Self {
        let arcs: Vec<Arc> = g.edges().flat_map(|(u, v)| [(u, v), (v, u)]).collect();
        let neighbors = group_neighbors(lists.len(), &arcs);
        Solver {
            lists,
            g,
            h,
            arcs,
            neighbors,
            stats: Stats::default(),
        }
    }

    fn revise(&mut self, x: Var, y: Var, mut trail: Option<&mut Vec<Var>>) -> Revision {
        let mut revision = Revision::Unchanged;

        for i in (0..self.lists[x].vlen()).rev() {
            let mut is_possible = false;

            for &ay in self.lists[y].iter() {
                let ax = self.lists[x][i];
                self.stats.ccks += 1;
                if check_arc(self.g, self.h, (x, ax), (y, ay)) {
                    is_possible = true;
                    break;
                }
            }

            if !is_possible {
                if let Some(ref mut trail) = trail {
                    if !self.lists[x].is_modified() {
                        self.lists[x].save_state();
                        trail.push(x);
                    }
                }
                self.lists[x].remove(i);
                revision = Revision::Changed;
                if self.lists[x].is_empty() {
                    return Revision::Empty;
                }
            }
        }

        revision
    }

    pub(super) fn propagate(
        &mut self,
        work_list: &mut Vec<Arc>,
        mut trail: Option<&mut Vec<Var>>,
    ) -> bool {
        while let Some((x, y)) = work_list.pop() {
            match self.revise(x, y, trail.as_deref_mut()) {
                Revision::Unchanged => {}
                Revision::Changed => work_list.extend(self.neighbors[x].iter().copied()),
                Revision::Empty => return false,
            }
        }
        true
    }

    pub(super) fn solve(&mut self) -> Option<Vec<Value>> {
        trace!("  > Preprocessing with AC-3");
        let t_start = Instant::now();
        let consistent = self.propagate(&mut self.arcs.clone(), None);
        self.stats.ac3_time = t_start.elapsed();

        if !consistent {
            return None;
        }

        trace!("  > Solving with MAC-3");
        let t_start = Instant::now();
        let result = self.solve_iterative();
        self.stats.mac3_time = t_start.elapsed();

        result
    }

    fn solve_iterative(&mut self) -> Option<Vec<Value>> {
        let variables: Vec<Var> = (0..self.lists.len())
            .sorted_by_key(|&x| self.lists[x].vlen())
            .collect();
        let mut assignments = vec![0; self.lists.len()];
        let mut states: Vec<Vec<Var>> = Vec::new();
        let mut depth = 0;

        loop {
            if depth == variables.len() {
                let solution = self.lists.iter().map(|d| d[0]).collect();
                trace!("==> Valid solution: {:?}", solution);
                return Some(solution);
            }

            let x = variables[depth];
            let a = assignments[depth];

            if a == self.lists[x].vlen() {
                trace!("    - Tried every assignment for {}, backtracking...", x);
                if depth == 0 {
                    return None;
                }
                let trail = states.pop().unwrap();
                for x in trail {
                    self.lists[x].restore_state();
                }
                assignments[depth] = 0;
                depth -= 1;
                self.stats.backtracks += 1;
                continue;
            }

            trace!("    - Assignment: {} -> {}", x, a);
            self.lists[x].save_state();
            self.lists[x].set(a);
            self.stats.assignments += 1;
            assignments[depth] = a + 1;

            let mut trail = vec![x];
            let mut work_list = self.neighbors[x].clone();
            if self.propagate(&mut work_list, Some(&mut trail)) {
                trace!("    - Forward check succeeded");
                states.push(trail);
                depth += 1;
            } else {
                trace!("    - Forward check failed");
                for x in trail {
                    self.lists[x].restore_state();
                }
            }
        }
    }
}

fn group_neighbors(num_vars: usize, arcs: &[Arc]) -> Vec<Vec<Arc>> {
    let mut neighbors = vec![Vec::new(); num_vars];
    for &(u, v) in arcs {
        neighbors[v].push((u, v));
    }
    neighbors
}
