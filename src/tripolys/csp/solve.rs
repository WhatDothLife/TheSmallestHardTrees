use crate::graph::traits::HasEdge;
use std::time::{Duration, Instant};

use crate::graph::AdjMatrix;

use super::domain::Domain;

type Value = usize;
type Variable = usize;
pub type Arc = (Variable, Variable, Direction);

#[derive(Clone, Copy, Debug)]
pub enum Direction {
    Forward,
    Backward,
}

// Macros to trace debug logging

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

macro_rules! stat {
    ($c:ident . $field:ident $($t:tt)*) => {
        $c.stats.$field $($t)*;
    }
}

fn debug_print(domains: &Vec<Domain<Value>>) {
    for (i, d) in domains.iter().enumerate() {
        println!("{:?} -> {:?}", i, d.iter().collect::<Vec<_>>());
    }
}

enum Revision {
    Modified,
    Unchanged,
    Empty,
}

fn revise(
    (x, y, dir): Arc,
    domains: &mut Vec<Domain<Value>>,
    template: &AdjMatrix,
    config: &mut SolveConfig,
    mut trail: Option<&mut Vec<Vec<Variable>>>,
) -> Revision {
    let mut result = Revision::Unchanged;

    for i in (0..domains[x].size()).rev() {
        let mut is_possible = false;
        let ai = domains[x][i];

        for &aj in &domains[y] {
            stat!(config.ccks += 1);
            match dir {
                Direction::Forward => {
                    if template.has_edge(ai, aj) {
                        is_possible = true;
                        break;
                    }
                }
                Direction::Backward => {
                    if template.has_edge(aj, ai) {
                        is_possible = true;
                        break;
                    }
                }
            }
        }

        if !is_possible {
            // If used for backtracking we save the state of the variable
            if let Some(ref mut trail) = trail {
                if !domains[x].is_modified() {
                    domains[x].push_state();
                    trail.last_mut().unwrap().push(x);
                }
            }
            domains[x].remove(i);
            result = Revision::Modified;

            if domains[x].is_empty() {
                return Revision::Empty;
            }
        }
    }

    result
}

pub fn mac3<I>(
    domains: &mut Vec<Domain<Value>>,
    arcs: I,
    neighbors: &Vec<Vec<Arc>>,
    template: &AdjMatrix,
    config: &mut SolveConfig,
    trail: &mut Vec<Vec<Variable>>,
) -> bool
where
    I: IntoIterator<Item = Arc>,
{
    let mut work_list = Vec::from_iter(arcs);

    while let Some(arc) = work_list.pop() {
        match revise(arc, domains, template, config, Some(trail)) {
            Revision::Modified => {
                work_list.extend(neighbors[arc.0].iter().copied());
            }
            Revision::Empty => {
                return false;
            }
            Revision::Unchanged => {}
        }
    }
    true
}

pub fn ac3<I>(
    domains: &mut Vec<Domain<Value>>,
    arcs: I,
    neighbors: &Vec<Vec<Arc>>,
    template: &AdjMatrix,
    config: &mut SolveConfig,
) -> bool
where
    I: IntoIterator<Item = Arc>,
{
    let mut work_list = Vec::from_iter(arcs);

    while let Some(arc) = work_list.pop() {
        match revise(arc, domains, template, config, None) {
            Revision::Modified => {
                work_list.extend(neighbors[arc.0].iter().copied());
            }
            Revision::Empty => {
                return false;
            }
            Revision::Unchanged => {}
        }
    }
    true
}

#[derive(Clone, Debug)]
pub(crate) enum SolveError {
    /// Used internally to stop after the first solution (if enabled)
    RequestedStop,
}

/// Statistics from the execution of the backtracking search.
#[derive(Clone, Copy, Debug, Default)]
pub struct SolveStats {
    /// Number of consistency checks
    pub ccks: u32,
    /// Number of recursive calls
    pub calls: u32,
    /// Number of backtracks from dead ends
    pub backtracks: u32,
    /// Number of solutions emitted
    pub solutions: u32,
    /// Duration of the arc-consistency preprocessing
    pub ac3_time: Duration,
    /// Duration of the entire solving process
    pub mac3_time: Duration,
}

/// Configuration for backtracking
#[derive(Clone, Debug, Default)]
pub struct SolveConfig {
    /// If true, stop at first solution
    pub stop_at_first: bool,
    /// Statistics
    pub stats: SolveStats,
}

pub fn solve<A>(
    domains: &mut Vec<Domain<Value>>,
    arcs: A,
    neighbors: &Vec<Vec<Arc>>,
    template: &AdjMatrix,
    mut out: impl FnMut(Vec<Value>),
    config: &mut SolveConfig,
) where
    A: IntoIterator<Item = Arc>,
{
    trace!("Backtracking start");
    // if_trace!(self.domains.debug_print());

    if_trace!("Preprocessing with AC-3");
    let tstart = Instant::now();
    let ac = ac3(domains, arcs, neighbors, template, config);
    let tend = tstart.elapsed();
    stat!(config.ac3_time = tend);

    if_trace!(debug_print(domains));

    let mut stack: Vec<_> = (0..domains.len()).collect();
    let domain_sizes = domains.iter().map(|d| d.size()).collect::<Vec<_>>();
    stack.sort_unstable_by(|a, b| domain_sizes[*b].cmp(&domain_sizes[*a]));

    let mut trail = Vec::new();

    if ac {
        let tstart = Instant::now();
        let _ = solve_recursive(
            &mut stack, domains, neighbors, template, &mut out, config, &mut trail,
        );
        let tend = tstart.elapsed();
        stat!(config.mac3_time = tend);
    }
}

/// The solver runs through the whole search tree if not interrupted; the
/// BTError status is used to short-circuit and exit as soon as possible if
/// requested.
fn solve_recursive<F>(
    stack: &mut Vec<Variable>,
    domains: &mut Vec<Domain<Value>>,
    neighbors: &Vec<Vec<Arc>>,
    template: &AdjMatrix,
    out: &mut F,
    config: &mut SolveConfig,
    trail: &mut Vec<Vec<Variable>>,
) -> Result<(), SolveError>
where
    F: FnMut(Vec<usize>),
{
    stat!(config.calls += 1);

    if stack.is_empty() {
        let solution = domains.iter().map(|d| d[0]).collect();
        trace!("==> Valid solution: {:?}", solution);
        stat!(config.solutions += 1);
        out(solution);

        if config.stop_at_first {
            return Err(SolveError::RequestedStop);
        }
    }

    let mut status = Ok(());
    let x = stack.pop().unwrap();
    trace!("Selected variable = {}", x);

    for i in 0..domains[x].size() {
        trace!("Assignment: {} -> {}", x, domains[x][i]);

        trail.push(vec![x]);
        domains[x].push_state();
        domains[x].assign(i);

        if mac3(
            domains,
            neighbors[x].clone(),
            neighbors,
            template,
            config,
            trail,
        ) {
            trace!("Propagation successful, recursing...");
            // Repeat the algorithm recursively on the reduced domains
            status = solve_recursive(stack, domains, neighbors, template, out, config, trail);
        } else {
            trace!("Detected inconsistency, backtracking...");
            stat!(config.backtracks += 1);
        }
        for x in trail.pop().unwrap() {
            domains[x].pop_state();
        }

        if status.is_err() {
            break;
        }
    }
    stack.push(x);

    status
}
