use crate::graph::traits::{Edge, Edges, Vertex};
use std::time::{Duration, Instant};

use crate::graph::AdjMatrix;

use super::domain::Domain;

// These macros are used trace debug logging

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

enum Revision {
    Mutated,
    Unchanged,
    Empty,
}

fn revise(
    x: Vertex,
    y: Vertex,
    domains: &mut Vec<Domain<usize>>,
    h: &AdjMatrix,
    stats: &mut SolveStats,
) -> Revision {
    let mut result = Revision::Unchanged;

    for i in (0..domains[x].size()).rev() {
        let mut is_possible = false;

        for aj in &domains[y] {
            stats.ccks += 1;
            if h.has_edge(domains[x][i], *aj) {
                is_possible = true;
                break;
            }
        }

        if !is_possible {
            domains[x].remove(i);
            result = Revision::Mutated;

            if domains[x].is_empty() {
                return Revision::Empty;
            }
        }
    }

    result
}

pub fn mac3<A>(
    domains: &mut Vec<Domain<usize>>,
    arcs: A,
    neighbors: &Vec<Vec<(Vertex, Vertex)>>,
    h: &AdjMatrix,
    stats: &mut SolveStats,
) -> bool
where
    A: IntoIterator<Item = (Vertex, Vertex)>,
{
    let mut work_list = Vec::from_iter(arcs);

    while let Some((x, y)) = work_list.pop() {
        match revise(x, y, domains, h, stats) {
            Revision::Mutated => {
                work_list.extend(neighbors[x].iter().copied());
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
#[derive(Clone, Debug, Default)]
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
    /// Sort the stack of variables after initial run of AC-3 (smallest domain first)
    pub sort_stack: bool,
    /// If true, stop at first solution
    pub stop_at_first: bool,
    /// If true, record statistics during the search
    pub record_stats: bool,
    /// Statistics
    pub stats: SolveStats,
}

pub fn solve<A>(
    domains: &mut Vec<Domain<Vertex>>,
    arcs: A,
    neighbors: &Vec<Vec<Edge>>,
    h: &AdjMatrix,
    mut out: impl FnMut(Vec<Vertex>),
    config: &mut SolveConfig,
) where
    A: IntoIterator<Item = Edge>,
{
    trace!("Backtracking start");
    // if_trace!(self.domains.debug_print());


    if_trace!("Preprocessing with AC-3");
    let tstart = Instant::now();
    let ac = mac3(
        domains,
        neighbors.iter().flatten().copied(),
        &neighbors,
        &h,
        &mut config.stats,
    );
    let tend = tstart.elapsed();
    stat!(config.ac3_time = tend);

    if_trace!(debug_print(domains));

    let mut stack: Vec<_> = (0..domains.len()).collect();
    // TODO sort

    if ac {
        let tstart = Instant::now();
        let _ = solve_inner(&mut stack, domains, &neighbors, &h, &mut out, config);
        let tend = tstart.elapsed();
        stat!(config.mac3_time = tend);
    }
}

/// The solver runs through the whole search tree if not interrupted; the
/// BTError status is used to short-circuit and exit as soon as possible if
/// requested.
fn solve_inner<F>(
    stack: &mut Vec<Vertex>,
    domains: &mut Vec<Domain<Vertex>>,
    neighbors: &Vec<Vec<Edge>>,
    h: &AdjMatrix,
    out: &mut F,
    config: &mut SolveConfig,
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
        for d in &mut *domains {
            d.push_state();
        }

        domains[x].assign(i);

        if mac3(domains, neighbors[x].clone(), neighbors, h, &mut config.stats) {
            trace!("Propagation successful, recursing...");
            // Repeat the algorithm recursively on the reduced domains
            status = solve_inner(stack, domains, neighbors, h, out, config);
        } else {
            trace!("Detected inconsistency, backtracking...");
            stat!(config.backtracks += 1);
        }
        for d in &mut *domains {
            d.pop_state();
        }

        if status.is_err() {
            break;
        }
    }
    stack.push(x);

    status
}

pub fn debug_print(domains: &Vec<Domain<usize>>) {
    for (i, d) in domains.iter().enumerate() {
        println!("{:?} -> {:?}", i, d.iter().collect::<Vec<_>>());
    }
}
