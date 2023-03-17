use itertools::Itertools;

use std::{
    ops::Neg,
    time::{Duration, Instant},
};

use super::{domain::Domain, problem::*};

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

/// Statistics from the execution of the backtracking search.
#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    /// Number of consistency checks
    pub ccks: u32,
    /// Number of backtracks from dead ends
    pub backtracks: u32,
    /// Number of solutions emitted
    pub solutions: u32,
    /// Number of assignments
    pub assignments: u32,
    /// Duration of the arc-consistency preprocessing
    pub ac3_time: Duration,
    /// Duration of the backtracking
    pub mac3_time: Duration,
}

enum Revision {
    Unchanged,
    Changed,
    Empty,
}

fn revise<C: Constraints>(
    x: Var,
    y: Var,
    domains: &mut Vec<Domain<Value>>,
    constraints: &C,
    mut trail: Option<&mut Vec<Var>>,
    stats: &mut Stats,
) -> Revision {
    let mut revision = Revision::Unchanged;

    for i in (0..domains[x].size()).rev() {
        let mut is_possible = false;

        for &ay in domains[y].iter() {
            let ax = domains[x][i];

            stats.ccks += 1;
            if constraints.check_arc((x, ax), (y, ay)) {
                is_possible = true;
                break;
            }
        }

        if !is_possible {
            if let Some(ref mut trail) = trail {
                if !domains[x].is_modified() {
                    domains[x].save_state();
                    trail.push(x);
                }
            }

            domains[x].swap_remove(i);
            revision = Revision::Changed;

            if domains[x].is_empty() {
                return Revision::Empty;
            }
        }
    }

    revision
}

/// The MAC-3 algorithm due to Mackworth 1977.
pub fn mac_3<C>(
    x: Var,
    domains: &mut Vec<Domain<Value>>,
    constraints: &C,
    trail: &mut Vec<Var>,
    stats: &mut Stats,
) -> bool
where
    C: Constraints,
{
    let mut work_list: Vec<_> = Vec::from_iter(constraints.neighbors(x));

    while let Some((x, y)) = work_list.pop() {
        match revise(x, y, domains, constraints, Some(trail), stats) {
            Revision::Unchanged => {}
            Revision::Changed => work_list.extend(constraints.neighbors(x)),
            Revision::Empty => return false,
        }
    }
    true
}

/// The MAC-3 algorithm due to Mackworth 1977.
pub fn ac_3<C>(domains: &mut Vec<Domain<Value>>, constraints: &C, stats: &mut Stats) -> bool
where
    C: Constraints,
{
    let mut work_list: Vec<_> = Vec::from_iter(constraints.arcs());

    while let Some((x, y)) = work_list.pop() {
        match revise(x, y, domains, constraints, None, stats) {
            Revision::Unchanged => {}
            Revision::Changed => work_list.extend(constraints.neighbors(x)),
            Revision::Empty => return false,
        }
    }
    true
}

pub fn solve<C>(
    domains: &mut Vec<Domain<Value>>,
    constraints: &C,
    stats: &mut Stats,
    out: impl FnMut(Vec<Value>),
    stop_at_first: bool,
) where
    C: Constraints,
{
    trace!("  > Preprocessing with AC-3");
    let t_start = Instant::now();
    ac_3(domains, constraints, stats);
    let t_end = t_start.elapsed();
    stats.ac3_time = t_end;

    trace!("  > Solving with MAC-3");
    let t_start = Instant::now();
    solve_recursive(domains, constraints, stats, out, stop_at_first);
    let t_end = t_start.elapsed();
    stats.mac3_time = t_end;
}

fn solve_recursive<C>(
    domains: &mut Vec<Domain<Value>>,
    constraints: &C,
    stats: &mut Stats,
    mut out: impl FnMut(Vec<Value>),
    stop_at_first: bool,
) where
    C: Constraints,
{
    // Variables wtih smallest remaining values first
    // Order is static during the solving process
    let mut stack: Vec<Var> = (0..domains.len())
        .sorted_by_key(|&x| (domains[x].size() as isize).neg())
        .collect();

    let _ = solve_recursive_inner(
        &mut stack,
        domains,
        constraints,
        stats,
        &mut out,
        stop_at_first,
    );
}

#[derive(Clone, Debug)]
pub(crate) enum SolveError {
    /// Used internally to stop after the first solution (if enabled)
    RequestedStop,
}

fn solve_recursive_inner<C>(
    stack: &mut Vec<Var>,
    domains: &mut Vec<Domain<Value>>,
    constraints: &C,
    stats: &mut Stats,
    out: &mut impl FnMut(Vec<Value>),
    stop_at_first: bool,
) -> Result<(), SolveError>
where
    C: Constraints,
{
    if stack.is_empty() {
        let solution = domains.iter().map(|d| d[0]).collect();
        trace!("==> Valid solution: {:?}", solution);
        stats.solutions += 1;
        out(solution);

        if stop_at_first {
            return Err(SolveError::RequestedStop);
        }
    }

    let mut status = Ok(());
    let x = stack.pop().unwrap();
    trace!("Selected variable = {}", x);

    for i in 0..domains[x].size() {
        trace!("Assignment: {} -> {}", x, domains[x][i]);
        let mut trail = vec![x];
        domains[x].save_state();
        domains[x].assign(i);
        stats.assignments += 1;

        if mac_3(x, domains, constraints, &mut trail, stats) {
            trace!("Propagation successful, recursing...");
            // Repeat the algorithm recursively on the reduced domains
            status = solve_recursive_inner(stack, domains, constraints, stats, out, stop_at_first);
        } else {
            trace!("Detected inconsistency, backtracking...");
            stats.backtracks += 1;
        }
        if status.is_err() {
            break;
        }
        // Backtrack
        for x in trail {
            domains[x].restore_state();
        }
    }
    stack.push(x);

    status
}

fn debug_print(domains: &Vec<Domain<Value>>) {
    for (i, d) in domains.iter().enumerate() {
        println!("{:?} -> {:?}", i, d.iter().collect::<Vec<_>>());
    }
}
