use super::{domain::Domain, problem::*};
use itertools::Itertools;
use std::time::{Duration, Instant};

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

/// The Revision enum is used as a result of the revise routine.
///
/// * `Unchanged` - No domain was changed.
/// * `Changed` - Some domains was changed.
/// * `Empty` - Some domain is empty.
#[derive(Copy, Clone, Debug)]
enum Revision {
    Unchanged,
    Changed,
    Empty,
}

/// Checks the consistency of a constraint satisfaction problem (CSP) by
/// examining a pair of variables. It removes values from the domain of `x`  so
/// that it satisfies the constraints with respect to the other variable.
fn revise<C: Constraints>(
    x: Var,
    y: Var,
    domains: &mut Vec<Domain<Value>>,
    constraints: &C,
    mut trail: Option<&mut Vec<Var>>, // If presents records variables whose domain was changed
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
    solve_iterative(domains, constraints, stats, out, stop_at_first);
    let t_end = t_start.elapsed();
    stats.mac3_time = t_end;
}

fn debug_print(domains: &Vec<Domain<Value>>) {
    for (i, d) in domains.iter().enumerate() {
        println!("{:?} -> {:?}", i, d.iter().collect::<Vec<_>>());
    }
}

fn solve_iterative<C>(
    domains: &mut Vec<Domain<Value>>,
    constraints: &C,
    stats: &mut Stats,
    mut out: impl FnMut(Vec<Value>),
    stop_at_first: bool,
) where
    C: Constraints,
{
    let variables: Vec<Var> = (0..domains.len())
        .sorted_by_key(|&x| domains[x].size())
        .collect();
    let mut assignments = vec![0; domains.len()];
    let mut states: Vec<Vec<Var>> = Vec::new();
    let mut depth = 0;

    loop {
        if depth == variables.len() {
            // We have a solution
            let solution = domains.iter().map(|d| d[0]).collect();
            trace!("==> Valid solution: {:?}", solution);
            stats.solutions += 1;
            out(solution);

            if stop_at_first {
                break;
            }
            depth -= 1;
        }

        let x = variables[depth];
        let a = assignments[depth];

        if a == domains[x].size() {
            trace!("    - Tried every assigment for {}, backtracking...", x);
            if depth == 0 {
                // Search space exhausted
                break;
            }
            let trail = states.pop().unwrap();
            for x in trail {
                domains[x].restore_state();
            }
            assignments[depth] = 0;
            depth -= 1;
            stats.backtracks += 1;
            continue;
        }

        trace!("    - Assignment: {} -> {}", x, a);
        domains[x].save_state();
        domains[x].assign(a);
        stats.assignments += 1;
        assignments[depth] = a + 1;

        let mut trail = vec![x];
        // Propagate the assignment
        if mac_3(x, domains, constraints, &mut trail, stats) {
            trace!("    - Forward check succeeded");
            states.push(trail);
            depth += 1;
        } else {
            trace!("    - Forward check failed");
            for x in trail {
                domains[x].restore_state();
            }
        }
    }
}
