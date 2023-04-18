use std::{sync::Arc, time::Duration};

use crate::tree::{is_core_tree, is_rooted_core_tree, Tree};
use itertools::Itertools;
use rayon::prelude::*;
use serde::{ser::SerializeStruct, Serialize};

/// Returns every set of `k` integers that sum up to `n` sorted in ascending order.
///
/// E.g. `split_into_sums(6, 3)` yields [[1, 1, 4], [1, 2, 3], [2, 2, 2]].
fn split_into_sums(n: usize, k: usize) -> Vec<Vec<usize>> {
    fn inner(pos: usize, left: usize, k: usize, last: usize) -> Vec<Vec<usize>> {
        // Base Case
        if pos == k {
            if left == 0 {
                return vec![vec![]];
            } else {
                return vec![];
            }
        }

        if left == 0 {
            return vec![];
        }

        let mut addends = Vec::new();

        for i in 1..=left {
            if i > last {
                break;
            }
            for mut sub in inner(pos + 1, left - i, k, i) {
                sub.push(i);
                addends.push(sub);
            }
        }

        addends
    }

    inner(0, n, k, n)
}

/// Configuration for tree generation algorithm.
#[derive(Clone, Debug, Default)]
pub struct Config {
    /// Only generate triads
    pub triad: bool,
    /// Only generate cores
    pub core: bool,
}

/// Statistics from the execution of the algorithm
#[derive(Clone, Debug, Default)]
pub struct Stats {
    /// Number of vertices
    pub vertices: u32,
    /// Number of generated (core) trees
    pub num_trees: u32,
    /// Number of AC calls
    pub num_ac_calls: Option<u32>,
    /// Time per AC call (average)
    pub time_ac_call: Option<Duration>,
    /// Time to generate the trees
    pub time_total: Duration,
}

impl Serialize for Stats {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("Stats", 5)?;

        state.serialize_field("vertices", &self.vertices)?;
        state.serialize_field("trees", &self.num_trees)?;
        if let Some(num_ac_calls) = self.num_ac_calls {
            state.serialize_field("ac calls", &num_ac_calls)?;
        } else {
            state.serialize_field("ac calls", "")?;
        }
        if let Some(time_ac_call) = self.time_ac_call {
            state.serialize_field(
                "time per ac call (μs)",
                &format!("{}", time_ac_call.as_micros()),
            )?;
        } else {
            state.serialize_field("time per ac call (μs)", "")?;
        }
        state.serialize_field("total time", &format!("{:.1?}", self.time_total))?;

        state.end()
    }
}

/// Returns all unique sets of `k` children whose number of nodes sum up to `n`.
/// The trees are sorted by their number of nodes in ascending order.
fn collect_children(m: usize, k: usize, rooted_trees: &[Vec<Arc<Tree>>]) -> Vec<Vec<Arc<Tree>>> {
    split_into_sums(m, k)
        .into_iter()
        .flat_map(|sum| {
            sum.into_iter()
                .map(|a| rooted_trees[a].iter().cloned())
                .multi_cartesian_product()
        })
        .filter(|vec| vec.windows(2).all(|w| w[0] <= w[1])) // excludes permutations
        .collect()
}

fn connect(children: Vec<Arc<Tree>>) -> Vec<Tree> {
    (0..children.len())
        .map(|_| [true, false])
        .multi_cartesian_product()
        .map(|edges| children.iter().cloned().zip(edges))
        .filter_map(|v| {
            if v.clone().tuple_windows().all(|(a, b)| a <= b) {
                Some(v.collect())
            } else {
                None
            }
        })
        .collect::<Vec<Tree>>()
}

fn trees(n: usize, rooted_trees: &[Vec<Arc<Tree>>]) -> Vec<Tree> {
    (0..n)
        .flat_map(|k| {
            collect_children(n - 1, k, rooted_trees)
                .into_iter()
                .flat_map(connect)
        })
        .collect()
}

// A triad is an orientation of a tree which has a single vertex of degree
// 3 and otherwise only vertices of degree 2 and 1.
fn generate_triads(n: usize, rooted_trees: &[Vec<Arc<Tree>>]) -> Vec<Tree> {
    collect_children(n - 1, 3, rooted_trees)
        .into_par_iter()
        .flat_map(connect)
        .collect()
}

// A tree with centre is a rooted tree where at least two children of the root
// have height d−1
fn generate_centered_trees(n: usize, rooted_trees: &[Vec<Arc<Tree>>]) -> Vec<Tree> {
    trees(n, rooted_trees)
        .into_par_iter()
        .filter(|t| t.is_centered())
        .collect()
}

// A bicentered tree is formed by taking two rooted trees of equal height and
// adding an edge between their roots
fn generate_bicentered_trees(n: usize, rooted_trees: &[Vec<Arc<Tree>>]) -> Vec<Tree> {
    fn connect(tree: Arc<Tree>, child: Arc<Tree>) -> Vec<Tree> {
        if *tree == *child {
            let mut t1 = (*tree).clone();
            t1.push_child(child, true);
            vec![t1]
        } else {
            let mut t1 = (*tree).clone();
            t1.push_child(child.clone(), true);
            let mut t2 = (*tree).clone();
            t2.push_child(child, false);
            vec![t1, t2]
        }
    }

    collect_children(n, 2, rooted_trees)
        .into_iter()
        .filter(|c| c[0].height == c[1].height)
        .flat_map(|c| connect(c[0].clone(), c[1].clone()))
        .collect()
}

fn generate_rooted_trees(
    n: usize,
    rooted_trees: &mut [Vec<Arc<Tree>>],
    config: &Config,
) -> Vec<Tree> {
    if n == 0 {
        return vec![];
    }
    if n == 1 {
        return vec![Tree::leaf()];
    }

    let mut trees = trees(n, rooted_trees);

    if config.triad {
        trees = trees
            .into_par_iter()
            .filter(|child| child.is_rooted_path())
            .collect();
    }

    if config.core {
        trees = trees
            .into_par_iter()
            .filter(|child| is_rooted_core_tree(child, 0))
            .collect();
    }
    trees
}

/// Generates all trees with n vertices.
///
/// # Arguments
///
/// * n - The number of vertices in the trees to generate.
/// * rooted_trees - A mutable vector of vectors that stores the rooted trees for each size from 0 to n - 1.
/// * config - A reference to a Config struct that determines whether to generate only triads or cores.
/// * stats - A mutable reference to a Stats struct that tracks statistics from the execution of the algorithm.
///
/// # Returns
///
/// A vector of all trees with n vertices.
pub fn generate_trees(
    n: usize,
    rooted_trees: &mut Vec<Vec<Arc<Tree>>>,
    config: &Config,
    stats: &mut Stats,
) -> Vec<Tree> {
    if n == 0 {
        return vec![];
    }
    if n == 1 {
        return vec![Tree::leaf()];
    }

    for i in rooted_trees.len()..n {
        let i_rooted_trees = generate_rooted_trees(i, rooted_trees, config)
            .into_iter()
            .map(Arc::new)
            .collect();

        rooted_trees.push(i_rooted_trees);
    }

    let t_start = std::time::Instant::now();
    let mut trees = if config.triad {
        generate_triads(n, rooted_trees)
    } else {
        let centered = generate_centered_trees(n, rooted_trees);
        let bicentered = generate_bicentered_trees(n, rooted_trees);
        centered.into_iter().chain(bicentered).collect()
    };

    if config.core {
        stats.num_ac_calls = Some(trees.len() as u32);

        let (core_trees, times): (Vec<_>, Vec<_>) = trees
            .into_par_iter()
            .filter_map(|tree| {
                let t_start = std::time::Instant::now();
                let is_core_tree = is_core_tree(&tree);
                let t_end = t_start.elapsed();

                if is_core_tree {
                    Some((tree, t_end))
                } else {
                    None
                }
            })
            .unzip();

        stats.time_ac_call = if times.len() != 0 {
            Some(times.iter().sum::<Duration>() / times.len() as u32)
        } else {
            None
        };
        trees = core_trees;
    }
    let t_end = t_start.elapsed();
    stats.time_total = t_end;
    stats.num_trees = trees.len() as u32;

    trees
}
