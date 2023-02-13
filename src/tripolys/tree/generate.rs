use std::{sync::Arc, time::Instant};

use crate::tree::{is_core_tree, is_rooted_core_tree, Tree};
use itertools::Itertools;
use rayon::prelude::*;

macro_rules! stat {
    ($c:ident . $field:ident $($t:tt)*) => {
        #[cfg(feature = "stats")]
        {
            if let Some(ref mut st) = $c.stats {
                st . $field $($t)*;
            }
        }
    }
}

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
pub struct TreeGenConfig {
    /// Only generate cores
    pub core: bool,
    /// Record statistics
    pub stats: Option<TreeGenStats>,
}

/// Statistics from the execution of tree generation algorithm.
#[derive(Clone, Debug, Default)]
pub struct TreeGenStats {
    /// Time for rooted core checks
    pub rcc_time: f32,
    /// Number of generated rooted trees
    pub num_rcc: usize,
    /// Time for core checks
    pub cc_time: f32,
    /// Number of generated trees
    pub num_cc: usize,
}

/// Returns all unique sets of `k` children whose number of nodes sum up to `n`.
/// The trees are sorted by their number of nodes in ascending order.
fn collect_children(n: usize, k: usize, rooted_trees: &[Vec<Arc<Tree>>]) -> Vec<Vec<Arc<Tree>>> {
    split_into_sums(n, k)
        .into_iter()
        .flat_map(|sum| {
            sum.into_iter()
                .map(|a| rooted_trees[a].iter().cloned())
                .multi_cartesian_product()
        })
        .filter(|vec| vec.is_sorted()) // excludes permutations
        .collect()
}

fn generate_rooted_trees(
    n: usize,
    rooted_trees: &mut [Vec<Arc<Tree>>],
    config: &TreeGenConfig,
) -> Vec<Tree> {
    if n == 0 {
        return vec![];
    }
    if n == 1 {
        return vec![Tree::leaf()];
    }

    let mut rcc_time = Instant::now();
    // let mut num_rcc = 0;
    let mut trees = trees(n, rooted_trees);
    // num_rcc += trees.len();

    let start = Instant::now();

    if config.core {
        trees = trees
            .into_par_iter()
            .filter(|child| is_rooted_core_tree(child, 0))
            .collect();
    }

    rcc_time += start.elapsed();

    stat!(config.num_rcc = num_rcc);
    stat!(config.rcc_time = rcc_time);
    trees
}

pub fn generate_trees(
    n: usize,
    rooted_trees: &mut Vec<Vec<Arc<Tree>>>,
    config: &TreeGenConfig,
) -> Vec<Tree> {
    if n == 0 {
        return vec![];
    }
    if n == 1 {
        return vec![Tree::leaf()];
    }

    for i in rooted_trees.len()..n {
        let trees = generate_rooted_trees(i, rooted_trees, config)
            .into_iter()
            .map(Arc::new)
            .collect();

        rooted_trees.push(trees);
    }
    let centered = generate_centered_trees(n, rooted_trees);
    let bicentered = generate_bicentered_trees(n, rooted_trees);

    let trees = centered.into_iter().chain(bicentered);

    if config.core {
        trees.par_bridge().filter(is_core_tree).collect()
    } else {
        trees.collect()
    }
}

fn trees(n: usize, rooted_trees: &[Vec<Arc<Tree>>]) -> Vec<Tree> {
    let connect = |children: Vec<Arc<Tree>>| {
        (0..children.len())
            .map(|_| [true, false])
            .multi_cartesian_product()
            .map(|edges| children.iter().cloned().zip(edges))
            .filter(|v| v.clone().is_sorted())
            .map(|t| t.collect())
            .collect::<Vec<_>>()
    };

    (0..n)
        .flat_map(|k| {
            collect_children(n - 1, k, rooted_trees)
                .into_iter()
                .flat_map(connect)
        })
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
    let connect = |tree: Arc<Tree>, child: Arc<Tree>| {
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
    };

    collect_children(n, 2, rooted_trees)
        .into_iter()
        .filter(|c| c[0].height == c[1].height)
        .flat_map(|c| connect(c[0].clone(), c[1].clone()))
        .collect()
}
