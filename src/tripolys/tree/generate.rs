use std::sync::Arc;

use crate::tree::{is_core_tree, is_rooted_core_tree, Node};
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
/// E.g. `calculate_addends(6, 3)` yields [[1, 1, 4], [1, 2, 3], [2, 2, 2]].
fn addends(n: usize, k: usize) -> Vec<Vec<usize>> {
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
    /// Number of vertices to start at
    pub start: usize,
    /// Number of vertices to end at (inclusive)
    pub end: usize,
    /// Only generate cores
    pub core: bool,
    /// Record statistics
    pub stats: Option<TreeGenStats>,
    // /// Maximal degree of each node
    // pub max_arity: usize,
    // /// Only enumerate triads
    // pub triad: bool,
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

// pub struct TreeGenerator {
//     rooted_trees: Vec<Vec<Arc<Node>>>,
//     settings: TreeGenConfig,
//     nvertices: usize,
// }

impl TreeGenerator {
    pub fn new(config: TreeGenConfig) -> TreeGenerator {
        assert!(
            config.start != 0,
            "There is no tree with {} nodes",
            config.start
        );

        TreeGenerator {
            rooted_trees: vec![vec![Arc::new(Node::leaf())]],
            nvertices: config.start,
            settings: config,
        }
    }

    /// Returns all unique sets of `k` rooted trees whose number of nodes sum up
    /// to `n`. The trees are sorted by their number of nodes in ascending
    /// order.
    fn rooted_trees(&self, n: usize, k: usize) -> impl Iterator<Item = Vec<Arc<Node>>> + '_ {
        addends(n, k)
            .into_iter()
            .flat_map(|set| {
                set.into_iter()
                    .map(|nvertices| self.rooted_trees[nvertices - 1].iter().cloned())
                    .multi_cartesian_product()
            })
            .filter(|vec| vec.windows(2).all(|w| w[0] <= w[1])) // excludes permutations
    }

    fn generate_rooted_trees(&mut self) {
        for step in self.rooted_trees.len() + 1..self.nvertices {
            let mut trees = Vec::<Vec<Arc<Node>>>::new();
            // let mut rcc_time = time::OffsetDateTime::now_utc();
            let mut num_rcc = 0;

            for arity in 1..self.settings.max_arity {
                let treenagers = self
                    .rooted_trees(step - 1, arity)
                    .par_bridge()
                    .flat_map(|children| connect_by_vertex(&children))
                    .collect::<Vec<_>>();

                num_rcc += treenagers.len();
                // let start = Instant::now();
                let filtered = treenagers
                    .into_par_iter()
                    .filter_map(|child| {
                        if !self.settings.core || is_rooted_core_tree(&child, 0) {
                            Some(Arc::new(child))
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>();

                // rc_time += start.elapsed();
                trees.push(filtered);
            }
            let trees = trees.into_iter().flatten().collect_vec();

            if let Some(mut stats) = self.settings.stats {
                // stats.rcc_time = rcc_time; TODO
                stats.num_rcc = num_rcc;
            }
            self.rooted_trees.push(trees);
        }
    }

    fn generate_trees(&mut self) -> Vec<Node> {
        self.generate_rooted_trees();

        // A tree with centre is a rooted tree where at least two children of the root
        // have height d−1
        let centered = (2..=self.nvertices)
            .flat_map(|arity| {
                self.rooted_trees(self.nvertices - 1, arity)
                    .flat_map(|children| connect_by_vertex(&children))
            })
            .filter(|tree| tree.is_centered());

        // A bicentered tree is formed by taking two rooted trees of equal
        // height and adding an edge between their roots
        let bicentered = self
            .rooted_trees(self.nvertices, 2)
            .filter(|c| c[0].height == c[1].height)
            .flat_map(|v| connect_by_edge(&v[0], &v[1]));

        centered.chain(bicentered).collect()
    }

    pub fn generate(&mut self) -> Vec<Node> {
        if self.nvertices == 1 {
            return vec![Node::leaf()];
        }

        let trees = self.generate_trees();

        let num_cc = trees.len();
        let filtered = trees
            .into_par_iter()
            .filter(|t| !self.settings.core || is_core_tree(t))
            .collect::<Vec<_>>();
        stat!(config.num_cc = num_cc);
        stat!(config.cc_time = cc_time);
        self.nvertices += 1;

        filtered
    }
}

/// Connects two rooted trees by adding an edge between their roots.
/// `child` becomes the rightmost child of `tree`.
///
/// If the two trees happen to be the same, we only add an edge once.
fn connect_by_edge(tree: Arc<Node>, child: Arc<Node>) -> Vec<Node> {
    let connect = |dir| {
        tree.iter()
            .chain(std::iter::once((child.clone(), dir)))
            .collect()
    };

    if *tree == *child {
        [true].iter().map(|&dir| connect(dir)).collect()
    } else {
        [true, false].iter().map(|&dir| connect(dir)).collect()
    }
}

/// Connects an arbitrary number of rooted trees by adding a new vertex that is
/// adjacent to each of their roots.
fn connect_by_vertex(children: impl IntoIterator<Item = Arc<Node>>) -> Vec<Node> {
    (0..children.len())
        .map(|_| [true, false])
        .multi_cartesian_product()
        .map(|edges| children.into_iter().cloned().zip(edges))
        .filter(|v| v.clone().tuple_windows().all(|(a, b)| a <= b)) // excludes permutations
        .map(|t| t.collect())
        .collect()
}

/// Returns all unique sets of `k` rooted trees whose number of nodes sum up
/// to `n`. The trees are sorted by their number of nodes in ascending
/// order.
fn rooted_trees(
    rooted_trees: Vec<Vec<Arc<Node>>>,
    n: usize,
    k: usize,
) -> impl Iterator<Item = Vec<Arc<Node>>> + '_ {
    addends(n, k)
        .into_iter()
        .flat_map(|set| {
            set.into_iter()
                .map(|nvertices| rooted_trees[nvertices - 1].iter().cloned())
                .multi_cartesian_product()
        })
        .filter(|vec| vec.windows(2).all(|w| w[0] <= w[1])) // excludes permutations
}

fn generate_rooted_trees(n: usize, config: &TreeGenConfig) {
    for step in self.rooted_trees.len() + 1..self.nvertices {
        let mut trees = Vec::<Vec<Arc<Node>>>::new();
        // let mut rcc_time = time::OffsetDateTime::now_utc();
        let mut num_rcc = 0;

        for arity in 1..config.max_arity {
            let treenagers = rooted_trees(step - 1, arity)
                .par_bridge()
                .flat_map(|children| connect_by_vertex(&children))
                .collect::<Vec<_>>();

            num_rcc += treenagers.len();
            // let start = Instant::now();
            let filtered = treenagers
                .into_par_iter()
                .filter_map(|child| {
                    if !config.core || is_rooted_core_tree(&child, 0) {
                        Some(Arc::new(child))
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();

            // rc_time += start.elapsed();
            trees.push(filtered);
        }
        let trees = trees.into_iter().flatten().collect_vec();

        stat!(config.num_rcc = num_rcc);
        stat!(config.rcc_time = rcc_time);

        // self.rooted_trees.push(trees);
    }
}

fn generate_trees(n: usize, config: &TreeGenConfig) {
    let rooted_trees = vec![vec![Arc::new(Node::leaf())]];
    self.generate_rooted_trees();

    // A tree with centre is a rooted tree where at least two children of the root
    // have height d−1
    let centered = (2..=self.nvertices)
        .flat_map(|arity| {
            self.rooted_trees(self.nvertices - 1, arity)
                .flat_map(|children| connect_by_vertex(&children))
        })
        .filter(|tree| tree.is_centered());

    // A bicentered tree is formed by taking two rooted trees of equal
    // height and adding an edge between their roots
    let bicentered = self
        .rooted_trees(self.nvertices, 2)
        .filter(|c| c[0].height == c[1].height)
        .flat_map(|v| connect_by_edge(&v[0], &v[1]));

    centered.chain(bicentered).collect()
}

fn connect_by_edge_2(tree: Arc<Node>, child: Arc<Node>, dir: bool) -> Node {
    tree.iter().chain(std::iter::once((child, dir))).collect()
}
