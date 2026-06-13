use std::{
    fs::{create_dir_all, File},
    io::{BufRead, BufReader, BufWriter, Write},
    path::{Path, PathBuf},
    sync::Arc,
    time::Duration,
};

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
        .into_par_iter()
        .flat_map(|k| {
            collect_children(n - 1, k, rooted_trees)
                .into_par_iter()
                .flat_map(connect)
        })
        .collect()
}

// A triad is an orientation of a tree which has a single vertex of degree
// 3 and otherwise only vertices of degree 2 and 1.
fn triads(n: usize, rooted_trees: &[Vec<Arc<Tree>>]) -> Vec<Tree> {
    collect_children(n - 1, 3, rooted_trees)
        .into_par_iter()
        .flat_map(connect)
        .collect()
}

// A tree with centre is a rooted tree where at least two children of the root
// have height d−1
fn centered_trees(n: usize, rooted_trees: &[Vec<Arc<Tree>>]) -> Vec<Tree> {
    trees(n, rooted_trees)
        .into_par_iter()
        .filter(|t| t.is_centered())
        .collect()
}

// A bicentered tree is formed by taking two rooted trees of equal height and
// adding an edge between their roots
fn bicentered_trees(n: usize, rooted_trees: &[Vec<Arc<Tree>>]) -> Vec<Tree> {
    fn attach_child(tree: Arc<Tree>, child: Arc<Tree>) -> Vec<Tree> {
        let dirs: &[bool] = if *tree == *child {
            &[true]
        } else {
            &[true, false]
        };
        dirs.iter()
            .map(|&dir| {
                let mut t = (*tree).clone();
                t.push_child(child.clone(), dir);
                t
            })
            .collect()
    }

    collect_children(n, 2, rooted_trees)
        .into_par_iter()
        .filter(|c| c[0].height == c[1].height)
        .flat_map(|c| attach_child(c[0].clone(), c[1].clone()))
        .collect()
}

/// Generates orientations of trees incrementally, caching intermediate results.
pub struct TreeGenerator {
    rooted_trees: Vec<Vec<Arc<Tree>>>,
    config: Config,
    data_path: Option<PathBuf>,
}

impl TreeGenerator {
    pub fn new(config: Config) -> Self {
        TreeGenerator {
            rooted_trees: vec![],
            config,
            data_path: None,
        }
    }

    /// Enables persistent caching of rooted trees in `path`.
    pub fn with_cache_dir(mut self, path: PathBuf) -> Self {
        self.data_path = Some(path);
        self
    }

    fn rooted(&self, n: usize) -> Vec<Tree> {
        if n == 0 {
            return vec![];
        }
        if n == 1 {
            return vec![Tree::leaf()];
        }

        let mut trees = trees(n, &self.rooted_trees);

        if self.config.triad {
            trees = trees
                .into_par_iter()
                .filter(|child| child.is_rooted_path())
                .collect();
        }

        if self.config.core {
            trees = trees
                .into_par_iter()
                .filter(|child| is_rooted_core_tree(child, 0))
                .collect();
        }
        trees
    }

    /// Returns all trees with `n` vertices.
    pub fn trees(&mut self, n: usize, stats: &mut Stats) -> Vec<Tree> {
        if n == 0 {
            return vec![];
        }
        if n == 1 {
            return vec![Tree::leaf()];
        }

        for i in self.rooted_trees.len()..n {
            let trees = if let Some(ref data_path) = self.data_path {
                let file = data_path
                    .join(format!("{i:02}"))
                    .join(rooted_file_name(self.config.core, self.config.triad));
                if file.exists() {
                    load_rooted_trees(&file).unwrap_or_else(|e| {
                        eprintln!("warning: could not load {file:?}: {e}");
                        self.rooted(i)
                    })
                } else {
                    let trees = self.rooted(i);
                    if let Some(parent) = file.parent() {
                        let _ = create_dir_all(parent);
                    }
                    if let Err(e) = save_rooted_trees(&trees, &file) {
                        eprintln!("warning: could not save {file:?}: {e}");
                    }
                    trees
                }
            } else {
                self.rooted(i)
            };
            self.rooted_trees.push(trees.into_iter().map(Arc::new).collect());
        }

        let t_start = std::time::Instant::now();
        let mut trees = if self.config.triad {
            triads(n, &self.rooted_trees)
        } else {
            let centered = centered_trees(n, &self.rooted_trees);
            let bicentered = bicentered_trees(n, &self.rooted_trees);
            centered.into_iter().chain(bicentered).collect()
        };

        if self.config.core {
            stats.num_ac_calls = Some(trees.len() as u32);

            let (core_trees, times): (Vec<_>, Vec<_>) = trees
                .into_par_iter()
                .filter_map(|tree| {
                    let t_start = std::time::Instant::now();
                    let is_core = is_core_tree(&tree);
                    let elapsed = t_start.elapsed();
                    if is_core {
                        Some((tree, elapsed))
                    } else {
                        None
                    }
                })
                .unzip();

            stats.time_ac_call = if !times.is_empty() {
                Some(times.iter().sum::<Duration>() / times.len() as u32)
            } else {
                None
            };
            trees = core_trees;
        }

        stats.time_total = t_start.elapsed();
        stats.num_trees = trees.len() as u32;

        trees
    }
}

fn rooted_file_name(core: bool, triad: bool) -> &'static str {
    match (core, triad) {
        (true, true) => "rooted_core_triads.tree",
        (true, false) => "rooted_core_trees.tree",
        (false, true) => "rooted_triads.tree",
        (false, false) => "rooted_trees.tree",
    }
}

fn load_rooted_trees(path: &Path) -> Result<Vec<Tree>, Box<dyn std::error::Error>> {
    let file = File::open(path)?;
    BufReader::new(file)
        .lines()
        .map(|line| Ok(line?.parse::<Tree>()?))
        .collect()
}

fn save_rooted_trees(trees: &[Tree], path: &Path) -> std::io::Result<()> {
    let mut writer = BufWriter::new(File::create(path)?);
    for tree in trees {
        writeln!(writer, "{tree}")?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn counts(config: Config) -> Vec<usize> {
        let mut generator = TreeGenerator::new(config);
        (1..=10)
            .map(|n| {
                let mut stats = Stats::default();
                generator.trees(n, &mut stats).len()
            })
            .collect()
    }

    #[test]
    fn test_trees() {
        assert_eq!(
            counts(Config {
                core: false,
                triad: false
            }),
            [1, 1, 3, 8, 27, 91, 350, 1376, 5743, 24635]
        );
    }

    #[test]
    fn test_core_trees() {
        assert_eq!(
            counts(Config {
                core: true,
                triad: false
            }),
            [1, 1, 1, 1, 1, 2, 3, 7, 15, 36]
        );
    }

    #[test]
    fn test_triads() {
        assert_eq!(
            counts(Config {
                core: false,
                triad: true
            }),
            [1, 0, 0, 4, 12, 44, 132, 376, 1008, 2632]
        );
    }

    #[test]
    fn test_core_triads() {
        assert_eq!(
            counts(Config {
                core: true,
                triad: true
            }),
            [1, 0, 0, 0, 0, 0, 0, 2, 6, 18]
        );
    }
}
