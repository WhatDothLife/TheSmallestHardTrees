//! Data-structure and algorithm for generating trees.

mod generate;
mod tree;

pub use generate::*;
pub use tree::Tree;

use crate::{csp::Problem, graph::traits::Digraph};

/// Determines if the given `tree` is a core tree.
///
/// # Examples
///
/// ```
/// use tripolys::graph::AdjList;
/// use tripolys::tree::is_core_tree;
///
/// let tree = AdjList::from_edges([(0, 1), (1, 2), (2, 3)]);
/// assert!(is_core_tree(&tree));
/// ```
///
/// # Parameters
///
/// - `tree`: A reference to the input graph. It must implement the `Digraph` trait.
///
/// # Returns
///
/// A `bool` value indicating whether the input `tree` is a core tree.
pub fn is_core_tree<T>(tree: &T) -> bool
where
    T: Digraph,
{
    let mut problem = Problem::new(tree, tree);
    problem.make_arc_consistent();

    problem.all_singleton()
}

/// Determines if the given `tree` is a rooted core tree with the specified `root` vertex.
///
/// # Examples
///
/// ```
/// use tripolys::graph::AdjList;
/// use tripolys::tree::is_core_tree;
/// use tripolys::tree::is_rooted_core_tree;
///
/// let tree = AdjList::from_edges([(0, 1), (2, 1), (3, 2)]);
/// assert!(!is_core_tree(&tree));
/// assert!(is_rooted_core_tree(&tree, 0));
/// ```
///
/// # Parameters
///
/// - `tree`: A reference to the input graph. It must implement the `Digraph` trait.
/// - `root`: The root vertex of the tree.
///
/// # Returns
///
/// A `bool` value indicating whether the input `tree` is a rooted core tree
/// with the specified `root` vertex.
pub fn is_rooted_core_tree<T>(tree: &T, root: T::Vertex) -> bool
where
    T: Digraph,
{
    let mut problem = Problem::new(tree, tree);
    problem.set_value(root.clone(), root);
    problem.make_arc_consistent();

    problem.all_singleton()
}
