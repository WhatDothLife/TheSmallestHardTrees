//! Data-structure and algorithm for generating trees.

pub mod generate;
mod node;

pub use node::Node;

use crate::{graph::traits::Digraph, csp::Problem};

/// Determines if the given `tree` is a core tree.
///
/// # Examples
///
/// ```
/// use crate::graph::AdjList;
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

    for d in problem.domains() {
        if d.size() != 1 {
            return false;
        }
    }
    true
}

/// Determines if the given `tree` is a rooted core tree with the specified `root` vertex.
///
/// # Examples
///
/// ```
/// use crate::graph::AdjList;
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

    for d in problem.domains() {
        if d.size() != 1 {
            return false;
        }
    }
    true
}
