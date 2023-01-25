//! A connected, acyclic digraph.
pub mod generate;
mod node;

pub use node::Node;

use crate::{graph::traits::Digraph, solve::Problem};

pub fn is_core_tree<T: Digraph>(t: &T) -> bool {
    let mut problem = Problem::new(t, t);
    problem.make_arc_consistent();

    for d in problem.domains() {
        if d.size() != 1 {
            return false;
        }
    }
    true
}

pub fn is_rooted_core_tree<R: Digraph>(rt: &R, root: usize) -> bool {
    let mut problem = Problem::new(rt, rt);
    problem.set_value(root, root);
    problem.make_arc_consistent();

    for d in problem.domains() {
        if d.size() != 1 {
            return false;
        }
    }
    true
}

// let coloring = move |v: usize| {
//     if v == root {
//         Some(root)
//     } else {
//         None
//     }
// };
