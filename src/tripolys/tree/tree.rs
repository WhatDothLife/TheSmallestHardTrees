use std::str::FromStr;
use std::sync::Arc;
use std::{cmp::max, ops::Range};

use itertools::Itertools;

use crate::graph::traits::{Edges, VertexType, Vertices};

/// An orientation of a tree defined as a recursive data structure.
///
/// Note that the `Tree` data structure is specifically designed for use with
/// the orientation generation algorithm and may not be suitable for other use
/// cases.
///
/// It uses shared pointers to point to its children. Each shared pointer
/// contains a reference to the child `Tree` object and a boolean flag that
/// determines the direction of the connecting edge.
///
/// Also it implements traits such as `Vertices` and `Edges`, and provides
/// methods such as `max_arity` that return information specific to the graph
/// interpretation of the data structure.
#[derive(Clone, Debug, PartialOrd, PartialEq)]
pub struct Tree {
    /// The total number of vertices in the tree.
    pub(crate) num_vertices: usize,
    pub(crate) height: usize,
    pub(crate) max_arity: usize,
    children: Vec<(Arc<Tree>, bool)>,
}

impl Tree {
    /// Returns a tree with only one node, also referred to as 'leaf'.
    pub const fn leaf() -> Tree {
        Tree {
            num_vertices: 1,
            height: 0,
            max_arity: 0,
            children: Vec::new(),
        }
    }

    /// Returns the number of childern, also referred to as 'arity'.
    pub fn arity(&self) -> usize {
        self.children.len()
    }

    /// Returns `true` if the tree is centered.
    ///
    /// A centered tree is a rooted tree where at least two children of the root
    /// have height d−1.
    pub fn is_centered(&self) -> bool {
        let mut found = false;

        for (child, _) in &self.children {
            if child.height == self.height - 1 {
                if found {
                    return true;
                }
                found = true;
            }
        }
        false
    }

    /// Returns `true` if the tree is a path
    pub fn is_rooted_path(&self) -> bool {
        self.is_path() && self.arity() == 1
    }

    /// Returns `true` if the tree is a path.
    ///
    /// A path is an orientation of a tree which has only vertices of degree 2
    /// and 1.
    pub const fn is_path(&self) -> bool {
        self.max_arity < 3
    }

    /// Adds a child to the current tree.
    ///
    /// This method takes an Arc to a child tree and a direction bool,
    /// indicating the direction of the connecting edge.
    ///
    /// This method updates the properties of the current tree based on the
    /// properties of the added child, such as the total number of vertices in the
    /// tree, the height of the tree, and the maximum arity of the children.
    pub fn push_child(&mut self, child: Arc<Tree>, dir: bool) {
        self.num_vertices += child.num_vertices;
        self.height = max(self.height, child.height + 1);
        self.max_arity = max(self.max_arity, child.children.len() + 1);
        self.children.push((child, dir));
    }

    /// Returns an iterator over the children of the tree.
    ///
    /// The `iter` method returns an iterator that yields tuples of type `(Arc<Tree>, bool)`
    /// representing the children of the tree and their directions.
    pub fn iter(&self) -> impl Iterator<Item = (Arc<Tree>, bool)> + '_ {
        self.children.iter().cloned()
    }
}

impl VertexType for Tree {
    type Vertex = usize;
}

impl Vertices for Tree {
    type VertexIter<'a> = Range<usize>;

    fn vertices(&self) -> Self::VertexIter<'_> {
        0..self.vertex_count()
    }

    fn vertex_count(&self) -> usize {
        self.num_vertices
    }
}

#[derive(Default)]
pub struct EdgeIt<'a> {
    node_index: usize,
    last_index: usize,
    children: &'a [(Arc<Tree>, bool)],
    parent: Option<Box<EdgeIt<'a>>>,
}

impl Iterator for EdgeIt<'_> {
    type Item = (usize, usize);

    fn next(&mut self) -> Option<Self::Item> {
        match self.children.get(0) {
            None => match self.parent.take() {
                Some(mut parent) => {
                    // continue with the parent node
                    parent.last_index = self.last_index;
                    *self = *parent;
                    self.next()
                }
                None => None,
            },
            Some((tree, direction)) => {
                self.children = &self.children[1..];
                let next_index = self.last_index + 1;

                let edge = if *direction {
                    (self.node_index, next_index)
                } else {
                    (next_index, self.node_index)
                };
                // start iterating the child trees
                *self = EdgeIt {
                    children: tree.children.as_slice(),
                    parent: Some(Box::new(std::mem::take(self))),
                    node_index: next_index,
                    last_index: next_index,
                };
                Some(edge)
            }
        }
    }
}

impl Edges for Tree {
    type EdgeIter<'a> = EdgeIt<'a>;

    fn edges(&self) -> Self::EdgeIter<'_> {
        EdgeIt {
            node_index: 0,
            last_index: 0,
            children: &self.children,
            parent: None,
        }
    }

    fn edge_count(&self) -> usize {
        self.vertex_count() - 1
    }
}

impl FromIterator<(Arc<Tree>, bool)> for Tree {
    fn from_iter<T: IntoIterator<Item = (Arc<Tree>, bool)>>(iter: T) -> Tree {
        let mut node = Tree::leaf();
        for (child, dir) in iter {
            node.push_child(child, dir);
        }
        node
    }
}

impl FromStr for Tree {
    type Err = ParseTreeNodeError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut children_stack = Vec::<Vec<(Arc<Tree>, bool)>>::new();
        let mut dir_stack = Vec::new();

        let chars = s.chars().tuple_windows();
        let mut dir = false;

        for (c, d) in chars {
            match (c, d) {
                ('0', e) => {
                    dir = false;
                    match e {
                        '0' | '1' | ']' => {
                            children_stack
                                .last_mut()
                                .unwrap()
                                .push((Arc::new(Tree::leaf()), dir));
                        }
                        _ => {}
                    }
                }
                ('1', e) => {
                    dir = true;
                    match e {
                        '0' | '1' | ']' => {
                            children_stack
                                .last_mut()
                                .unwrap()
                                .push((Arc::new(Tree::leaf()), dir));
                        }
                        _ => {}
                    }
                }
                ('[', _) => {
                    children_stack.push(Vec::new());
                    dir_stack.push(dir);
                }
                (']', _) => {
                    let children = children_stack.pop().unwrap();
                    let dir = dir_stack.pop().unwrap();
                    children_stack
                        .last_mut()
                        .unwrap()
                        .push((Arc::new(Tree::from_iter(children)), dir));
                }
                (e, _) => {
                    return Err(ParseTreeNodeError::InvalidCharacter(e));
                }
            }
        }
        if let Some(v) = children_stack.pop() {
            Ok(Tree::from_iter(v))
        } else {
            Err(ParseTreeNodeError::InvalidCharacter('a'))
        }
    }
}

#[derive(Debug)]
pub enum ParseTreeNodeError {
    InvalidCharacter(char),
    // Delimiter
}

impl std::fmt::Display for ParseTreeNodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            ParseTreeNodeError::InvalidCharacter(c) => write!(f, "Could not parse: {c}"),
        }
    }
}

impl std::error::Error for ParseTreeNodeError {
    fn description(&self) -> &str {
        match self {
            ParseTreeNodeError::InvalidCharacter(_) => "Only 0, 1, [, ] allowed!",
        }
    }
}

impl std::fmt::Display for Tree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();

        for (child, dir) in &self.children {
            let d = if *dir { '1' } else { '0' };
            s.push_str(&format!("{d}{child}"));
        }
        if self.arity() != 0 {
            s = "[".to_string() + s.as_str() + "]";
        }

        write!(f, "{s}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_edges() {
        let t_left = Tree::from_iter([
            (Arc::new(Tree::leaf()), true),
            (Arc::new(Tree::leaf()), true),
            (Arc::new(Tree::leaf()), false),
        ]);
        let t_right = Tree::from_iter([
            (Arc::new(Tree::leaf()), false),
            (Arc::new(Tree::leaf()), true),
            (Arc::new(Tree::leaf()), false),
        ]);
        let t = Tree::from_iter([(Arc::new(t_left), true), (Arc::new(t_right), false)]);
        let t_edges = vec![
            (0, 1),
            (1, 2),
            (1, 3),
            (4, 1),
            (5, 0),
            (6, 5),
            (5, 7),
            (8, 5),
        ];
        assert_eq!(t.edges().collect::<Vec<_>>(), t_edges);
    }
}
