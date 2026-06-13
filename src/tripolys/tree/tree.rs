use std::str::FromStr;
use std::sync::Arc;
use std::{cmp::max, ops::Range};

use crate::graph::traits::Digraph;

/// An orientation of a tree defined as a recursive data structure.
///
/// Uses shared pointers to its children, each paired with a direction boolean
/// for the connecting edge. Designed specifically for the orientation
/// generation algorithm.
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
        match self.children.first() {
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

impl Digraph for Tree {
    type Vertex = usize;
    type VertexIter<'a> = Range<usize>;
    type EdgeIter<'a> = EdgeIt<'a>;

    fn vertices(&self) -> Self::VertexIter<'_> {
        0..self.vertex_count()
    }

    fn vertex_count(&self) -> usize {
        self.num_vertices
    }

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
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (tree, rest) = parse_tree(s)?;
        if !rest.is_empty() {
            return Err(format!("unexpected characters: {rest}"));
        }
        Ok(tree)
    }
}

fn parse_tree(s: &str) -> Result<(Tree, &str), String> {
    if s.starts_with('[') {
        let s = &s[1..];
        let (children, s) = parse_children(s)?;
        if !s.starts_with(']') {
            return Err("expected ']'".to_string());
        }
        Ok((children.into_iter().collect(), &s[1..]))
    } else {
        Ok((Tree::leaf(), s))
    }
}

fn parse_children(s: &str) -> Result<(Vec<(Arc<Tree>, bool)>, &str), String> {
    let mut children = Vec::new();
    let mut s = s;

    while !s.starts_with(']') {
        if s.is_empty() {
            return Err("unexpected end of input, expected ']'".to_string());
        }
        let dir = match s.chars().next().unwrap() {
            '0' => false,
            '1' => true,
            c => return Err(format!("expected '0' or '1', got '{c}'")),
        };
        s = &s[1..];
        let (child, rest) = parse_tree(s)?;
        s = rest;
        children.push((Arc::new(child), dir));
    }

    Ok((children, s))
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
    fn test_roundtrip() {
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

        let s = t.to_string();
        let parsed: Tree = s.parse().unwrap();
        assert_eq!(t, parsed);
    }

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
