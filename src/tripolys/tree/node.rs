use std::{cmp::max, ops::Range};
use std::str::FromStr;
use std::sync::Arc;

use itertools::Itertools;
// use num_iter::{range, Range};

use crate::graph::traits::{Digraph, Edges, Vertices};

/// A recursive tree data-structure
#[derive(Clone, Debug, PartialOrd, PartialEq)]
pub struct Node {
    pub(crate) num_nodes: usize,
    pub(crate) height: usize,
    pub(crate) max_arity: usize,
    children: Vec<(Arc<Node>, bool)>,
}

impl Node {
    /// Returns a tree with only one node, also referred to as 'leaf'.
    pub const fn leaf() -> Node {
        Node {
            num_nodes: 1,
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

    /// Returns `true` if the tree is a path.
    ///
    /// A path is an orientation of a tree which has only vertices of degree 2
    /// and 1.
    pub const fn is_path(&self) -> bool {
        self.max_arity < 3
    }

    /// Returns `true` if the tree is a triad.
    ///
    /// A triad is an orientation of a tree which has a single vertex of degree
    /// 3 and otherwise only vertices of degree 2 and 1.
    pub fn is_triad(&self) -> bool {
        let mut root_found = false;

        match self.arity() {
            4.. => return false,
            3 => {
                root_found = true;
            }
            _ => {}
        }

        let mut stack = self.children.iter().map(|(t, _)| t.as_ref()).collect_vec();

        while let Some(tree) = stack.pop() {
            match tree.arity() {
                3.. => return false,
                2 => {
                    if root_found {
                        return false;
                    }
                    root_found = true;
                }
                _ => {}
            }
            stack.extend(tree.children.iter().map(|(t, _)| t.as_ref()));
        }
        root_found
    }

    pub fn iter(&self) -> impl Iterator<Item = (Arc<Node>, bool)> + '_ {
        self.children.iter().cloned()
    }
}

impl Vertices for Node {
    type VertexIter = Range<usize>;

    fn vertices(&self) -> Self::VertexIter {
        0..self.vertex_count()
    }

    fn vertex_count(&self) -> usize {
        self.num_nodes
    }

    fn has_vertex(&self, v: usize) -> bool {
        v < self.num_nodes
    }
}

fn edges(tree: &Node) -> Vec<(usize, usize)> {
    fn inner(id: &mut usize, tree: &Node, edges: &mut Vec<(usize, usize)>) {
        let id_parent = *id;

        for (child, dir) in &tree.children {
            *id += 1;

            if *dir {
                edges.push((id_parent, *id));
            } else {
                edges.push((*id, id_parent));
            }
            inner(id, child, edges);
        }
    }

    let mut id = 0;
    let mut edges = Vec::new();
    inner(&mut id, tree, &mut edges);

    edges
}

pub struct EdgeIter(std::vec::IntoIter<(usize, usize)>);

impl Iterator for EdgeIter {
    type Item = (usize, usize);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

impl Edges for Node {
    type EdgeIter = EdgeIter;

    fn edges(&self) -> Self::EdgeIter {
        EdgeIter(edges(self).into_iter())
    }

    fn edge_count(&self) -> usize {
        self.vertex_count() - 1
    }

    fn has_edge(&self, _u: usize, _v: usize) -> bool {
        todo!()
    }
}

impl FromIterator<(Arc<Node>, bool)> for Node {
    fn from_iter<T: IntoIterator<Item = (Arc<Node>, bool)>>(iter: T) -> Node {
        let children = Vec::from_iter(iter);
        let mut num_nodes = 1;
        let mut height = 0;
        let mut max_arity = 0;

        for (child, _) in &children {
            num_nodes += child.num_nodes;
            height = max(height, child.height);
            max_arity = max(max_arity, child.children.len() + 1);
        }

        Node {
            num_nodes,
            height: height + 1,
            max_arity: max(max_arity, children.len()),
            children,
        }
    }
}

impl FromStr for Node {
    type Err = ParseTreeNodeError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut children_stack = Vec::<Vec<(Arc<Node>, bool)>>::new();
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
                                .push((Arc::new(Node::leaf()), dir));
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
                                .push((Arc::new(Node::leaf()), dir));
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
                        .push((Arc::new(Node::from_iter(children)), dir));
                }
                (e, _) => {
                    return Err(ParseTreeNodeError::InvalidCharacter(e));
                }
            }
        }
        if let Some(v) = children_stack.pop() {
            Ok(Node::from_iter(v))
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
            ParseTreeNodeError::InvalidCharacter(c) => write!(f, "Could not parse: {}", c),
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

impl std::fmt::Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();

        for (child, dir) in &self.children {
            let d = if *dir { '1' } else { '0' };
            s.push_str(&format!("{}{}", d, child));
        }
        if self.arity() != 0 {
            s = "[".to_string() + s.as_str() + "]";
        }

        write!(f, "{}", s)
    }
}
