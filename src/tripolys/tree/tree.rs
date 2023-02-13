use std::str::FromStr;
use std::sync::Arc;
use std::{cmp::max, ops::Range};

use itertools::Itertools;

use crate::graph::traits::{VertexType, Edges, Vertices};

/// A recursive tree data-structure.
#[derive(Clone, Debug, PartialOrd, PartialEq)]
pub struct Tree {
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

    pub fn push_child(&mut self, child: Arc<Tree>, dir: bool) {
        self.num_vertices += child.num_vertices;
        self.height = max(self.height, child.height + 1);
        self.max_arity = max(self.max_arity, child.children.len() + 1);
        self.children.push((child, dir));
    }

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

fn edges(tree: &Tree) -> Vec<(usize, usize)> {
    fn inner(id: &mut usize, tree: &Tree, edges: &mut Vec<(usize, usize)>) {
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

impl Edges for Tree {
    type EdgeIter<'a> = EdgeIter;

    fn edges(&self) -> Self::EdgeIter<'_> {
        EdgeIter(edges(self).into_iter())
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
