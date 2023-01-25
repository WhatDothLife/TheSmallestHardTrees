use std::{hash::Hash, collections::{HashMap, HashSet}};

/// `AdjMap`<V> is a directed graph datastructure using an adjacency list
/// representation.
///
/// For each vertex the `HashMap` contains an ordered pair, the adjacency
/// lists, where the first entry and second entry contain all successors and
/// predecessors, respectively.
#[derive(Debug, Clone, Default)]
pub struct AdjMap<V> {
    // Vertex -> (Out-Edges, In-Edges)
    lists: HashMap<V, (HashSet<V>, HashSet<V>)>,
    edges: HashSet<(V, V)>,
}

impl<T> AdjMap<T> {
    /// Creates an empty `Graph`.
    pub fn new() -> AdjMap<T> {
        AdjMap {
            lists: HashMap::new(),
            edges: HashSet::new(),
        }
    }

    #[allow(dead_code)]
    pub fn with_capacities(nvertices: usize, nedges: usize) -> AdjMap<T> {
        AdjMap {
            lists: HashMap::with_capacity(nvertices),
            edges: HashSet::with_capacity(nedges),
        }
    }

    /// Returns the number of vertices that are placed in
    /// the graph.
    ///
    /// ## Example
    /// ```rust
    /// use tripolys::digraph::AdjMap;
    ///
    /// let mut graph = AdjMap::<u32>::new();
    ///
    /// graph.add_vertex(1);
    /// graph.add_vertex(2);
    /// graph.add_vertex(3);
    ///
    /// assert_eq!(graph.vertex_count(), 3);
    /// ```
    pub fn vertex_count(&self) -> usize {
        self.lists.len()
    }

    /// Returns an iterator over references to all of the vertices in the graph.
    ///
    /// ## Example
    /// ```rust
    /// use tripolys::digraph::AdjMap;
    ///
    /// let mut graph = AdjMap::<u32>::new();
    /// let mut vertices = vec![];
    ///
    /// graph.add_vertex(0);
    /// graph.add_vertex(1);
    /// graph.add_vertex(2);
    /// graph.add_vertex(3);
    ///
    /// // Iterate over vertices
    /// for v in graph.vertices() {
    ///     vertices.push(v);
    /// }
    ///
    /// assert_eq!(vertices.len(), 4);
    /// ```
    pub fn vertices(&self) -> VertexIter<T> {
        VertexIter(Box::new(self.lists.keys()))
    }

    /// Returns the total number of edges that are listed
    /// in the graph.
    ///
    /// ## Example
    /// ```rust
    /// use tripolys::digraph::AdjMap;
    ///
    /// let mut graph = AdjMap::<u32>::new();
    ///
    /// graph.add_vertex(1);
    /// graph.add_vertex(2);
    /// graph.add_vertex(3);
    /// graph.add_vertex(4);
    ///
    /// graph.add_edge(&1, &2);
    /// graph.add_edge(&2, &3);
    /// graph.add_edge(&3, &4);
    ///
    /// println!("{:?}", graph.edges().collect::<Vec<_>>());
    /// assert_eq!(graph.edge_count(), 3);
    /// ```
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }
}

impl<T: Hash + Eq> AdjMap<T> {
    /// Adds a new vertex to the graph.
    ///
    /// If the graph did not have this vertex present, `true` is returned.
    ///
    /// If the graph did have this vertex present, `false` is returned.
    ///
    /// ## Example
    /// ```rust
    /// use tripolys::digraph::AdjMap;
    ///
    /// let mut graph = AdjMap::<u32>::new();
    ///
    /// assert!(graph.add_vertex(1));
    /// assert!(!graph.add_vertex(1));
    ///
    /// assert_eq!(graph.vertex_count(), 1);
    /// ```
    pub fn add_vertex(&mut self, v: T) -> bool {
        if self.has_vertex(&v) {
            false
        } else {
            self.lists.insert(v, (HashSet::new(), HashSet::new()));
            true
        }
    }

    /// Returns `true` if the graph contains the given vertex, false otherwise.
    ///
    /// ## Example
    /// ```rust
    /// use tripolys::digraph::AdjMap;
    ///
    /// let mut graph = AdjMap::<u32>::new();
    ///
    /// graph.add_vertex(1);
    ///
    /// assert!(graph.has_vertex(&1));
    /// assert!(!graph.has_vertex(&2));
    /// ```
    pub fn has_vertex(&self, v: &T) -> bool {
        self.lists.contains_key(v)
    }

    /// Returns `true` if the graph contains the given edge, false otherwise.
    ///
    /// ## Example
    /// ```rust
    /// use tripolys::digraph::AdjMap;
    ///
    /// let mut graph = AdjMap::<u32>::new();
    ///
    /// graph.add_vertex(1);
    /// graph.add_vertex(2);
    /// graph.add_vertex(3);
    ///
    /// graph.add_edge(&1, &2);
    ///
    /// assert!(graph.has_edge(&1, &2));
    /// assert!(!graph.has_edge(&2, &3));
    /// ```
    pub fn has_edge(&self, u: &T, v: &T) -> bool {
        self.lists.get(u).unwrap().0.contains(v)
    }
}

impl<T: Hash + Eq + Clone> AdjMap<T> {
    /// Removes a vertex from the graph.
    ///
    /// ## Example
    /// ```rust
    /// use tripolys::digraph::AdjMap;
    ///
    /// let mut graph = AdjMap::<u32>::new();
    ///
    /// graph.add_vertex(1);
    /// graph.add_vertex(2);
    /// graph.add_vertex(3);
    ///
    /// // The remove operation is idempotent
    /// graph.remove_vertex(&2);
    /// graph.remove_vertex(&2);
    /// graph.remove_vertex(&2);
    ///
    /// assert_eq!(graph.vertex_count(), 2);
    /// ```
    #[allow(dead_code)]
    pub fn remove_vertex(&mut self, v: &T) {
        if let Some((out_edges, in_edges)) = self.lists.remove(v) {
            // remove vertex from in-edge list of other vertices
            for u in &out_edges {
                self.lists.get_mut(u).unwrap().1.remove(v);
                self.edges.remove(&(v.clone(), u.clone()));
            }

            // remove vertex from out-edge list of other vertices
            for u in &in_edges {
                self.lists.get_mut(u).unwrap().0.remove(v);
                self.edges.remove::<_>(&(u.clone(), v.clone()));
            }
        }
    }

    /// Attempts to place a new edge in the graph.
    ///
    /// If the graph did not have this edge present, `true` is returned.
    ///
    /// If the graph did have this edge present, `false` is returned.
    ///
    ///
    /// ## Example
    /// ```rust
    /// use tripolys::digraph::AdjMap;
    ///
    /// let mut graph = AdjMap::<u32>::new();
    ///
    /// graph.add_vertex(1);
    /// graph.add_vertex(2);
    ///
    /// // Adding an edge is idempotent
    /// assert!(graph.add_edge(&1, &2));
    /// assert!(!graph.add_edge(&1, &2));
    /// ```
    pub fn add_edge(&mut self, u: &T, v: &T) -> bool {
        if self.has_edge(u, v) {
            false
        } else {
            if let Some((out_edges, _)) = self.lists.get_mut(u) {
                out_edges.insert(v.clone());
            } else {
                panic!("Vertex doesn't exist");
            }
            if let Some((_, in_edges)) = self.lists.get_mut(v) {
                in_edges.insert(u.clone());
            } else {
                panic!("Vertex doesn't exist");
            }
            self.edges.insert((u.clone(), v.clone()));
            true
        }
    }

    /// Removes an edge from the graph, returning true if the edge was previously
    /// present, false otherwise.
    ///
    /// ## Example
    /// ```rust
    /// use tripolys::digraph::AdjMap;
    ///
    /// let mut graph = AdjMap::<u32>::new();
    ///
    /// graph.add_vertex(1);
    /// graph.add_vertex(2);
    /// graph.add_vertex(3);
    /// graph.add_vertex(4);
    ///
    /// graph.add_edge(&1, &2);
    /// graph.add_edge(&2, &3);
    /// graph.add_edge(&3, &4);
    ///
    /// assert_eq!(graph.edge_count(), 3);
    ///
    /// // The remove edge operation is idempotent
    /// assert!(graph.remove_edge(&2, &3));
    /// assert!(!graph.remove_edge(&2, &3));
    ///
    /// assert_eq!(graph.edge_count(), 2);
    /// ```
    #[allow(dead_code)]
    pub fn remove_edge(&mut self, u: &T, v: &T) -> bool {
        if self.has_edge(u, v) {
            self.lists.get_mut(u).unwrap().0.remove(v);
            self.lists.get_mut(v).unwrap().1.remove(u);
            self.edges.remove(&(u.clone(), v.clone()));
            true
        } else {
            false
        }
    }

    /// Returns an iterator over all of the edges in the graph.
    ///
    /// ## Example
    /// ```rust
    /// use tripolys::digraph::AdjMap;
    ///
    /// let mut graph = AdjMap::<u32>::new();
    /// let mut edges = vec![];
    ///
    /// graph.add_vertex(1);
    /// graph.add_vertex(2);
    /// graph.add_vertex(3);
    /// graph.add_vertex(4);
    ///
    /// graph.add_edge(&1, &2);
    /// graph.add_edge(&3, &1);
    /// graph.add_edge(&1, &4);
    ///
    /// // Iterate over edges
    /// for v in graph.edges() {
    ///     edges.push(v);
    /// }
    ///
    /// assert_eq!(edges.len(), 3);
    /// ```
    pub fn edges(&self) -> impl Iterator<Item = (T, T)> + '_ {
        self.edges.iter().cloned()
    }

    /// Contracts the vertex `y` with the vertex `x`. The resulting vertex has
    /// id `x`.
    ///
    /// ## Example
    /// ```rust
    /// use tripolys::digraph::AdjMap;
    ///
    /// let mut graph = AdjMap::<u32>::new();
    ///
    /// graph.add_vertex(1);
    /// graph.add_vertex(2);
    /// graph.add_vertex(3);
    /// graph.add_vertex(4);
    ///
    /// graph.add_edge(&1, &2);
    /// graph.add_edge(&2, &3);
    /// graph.add_edge(&1, &4);
    ///
    /// graph.contract_vertices(&2, &4);
    /// graph.contract_vertices(&1, &3);
    ///
    /// // assert_eq!(graph.vertex_count(), 2);
    /// assert_eq!(graph.edge_count(), 2);
    /// ```
    pub fn contract_vertices(&mut self, u: &T, v: &T) -> bool {
        if u == v {
            return true;
        }
        if !self.lists.contains_key(u) || !self.lists.contains_key(v) {
            return false;
        }
        let (o, i) = self.lists.remove(v).unwrap();
        for w in o {
            self.add_edge(u, &w);
            self.lists.get_mut(&w).unwrap().1.remove(v);
            self.edges.remove(&(v.clone(), w.clone()));
        }
        for w in i {
            self.add_edge(&w, u);
            self.lists.get_mut(&w).unwrap().0.remove(v);
            self.edges.remove(&(w.clone(), v.clone()));
        }
        true
    }
}

impl<V: Clone + Hash + Eq> FromIterator<(V, V)> for AdjMap<V> {
    fn from_iter<T: IntoIterator<Item = (V, V)>>(iter: T) -> AdjMap<V> {
        // TODO use with_capacity
        let mut graph = AdjMap::<V>::new();
        for (u, v) in iter {
            graph.add_vertex(u.clone());
            graph.add_vertex(v.clone());
            graph.add_edge(&u, &v);
        }
        graph
    }
}

impl<V: std::fmt::Display + Hash + Eq + Clone> std::fmt::Display for AdjMap<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::from("[");

        for (i, (u, v)) in self.edges().enumerate() {
            if i != 0 {
                s.push(',');
            }
            s.push_str(&format!("({},{})", u, v));
        }
        s.push(']');

        write!(f, "{}", s)
    }
}

pub struct VertexIter<'a, T>(pub(crate) Box<dyn 'a + Iterator<Item = &'a T>>);

impl<'a, T> Iterator for VertexIter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}
