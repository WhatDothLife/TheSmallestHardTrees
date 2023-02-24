use itertools::Itertools;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::str::FromStr;

use crate::csp::Problem;
use crate::graph::classes::directed_path;
use crate::graph::traits::{Contract, Digraph, Edges, Vertices};
use crate::graph::AdjList;

/// Returns `true` if the input graph `g` is balanced, `false` otherwise.
///
/// A digraph is considered balanced if its vertices can be organized into levels
/// such that there exists a function lvl : H → N such that lvl(v) = lvl(u) + 1
/// for all (u, v) ∈ E(H) and the smallest level is 0. The height of a balanced
/// digraph is defined as the maximum level.
///
/// # Examples
///
/// ```
/// use tripolys::graph::AdjList;
/// use tripolys::algebra::is_balanced;
///
/// let mut g = AdjList::from_edges([(0, 1), (1, 2), (2, 3), (1, 4)]);
/// assert!(is_balanced(&g));
/// g.add_edge(0, 2);
/// assert!(!is_balanced(&g));
/// ```
pub fn is_balanced<G>(g: &G) -> bool
where
    G: Digraph,
{
    let h: AdjList<_> = directed_path(g.edge_count());
    Problem::new(g, h).solution_exists()
}

pub fn levels<G>(g: &G) -> Option<HashMap<G::Vertex, usize>>
where
    G: Digraph,
{
    for k in 0..g.edge_count() {
        let h: AdjList<_> = directed_path(k + 1);
        let mut problem = Problem::new(g, h);

        if let Some(sol) = problem.solve_first() {
            let map: HashMap<_, _> = g
                .vertices()
                .map(|v| {
                    let level = sol.value(&v);
                    (v, level)
                })
                .collect();
            return Some(map);
        }
    }
    None
}

type Partition<V> = Vec<Vec<V>>;

impl<V: Clone, I> IterAlgebra<V> for I where I: Iterator<Item = (V, V)> {}

#[doc(hidden)]
pub trait IterAlgebra<V: Clone>: Iterator<Item = (V, V)> {
    fn kproduct(self, k: usize) -> KProduct<V>
    where
        Self: Sized + Clone,
    {
        let mut edges = vec![(vec![], vec![])];

        for _ in 0..k {
            let mut t_edges = Vec::<(Vec<V>, Vec<V>)>::new();
            for (u, v) in edges {
                for (e0, e1) in self.clone() {
                    let mut u_t = u.clone();
                    let mut v_t = v.clone();
                    u_t.push(e0);
                    v_t.push(e1);
                    t_edges.push((u_t, v_t));
                }
            }
            edges = t_edges;
        }
        KProduct(edges.into_iter())
    }
}

#[doc(hidden)]
#[derive(Clone, Debug)]
pub struct KProduct<V>(std::vec::IntoIter<(Vec<V>, Vec<V>)>);

impl<V> Iterator for KProduct<V> {
    type Item = (Vec<V>, Vec<V>);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

/// The problem of deciding whether a graph has a given type of polymorphism(s).
#[derive(Clone, Copy, Debug)]
pub struct MetaProblem {
    condition: Condition,
    level_wise: bool,
    conservative: bool,
    idempotent: bool,
}

impl MetaProblem {
    pub fn new(condition: Condition) -> MetaProblem {
        MetaProblem {
            level_wise: true,
            conservative: false,
            idempotent: false,
            condition,
        }
    }

    pub fn level_wise(mut self, flag: bool) -> Self {
        self.level_wise = flag;
        self
    }

    pub fn conservative(mut self, flag: bool) -> Self {
        self.conservative = flag;
        self
    }

    pub fn idempotent(mut self, flag: bool) -> Self {
        self.idempotent = flag;
        self
    }

    pub fn problem(
        &self,
        template: &AdjList<usize>,
    ) -> Result<Problem<(usize, Vec<usize>), usize>, Error> {
        let indicator = indicator_graph(template, self.condition, self.level_wise)?;

        let mut problem = Problem::new(&indicator, template);

        for v_ind in indicator.vertices() {
            if let Some(u) = precolor(self.condition, &v_ind) {
                problem.set_value(v_ind, u);
            } else if self.conservative {
                problem.set_domain(v_ind.clone(), v_ind.1.clone());
            } else if self.idempotent {
                if v_ind.1.iter().all_equal() {
                    problem.set_value(v_ind.clone(), v_ind.1[0]);
                } else {
                    problem.set_domain(v_ind, template.vertices());
                }
            } else {
                problem.set_domain(v_ind, template.vertices());
            }
        }

        Ok(problem)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Error {
    Unbalanced,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::Unbalanced => write!(f, "The given graph is not balanced"),
        }
    }
}

impl std::error::Error for Error {}

fn indicator_graph(
    template: &AdjList<usize>,
    condition: Condition,
    level_wise: bool,
) -> Result<AdjList<(usize, Vec<usize>)>, Error> {
    let levels = if level_wise {
        levels(template).ok_or(Error::Unbalanced)?
    } else {
        HashMap::new()
    };

    let mut indicator: AdjList<_> = arities(condition)
        .into_iter()
        .enumerate()
        .flat_map(|(i, k)| {
            template
                .edges()
                .kproduct(k)
                .map(move |(u, v)| ((i, u), (i, v)))
        })
        .filter(|((_, u), _)| !level_wise || u.iter().map(|v| levels.get(v).unwrap()).all_equal())
        .collect();

    for class in eq_classes(condition, &template.vertices().collect_vec()) {
        indicator.contract_vertices(class);
    }

    Ok(indicator)
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Condition {
    /// - p(x,y,y) ≈ q(y,x,x) ≈ q(x,x,y)
    /// - p(x,y,x) ≈ q(x,y,x)
    Kmm,
    /// - s(r,a,r,e) ≈ s(a,r,e,a)
    Siggers,
    /// - m(x,x,y) ≈ m(x,y,x) ≈ m(y,x,x) ≈ m(x,x,x) ≈ x
    Majority,
    /// - m(x,x,y) ≈ m(x,y,x) ≈ m(y,x,x) = x
    Nu(usize),
    /// - m(x,x,y) ≈ m(x,y,x) ≈ m(y,x,x)
    Wnu(usize),
    /// - f<sub>0</sub>(x,y,y,z) ≈ x
    /// - f<sub>i</sub>(x,x,y,x) ≈ f<sub>i+1</sub> (x,y,y,x) for all i ∈ {0,…,n−1}
    /// - f<sub>i</sub>(x,x,y,y) ≈ f<sub>i+1</sub> (x,y,y,y) for all i ∈ {0,…,n−1}
    /// - f<sub>n</sub>(x,x,y,z) ≈ z.
    NoName(usize),
    /// - j<sub>1</sub>(x,x,y)    = x
    /// - j<sub>2i−1</sub>(x,y,y) = j<sub>2i</sub>(x,y,y)     for all i ∈ {1,…,n}
    /// - j<sub>i</sub>(x,y,x)    = x                         for all i ∈ {1,…,2n + 1}
    /// - j<sub>2i</sub>(x,x,y)   = j<sub>2i+1</sub>(x,x,y)   for all i ∈ {1,…,n}
    /// - j<sub>2n+1</sub>(x,y,y) = y.
    Jonsson(usize),
    /// - d<sub>0</sub> (x,y,z) ≈ x
    /// - d<sub>i</sub> (x,y,y) ≈ d<sub>i+1</sub>(x,y,y)     for even i ∈ {0,1,…,n−1}
    /// - d<sub>i</sub> (x,y,x) ≈ d<sub>i+1</sub>(x,y,x)     for even i ∈ {0,1,…,n−1}
    /// - d<sub>i</sub> (x,x,y) ≈ d<sub>i+1</sub>(x,x,y)     for odd i ∈ {1, . . . , n − 1}
    /// - d<sub>n</sub> (x,y,z) ≈ z
    KearnesKiss(usize),
    /// - d<sub>0</sub>(x,y,z) = x
    /// - d<sub>i</sub>(x,y,y) = d<sub>i+1</sub>(x,y,y)   for even i < n
    /// - d<sub>i</sub>(x,x,y) = d<sub>i+1</sub>(x,x,y)   for odd i < n
    /// - d<sub>i</sub>(x,y,x) = d<sub>i+1</sub>(x,y,x)   for odd i < n
    /// - d<sub>n</sub>(x,y,y) = p(x,y,y)
    /// - p(x,x,y)             = e<sub>0</sub>(x,x,y)
    /// - e<sub>i</sub>(x,y,y) = e<sub>i+1</sub>(x,y,y)   for even i < n
    /// - e<sub>i</sub>(x,x,y) = e<sub>i+1</sub>(x,x,y)   for odd i < n
    /// - e<sub>i</sub>(x,y,x) = e<sub>i+1</sub>(x,y,x)   for even i < n
    /// - e<sub>n</sub>(x,y,z) = z.
    HobbyMcKenzie(usize),
    /// - p<sub>1</sub>(x,y,y) = x
    /// - p<sub>i</sub>(x,x,y) = p<sub>i+1</sub>(x,y,y) for all i ∈ {1,…,n−1}
    /// - p<sub>n</sub>(x,x,y) = y.
    HagemannMitschke(usize),
    TotallySymmetric(usize),
}

impl FromStr for Condition {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, <Self as FromStr>::Err> {
        match &*s.to_ascii_lowercase() {
            "majority" => Ok(Condition::Majority),
            "siggers" => Ok(Condition::Siggers),
            "kmm" => Ok(Condition::Kmm),
            _ => {
                if let Some((pr, su)) = s.split_once('-') {
                    if let Ok(pr) = pr.parse() {
                        match su {
                            "wnu" => Ok(Condition::Wnu(pr)),
                            "nu" => Ok(Condition::Nu(pr)),
                            "j" => Ok(Condition::Jonsson(pr)),
                            "hm" => Ok(Condition::HagemannMitschke(pr)),
                            "kk" => Ok(Condition::KearnesKiss(pr)),
                            "hmck" => Ok(Condition::HobbyMcKenzie(pr)),
                            "nn" => Ok(Condition::NoName(pr)),
                            "ts" => Ok(Condition::TotallySymmetric(pr)),
                            &_ => Err("unknown Condition, cannot convert from str".to_owned()),
                        }
                    } else {
                        Err("unknown Condition, cannot convert from str".to_owned())
                    }
                } else {
                    Err("unknown Condition, cannot convert from str".to_owned())
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ParseConditionError;

impl std::fmt::Display for ParseConditionError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "No condition registered with that name")
    }
}

impl std::error::Error for ParseConditionError {}

fn arities(condition: Condition) -> Vec<usize> {
    match condition {
        Condition::Kmm => vec![3, 3],
        Condition::Siggers => vec![4],
        Condition::Majority => vec![3],
        Condition::Nu(k) => vec![k],
        Condition::Wnu(k) => vec![k],
        Condition::NoName(n) => vec![4; n],
        Condition::Jonsson(n) => vec![3; n],
        Condition::KearnesKiss(n) => vec![3; n],
        Condition::HobbyMcKenzie(n) => vec![3; n],
        Condition::HagemannMitschke(n) => vec![3; n],
        Condition::TotallySymmetric(n) => vec![n],
    }
}

// Result of pre-processing for WNU/quasi-majority check
enum ElemCount<T: Eq + Clone + Hash> {
    // (x, x, x, y) -> (x, y)
    Once(T, T),
    // (x, x, x) -> (x)
    AllEqual(T),
    // (x, y, z, x, x) -> ()
    None,
}

fn elem_count<T: Eq + Clone + Hash>(x: &[T]) -> ElemCount<T> {
    // (elem, frequency of elem)
    let elem_freq = x.iter().fold(HashMap::<T, usize>::new(), |mut m, y| {
        *m.entry(y.clone()).or_default() += 1;
        m
    });

    match elem_freq.len() {
        1 => ElemCount::AllEqual(elem_freq.keys().next().cloned().unwrap()),
        2 => {
            let mut it = elem_freq.into_iter();
            let (e0, f0) = it.next().unwrap();
            let (e1, f1) = it.next().unwrap();
            if f0 == 1 {
                ElemCount::Once(e1, e0)
            } else if f1 == 1 {
                ElemCount::Once(e0, e1)
            } else {
                ElemCount::None
            }
        }
        _ => ElemCount::None,
    }
}

fn precolor(condition: Condition, (f, v): &(usize, Vec<usize>)) -> Option<usize> {
    match condition {
        Condition::Majority => {
            if v.iter().all_equal() {
                Some(v[0])
            } else {
                None
            }
        }
        Condition::Nu(_) => {
            if let ElemCount::Once(x1, _) = elem_count(v) {
                Some(x1)
            } else {
                None
            }
        }
        Condition::NoName(n) => {
            if *f == 0 && v[1] == v[2] {
                return Some(v[0]);
            }
            if *f == n && v[0] == v[1] {
                return Some(v[3]);
            }
            None
        }
        Condition::HobbyMcKenzie(n) => {
            if *f == 0 {
                return Some(v[0]);
            }
            if *f == (2 * n + 2) {
                return Some(v[2]);
            }
            None
        }
        Condition::HagemannMitschke(n) => {
            if *f == 0 && v[1] == v[2] {
                return Some(v[0]);
            }
            if *f == (n - 1) && v[0] == v[1] {
                return Some(v[2]);
            }
            None
        }
        _ => None,
    }
}

fn eq_classes(condition: Condition, vertices: &[usize]) -> Partition<(usize, Vec<usize>)> {
    match condition {
        Condition::Kmm => {
            let mut partition = Vec::new();

            for &x in vertices {
                for &y in vertices {
                    if x == y {
                        partition.push(vec![(0, vec![x, x, x]), (1, vec![x, x, x])]);
                    }
                    partition.push(vec![
                        (0, vec![x, y, y]),
                        (1, vec![y, x, x]),
                        (1, vec![x, x, y]),
                    ]);
                    partition.push(vec![(0, vec![x, y, x]), (1, vec![x, y, x])]);
                }
            }

            partition
        }
        Condition::Siggers => {
            let mut vec = Vec::new();

            for &x in vertices {
                for &y in vertices {
                    for &z in vertices {
                        if x != y || y != z {
                            if y == z {
                                vec.push(vec![
                                    (0, vec![x, y, z, x]),
                                    (0, vec![y, x, y, z]),
                                    (0, vec![x, z, x, y]),
                                ]);
                            } else if x != z {
                                vec.push(vec![(0, vec![x, y, z, x]), (0, vec![y, x, y, z])]);
                            }
                        }
                    }
                }
            }
            vec
        }
        Condition::Majority => majority_eq_classes(vertices),
        Condition::Nu(arity) => nu_eq_classes(vertices, arity),
        Condition::Wnu(arity) => wnu_eq_classes(vertices, arity),
        Condition::NoName(length) => {
            let mut partition = Vec::new();

            for &x in vertices {
                for &y in vertices {
                    for i in 0..length {
                        partition.push(vec![(i, vec![x, x, y, x]), (i + 1, vec![x, y, y, x])]);
                        partition.push(vec![(i, vec![x, x, y, y]), (i + 1, vec![x, y, y, y])]);
                    }
                }
            }

            partition
        }
        Condition::Jonsson(length) => {
            let mut partition = Vec::new();

            for &x in vertices {
                let mut id = (0..=(2 * length)).map(|i| (i, vec![x, x, x])).collect_vec();

                for &y in vertices {
                    if x == y {
                        continue;
                    }
                    for i in 0..length {
                        partition.push(vec![(2 * i, vec![x, y, y]), (2 * i + 1, vec![x, y, y])]);
                        partition
                            .push(vec![(2 * i + 1, vec![x, x, y]), (2 * i + 2, vec![x, x, y])]);
                    }
                    for i in 0..=(2 * length) {
                        id.push((i, vec![x, y, x]));
                    }
                    partition.push(vec![(0, vec![x, x, x]), (0, vec![x, x, y])]);
                    partition.push(vec![
                        (2 * length, vec![y, y, y]),
                        (2 * length, vec![x, y, y]),
                    ]);
                }
                partition.push(id);
            }

            partition
        }
        Condition::KearnesKiss(length) => {
            let mut partition = Vec::new();

            for &x in vertices {
                let mut id = (0..=length).map(|i| (i, vec![x, x, x])).collect_vec();

                for &y in vertices {
                    for i in (0..length).step_by(2) {
                        partition.push(vec![(i, vec![x, y, y]), (i + 1, vec![x, y, y])]);
                        partition.push(vec![(i, vec![x, y, x]), (i + 1, vec![x, y, x])]);
                    }
                    for i in (0..length).skip(1).step_by(2) {
                        partition.push(vec![(i, vec![x, x, y]), (i + 1, vec![x, x, y])]);
                    }
                    for &z in vertices {
                        id.push((0, vec![x, y, z]));
                        id.push((length, vec![y, z, x]));
                    }
                }
                partition.push(id);
            }

            partition
        }
        Condition::HobbyMcKenzie(n) => {
            let mut partition = Vec::new();

            for &x in vertices {
                partition.push((0..(2 * n + 3)).map(|i| (i, vec![x, x, x])).collect_vec());

                for &y in vertices {
                    if x == y {
                        continue;
                    }
                    partition.push(vec![(n, vec![x, y, y]), (n + 1, vec![x, y, y])]);
                    partition.push(vec![(n + 1, vec![x, x, y]), (n + 2, vec![x, x, y])]);

                    for j in (0..n).step_by(2) {
                        partition.push(vec![(j, vec![x, y, y]), (j + 1, vec![x, y, y])]);
                        partition
                            .push(vec![(j + n + 2, vec![x, y, y]), (j + n + 3, vec![x, y, y])]);
                        partition
                            .push(vec![(j + n + 2, vec![x, y, x]), (j + n + 3, vec![x, y, x])]);
                    }
                    for j in (0..n).skip(1).step_by(2) {
                        partition.push(vec![(j, vec![x, x, y]), (j + 1, vec![x, x, y])]);
                        partition.push(vec![(j, vec![x, y, x]), (j + 1, vec![x, y, x])]);
                        partition
                            .push(vec![(j + n + 2, vec![x, x, y]), (j + n + 3, vec![x, x, y])]);
                    }
                }
            }

            partition
        }
        Condition::HagemannMitschke(n) => {
            let mut partition = Vec::new();

            for &x in vertices {
                for &y in vertices {
                    for i in 0..n {
                        partition.push(vec![(i, vec![x, x, y]), (i + 1, vec![x, y, y])]);
                    }
                }
            }

            partition
        }
        Condition::TotallySymmetric(n) => ts_eq_classes(n, vertices),
    }
}

fn wnu_eq_classes(g: &[usize], k: usize) -> Partition<(usize, Vec<usize>)> {
    nu_eq_class_helper(k, g, true)
}

fn nu_eq_classes(g: &[usize], k: usize) -> Partition<(usize, Vec<usize>)> {
    nu_eq_class_helper(k, g, false)
}

fn majority_eq_classes(g: &[usize]) -> Partition<(usize, Vec<usize>)> {
    nu_eq_class_helper(3, g, true)
}

fn nu_eq_class_helper(arity: usize, g: &[usize], weak: bool) -> Partition<(usize, Vec<usize>)> {
    let mut partition = Vec::new();

    for &v in g {
        let mut vec = Vec::new();

        for &w in g {
            if v == w {
                continue;
            }
            let mut eq_class = Vec::new();

            for k in 0..arity {
                let mut tuple = (0, vec![v; arity]);
                tuple.1[k] = w;
                eq_class.push(tuple);
            }
            if weak {
                partition.push(eq_class);
            } else {
                vec.push(eq_class);
            }
        }
        if !weak {
            partition.push(vec.into_iter().flatten().collect_vec());
        }
    }

    partition
}

fn ts_eq_classes(arity: usize, g: &[usize]) -> Vec<Vec<(usize, Vec<usize>)>> {
    fn generate(k: usize, elements: Vec<usize>) -> Vec<(usize, Vec<usize>)> {
        (0..k)
            .map(|_| elements.clone())
            .multi_cartesian_product()
            .filter(|v| v.iter().unique().count() == elements.len())
            .map(|v| (0, v))
            .collect()
    }
    let mut partition = Vec::new();

    for i in 2..=arity {
        for c in g.iter().copied().combinations(i) {
            partition.push(generate(arity, c));
        }
    }

    partition
}
