use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::zip;

use indexmap::IndexSet;
use itertools::Itertools;

use crate::csp::Problem;
use crate::graph::traits::{Contract, Edges, Vertices};
use crate::graph::utils::levels;
use crate::graph::AdjList;

use super::identities::Identities;
use super::iteralgebra::IterAlgebra;
use super::Term;

pub trait Vertex: Eq + Copy + Hash + Debug {}

impl<V: Eq + Copy + Hash + Debug> Vertex for V {}

pub fn indicator_graph<V>(graph: &AdjList<V>, condition: &Identities) -> AdjList<Term<V>>
where
    V: Vertex,
{
    let mut ind_edges: Vec<_> = condition
        .operations()
        .into_iter()
        .flat_map(|(symbol, arity)| {
            graph
                .edges()
                .kproduct_tuples(arity)
                .map(move |(u, v)| (Term::new(symbol, u), Term::new(symbol, v)))
        })
        .collect();

    if condition.level_wise() {
        if let Some(lvls) = levels(graph) {
            ind_edges.retain(|(u, _)| {
                u.arguments()
                    .iter()
                    .map(|v| lvls.get(v).unwrap())
                    .all_equal()
            });
        }
    }
    let mut ind_graph = AdjList::from_edges(ind_edges);

    let mut queue: IndexSet<_> = ind_graph.vertices().collect();

    while let Some(u) = queue.pop() {
        let mut queue_u = vec![u.clone()];

        while let Some(x) = queue_u.pop() {
            for v in height1_neighbors(condition, &x, graph.vertices()) {
                if queue.remove(&v) {
                    ind_graph.contract_vertex(u.clone(), v.clone());
                    queue_u.push(v);
                }
            }
        }
    }

    ind_graph
}

fn height1_neighbors<V, I>(condition: &Identities, term: &Term<V>, vertices: I) -> Vec<Term<V>>
where
    I: IntoIterator<Item = V> + Clone,
    I::IntoIter: Clone,
    V: Copy + Eq + Hash,
{
    let mut res = Vec::new();

    for (lhs, rhs) in condition
        .h1_equations()
        .iter()
        .flat_map(|(a, b)| [(a, b), (b, a)])
    {
        if let Some(binding) = lhs.match_with(term) {
            let neighbors = neighbors(rhs.arguments(), binding, vertices.clone())
                .into_iter()
                .map(|arguments| Term::new(rhs.symbol(), arguments));
            res.extend(neighbors);
        }
    }

    res
}

fn neighbors<I, U, V>(args: &[U], bind: HashMap<U, V>, vertices: I) -> Vec<Vec<V>>
where
    I: IntoIterator<Item = V>,
    I::IntoIter: Clone,
    U: Copy + Hash + Eq,
    V: Copy,
{
    let unbound_vars: Vec<_> = args
        .iter()
        .copied()
        .filter(|v| bind.get(v).is_none())
        .unique()
        .collect();

    vertices
        .into_iter()
        .kproduct(unbound_vars.len())
        .map(|vs| {
            let mut bind = bind.clone();
            bind.extend(zip(unbound_vars.clone(), vs));

            args.clone()
                .into_iter()
                .map(|x| *bind.get(&x).unwrap())
                .collect()
        })
        .collect()
}

/// The problem of deciding whether a graph has a given type of polymorphism(s).
#[derive(Clone, Debug)]
pub struct Polymorphism {
    pub(crate) condition: Identities,
    conservative: bool,
    idempotent: bool,
}

impl Polymorphism {
    pub fn new(condition: Identities) -> Polymorphism {
        Polymorphism {
            condition,
            conservative: false,
            idempotent: false,
        }
    }

    pub fn conservative(mut self, flag: bool) -> Self {
        self.conservative = flag;
        self
    }

    pub fn idempotent(mut self, flag: bool) -> Self {
        self.idempotent = flag;
        self
    }

    pub fn meta_problem<V: Vertex>(&self, h: &AdjList<V>) -> Problem<Term<V>, V> {
        let indicator = indicator_graph(h, &self.condition);
        let mut problem = Problem::new(&indicator, h);

        let non_h1_equations = self.condition.non_h1_equations();

        for v in indicator.vertices() {
            for (term, constant) in &non_h1_equations {
                if let Some(bindings) = term.match_with(&v) {
                    problem.precolor(v.clone(), *bindings.get(constant).unwrap());
                }
            }
        }

        if self.idempotent {
            for (symbol, arity) in self.condition.operations() {
                for i in h.vertices() {
                    let term = Term::new(symbol, vec![i; arity]);
                    problem.precolor(term, i);
                }
            }
        }

        if self.conservative {
            for v in indicator.vertices() {
                problem.set_list(v.clone(), v.arguments().to_vec());
            }
        }

        problem
    }
}
