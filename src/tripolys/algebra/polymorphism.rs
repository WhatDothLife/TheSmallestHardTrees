use std::fmt::Debug;
use std::hash::Hash;

use crate::csp::Problem;
use crate::graph::traits::Vertices;
use crate::graph::AdjList;

use super::identities::Identities;
use super::Term;

/// The problem of deciding whether a graph has a given type of polymorphism(s).
#[derive(Clone, Debug)]
pub struct Polymorphism {
    identities: Identities,
    conservative: bool,
    idempotent: bool,
}

impl Polymorphism {
    pub fn new(identities: Identities) -> Polymorphism {
        Polymorphism {
            identities,
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

    pub fn meta_problem<V: Copy + Eq + Hash>(&self, h: &AdjList<V>) -> Problem<Term<V>, V> {
        let indicator = self.identities.indicator_graph(h);
        let mut problem = Problem::new(&indicator, h);

        for v in indicator.vertices() {
            for (term, constant) in &self.identities.non_h1 {
                if let Some(bindings) = term.match_with(&v) {
                    problem.precolor(v.clone(), *bindings.get(constant).unwrap());
                }
            }
        }

        if self.idempotent {
            for (symbol, arity) in &self.identities.ops {
                for i in h.vertices() {
                    let term = Term::new(&symbol, vec![i; *arity]);
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

    pub fn exists<V: Copy + Eq + Hash>(&self, h: &AdjList<V>) -> bool {
        self.meta_problem(h).solution_exists()
    }
}
