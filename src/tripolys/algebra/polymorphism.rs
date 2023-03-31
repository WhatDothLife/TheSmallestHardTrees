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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::Polymorphism;
    use crate::graph::classes::triad;

    #[test]
    fn test_np_hard() {
        let triad: AdjList<_> = triad("01001111,1010000,011000").unwrap();
        let graph = AdjList::from_edges([
            (1, 0),
            (1, 2),
            (2, 3),
            (4, 3),
            (5, 4),
            (6, 5),
            (7, 0),
            (8, 7),
            (8, 9),
            (9, 10),
            (10, 11),
            (11, 12),
            (13, 0),
            (13, 14),
            (15, 14),
            (15, 18),
            (18, 19),
            (16, 15),
            (17, 16),
        ]);
        let wnu2 = Polymorphism::new(Identities::wnu(2));
        let wnu2_exists = wnu2.exists(&graph) || wnu2.exists(&triad);
        assert!(!wnu2_exists);

        let kmm = Polymorphism::new(Identities::kmm());
        let kmm_exists = kmm.exists(&graph) || kmm.exists(&triad);
        assert!(!kmm_exists);
    }

    #[test]
    fn test_not_solved_by_ac() {
        let graph = AdjList::from_edges([
            (0, 1),
            (1, 2),
            (2, 3),
            (4, 5),
            (5, 6),
            (6, 7),
            (8, 9),
            (9, 10),
            (11, 12),
            (12, 13),
            (13, 14),
            (15, 16),
            (16, 17),
            (17, 18),
            (8, 6),
            (9, 3),
            (15, 9),
            (12, 10),
        ]);
        let majority_exists = Polymorphism::new(Identities::majority()).exists(&graph);
        assert!(majority_exists);

        let wnu2_exists = Polymorphism::new(Identities::wnu(2)).exists(&graph);
        assert!(!wnu2_exists);
    }

    #[test]
    fn test_not_known_to_be_in_nl() {
        let graph = AdjList::from_edges([
            (0, 1),
            (1, 2),
            (2, 3),
            (3, 4),
            (0, 5),
            (5, 6),
            (7, 8),
            (8, 5),
            (8, 9),
            (9, 10),
            (10, 11),
            (12, 13),
            (13, 14),
            (14, 15),
            (13, 6),
        ]);
        let majority = Polymorphism::new(Identities::majority()).exists(&graph);
        assert!(!majority);

        let homck2 = Polymorphism::new(Identities::hobby_mckenzie(2)).exists(&graph);
        assert!(homck2);

        let kk5 = Polymorphism::new(Identities::kearnes_kiss(5)).exists(&graph);
        assert!(kk5);
    }

    // #[test]
    // fn test_nl_hard() {
    //     let graph = AdjList::from_edges([
    //         (0, 1),
    //         (1, 2),
    //         (3, 2),
    //         (3, 4),
    //         (4, 5),
    //         (6, 0),
    //         (6, 7),
    //         (8, 7),
    //         (9, 8),
    //         (8, 10),
    //         (10, 11),
    //     ]);
    //     let hami = Polymorphism::new(Identities::hagemann_mitschke(8)).exists(&graph);
    //     assert!(hami);
    // }
}
