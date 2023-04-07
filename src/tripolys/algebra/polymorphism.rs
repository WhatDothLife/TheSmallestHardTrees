use super::iteralgebra::IterAlgebra;
use super::levels;
use super::term::Term;

use crate::csp::Problem;
use crate::graph::traits::{Edges, Vertices};
use crate::graph::AdjList;

use indexmap::IndexSet;
use itertools::{chain, Itertools};
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::zip;
use std::str::FromStr;

/// Operations D<sup>3</sup> → D that must satisfy a system of linear identities.
#[derive(Clone, Debug, PartialEq)]
pub struct Polymorphisms {
    // Operation symbols and their arity
    ops: Vec<(String, usize)>,
    // Equations of the form f(x...z)=d
    non_h1: Vec<(Term<char>, char)>,
    // Equations of the form f(x...z)=f(a...c)
    h1: Vec<(Term<char>, Term<char>)>,
    // Whether the identities can be satisfied level-wise
    level_wise: bool,
    // Whether the polymorphisms must be conservative
    conservative: bool,
}

#[derive(Debug, PartialEq)]
pub enum ParseError {
    EmptyString,
    MalformedEquation,
    AmbiguousArity(String),
    UnboundConstant(char),
    OneElementStructure(char, char),
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::EmptyString => write!(f, "String is empty"),
            ParseError::MalformedEquation => write!(f, "Failed to parse identities"),
            ParseError::AmbiguousArity(symbol) => write!(f, "{} has ambiguous arity", symbol),
            ParseError::UnboundConstant(c) => write!(f, "Constant {} is not bound by term", c),
            ParseError::OneElementStructure(c, d) => {
                write!(f, "{} = {} only satisfied for one element structures", c, d)
            }
        }
    }
}

impl std::error::Error for ParseError {}

fn parse(s: &str) -> Result<Polymorphisms, ParseError> {
    let trimmed = s.trim();
    if trimmed.is_empty() {
        return Err(ParseError::EmptyString);
    }
    let mut operations = HashMap::new();
    let mut non_h1 = Vec::new();
    let mut h1: Vec<(Term<char>, Term<char>)> = Vec::new();

    for eq_str in trimmed.split([',', '\n']).filter(|x| !x.is_empty()) {
        let mut constant = None;
        let mut terms = Vec::new();

        for st in eq_str.split('=') {
            if let Ok(term) = Term::from_str(st) {
                if let Some(k) = operations.get(term.symbol()) {
                    if *k != term.arity() {
                        return Err(ParseError::AmbiguousArity(term.symbol().into()));
                    }
                } else {
                    operations.insert(term.symbol().to_owned(), term.arity());
                }
                terms.push(term);
            } else if let Some(c) = st.trim().chars().next() {
                if let Some(d) = constant {
                    return Err(ParseError::OneElementStructure(c, d));
                }
                constant = Some(c);
            } else {
                return Err(ParseError::MalformedEquation);
            }
        }
        if terms.len() == 0 {
            return Err(ParseError::MalformedEquation);
        }
        if constant.is_none() && terms.len() == 1 {
            return Err(ParseError::MalformedEquation);
        }

        if let Some(c) = constant {
            for term in &terms {
                if !term.args().contains(&c) {
                    return Err(ParseError::UnboundConstant(c));
                }
                non_h1.push((term.clone(), c));
            }
        }
        if terms.len() > 1 {
            h1.extend(terms.into_iter().tuple_combinations());
        }
    }

    let per_identity = h1
        .iter()
        .all(|(lhs, rhs)| lhs.arg_count() == 2 && rhs.arg_count() == 2);
    let total = h1
        .iter()
        .flat_map(|(lhs, rhs)| chain(lhs.args(), rhs.args()))
        .unique()
        .count()
        == 2;

    Ok(Polymorphisms {
        ops: operations.into_iter().collect(),
        non_h1,
        h1,
        level_wise: total && per_identity,
        conservative: false,
    })
}

macro_rules! condition {
    ($name:ident, $($eq:expr),+ $(,)?) => {
        #[doc = concat!($(concat!("- ", $eq, "\n")),+)]
        pub fn $name() -> Polymorphisms {
            let equation = concat!($($eq, ",",)+);
            Polymorphisms::parse(equation).unwrap()
        }
    };
}

impl Polymorphisms {
    /// Parses a system of linear identities from a string that the
    /// polymorphisms must satisfy.
    ///
    /// The input string should contain a list of linear identities separated by
    /// commas or newlines. The terms that are not constants are of the form
    /// `f(v1...vn)`, where `v1`, `v2`, ..., `vn`, are variables. Note, that
    /// they're not separated by commas because of brevity. Variables can be any
    /// non-empty sequence of characters that does not contain the `(`, `)`,
    /// `=`, or `,` characters.
    ///
    /// # Example
    ///
    /// ```
    /// use tripolys::graph::AdjList;
    /// use tripolys::graph::classes::triad;
    /// use tripolys::algebra::Polymorphisms;
    ///
    /// let kmm = "p(xyy)=q(yxx)=q(xxy), p(xyx)=q(xyx)";
    ///
    /// let triad: AdjList<_> = triad("0,0,0").unwrap();
    /// let exists = Polymorphisms::parse(kmm).unwrap().exist(&triad);
    ///
    /// assert!(exists);
    /// ```
    pub fn parse(s: &str) -> Result<Self, ParseError> {
        parse(s)
    }

    condition!(siggers, "s(area)=s(rare)");
    condition!(kmm, "p(xyy)=q(yxx)=q(xxy)", "p(xyx)=q(xyx)");
    condition!(majority, "m(xxy)=m(xyx)=m(yxx)=m(xxx)=x");
    condition!(minority, "m(yyy)=m(xxy)=m(xyx)=m(yxx)=y");
    condition!(maltsev, "f(xxy)=f(yxx)=y");
    condition!(fs3, "f(xyz)=f(zxy)=f(yxz)");
    condition!(edge4, "f(yyxx)=f(yxyx)=f(xxxx)=f(xxxy)");
    condition!(edge5, "f(yyxxx)=f(yxyxx)=f(xxxxx)=f(xxxyx)=f(xxxxy)");
    condition!(symmetric_majority, "t(xyz)=t(yxz)=t(yzx)", "t(xxy)=t(xxx)");
    condition!(g2, "f(aaxy)=f(bbxy)=f(xaay)=f(yaxa)");
    condition!(g3, "f(aaxyz)=f(bbxyz)=f(xaayz)=f(yaxaz)=f(zaxya)");
    condition!(gs3, "f(xxxx)=f(xxxy)", "f((123x)=f(231x)");
    condition!(
        wnu3_4,
        "g(xxy)=g(xyx)=g(yxx)",
        "f(xxxy)=f(xxyx)=f(xyxx)=f(yxxx)",
        "g(yxx)=f(yxxx)"
    );
    condition!(
        hm2maj,
        "p(yyx)=p(xxx)",
        "p(xyy)=q(xxy)",
        "q(xyy)=q(xxx)",
        "p(xyx)=p(xxx)=q(xyx)"
    );
    condition!(
        pix2,
        "p(xyy)=p(xxx)=p(xyx),p(xxy)=q(xyy)",
        "q(yxy)=q(xxy)=q(yyy)"
    );

    /// f (y,x,x,…,x,x) = f (x,y,x,…,x,x) = … = f (x,x,x,…,x,y)
    pub fn wnu(k: u32) -> Polymorphisms {
        Polymorphisms::parse(&weak_near_unamity(k)).unwrap()
    }

    /// f (y,x,x,…,x,x) = f (x,y,x,…,x,x) = … = f (x,x,x,…,x,y) = x
    pub fn nu(k: u32) -> Polymorphisms {
        Polymorphisms::parse(&near_unamity(k)).unwrap()
    }

    /// f(x1,x2,…,xk) = f(x2,…,xk,x1)
    pub fn sigma(k: u32) -> Polymorphisms {
        Polymorphisms::parse(&sigma(k)).unwrap()
    }

    /// - p<sub>1</sub>(x,y,y) = x
    /// - p<sub>i</sub>(x,x,y) = p<sub>i+1</sub>(x,y,y) for all i ∈ {1,…,n−1}
    /// - p<sub>n</sub>(x,x,y) = y.
    pub fn hagemann_mitschke(n: u32) -> Polymorphisms {
        Polymorphisms::parse(&hagemann_mitschke_chain(n)).unwrap()
    }

    /// - d<sub>0</sub> (x,y,z) ≈ x
    /// - d<sub>i</sub> (x,y,y) ≈ d<sub>i+1</sub>(x,y,y)     for even i ∈ {0,1,…,n−1}
    /// - d<sub>i</sub> (x,y,x) ≈ d<sub>i+1</sub>(x,y,x)     for even i ∈ {0,1,…,n−1}
    /// - d<sub>i</sub> (x,x,y) ≈ d<sub>i+1</sub>(x,x,y)     for odd i ∈ {1,…, n − 1}
    /// - d<sub>n</sub> (x,y,z) ≈ z
    pub fn kearnes_kiss(n: u32) -> Polymorphisms {
        Polymorphisms::parse(&kearnes_kiss_chain(n)).unwrap()
    }

    /// - f<sub>0</sub>(x,y,y,z) ≈ x
    /// - f<sub>i</sub>(x,x,y,x) ≈ f<sub>i+1</sub> (x,y,y,x) for all i ∈ {0,…,n−1}
    /// - f<sub>i</sub>(x,x,y,y) ≈ f<sub>i+1</sub> (x,y,y,y) for all i ∈ {0,…,n−1}
    /// - f<sub>n</sub>(x,x,y,z) ≈ z.
    pub fn no_name(n: u32) -> Polymorphisms {
        Polymorphisms::parse(&no_name_chain(n)).unwrap()
    }

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
    pub fn hobby_mckenzie(n: u32) -> Polymorphisms {
        Polymorphisms::parse(&hobby_mckenzie(n)).unwrap()
    }

    /// - j<sub>1</sub>(x,x,y)    = x
    /// - j<sub>2i−1</sub>(x,y,y) = j<sub>2i</sub>(x,y,y)     for all i ∈ {1,…,n}
    /// - j<sub>i</sub>(x,y,x)    = x                         for all i ∈ {1,…,2n + 1}
    /// - j<sub>2i</sub>(x,x,y)   = j<sub>2i+1</sub>(x,x,y)   for all i ∈ {1,…,n}
    /// - j<sub>2n+1</sub>(x,y,y) = y.
    pub fn jonsson(n: u32) -> Polymorphisms {
        Polymorphisms::parse(&jonsson_chain(n)).unwrap()
    }

    /// f(x<sub>1</sub>,x<sub>2</sub>,…,x<sub>n</sub>) = f(y<sub>1</sub>,y<sub>2</sub>,…,y<sub>n</sub>)
    /// where {y<sub>1</sub>,y<sub>2</sub>,…,y<sub>n</sub>} = {x<sub>1</sub>,x<sub>2</sub>,…,x<sub>n</sub>}
    pub fn totally_symmetric(k: u32) -> Polymorphisms {
        let mut ids = Polymorphisms::parse(&totally_symmetric(k)).unwrap();
        // NOTE: So far there is no characterization of linear identities that
        // can be satisfied level-wise. While parsing we only check for the case
        // where a h1-condition in two variables has both these variables appear
        // on each side in every identity. However, totally symmetric can also
        // be satisfied level-wise for any k.
        ids.level_wise = true;
        ids
    }

    /// f(a<sub>1</sub>,…,a<sub>n</sub>) ∈ {a<sub>1</sub>,…,a<sub>n</sub>} for all a<sub>i</sub> ∈ D
    pub fn conservative(mut self, flag: bool) -> Self {
        self.conservative = flag;
        self
    }

    /// f(a,a,…,a) = a
    ///
    /// # Examples
    ///
    /// ```
    /// use tripolys::graph::AdjList;
    /// use tripolys::graph::classes::triad;
    /// use tripolys::algebra::Polymorphisms;
    ///
    /// let triad: AdjList<_> = triad("01001111,101000,011000").unwrap();
    /// let exists = Polymorphisms::wnu(3)
    ///     .idempotent(true)
    ///     .exist(&triad);
    ///
    /// assert!(!exists);
    /// ```
    pub fn idempotent(mut self, flag: bool) -> Self {
        if flag {
            for (symbol, arity) in &self.ops {
                self.non_h1
                    .push((Term::new(symbol, (0..*arity).map(|_| 'x')), 'x'));
            }
        }
        self
    }

    /// Computes the indicator graph H<sup>Ind</sup> of `graph`.
    ///
    /// # Examples
    ///
    /// ```
    /// use tripolys::graph::AdjList;
    /// use tripolys::graph::classes::triad;
    /// use tripolys::algebra::Polymorphisms;
    /// use tripolys::csp::Problem;
    ///
    /// let triad: AdjList<_> = triad("01001111,1010000,011000").unwrap();
    /// let mut ind_graph = Polymorphisms::wnu(2).indicator_graph(&triad);
    ///
    /// assert!(!Problem::new(&ind_graph, &triad).solution_exists());
    /// ```
    ///
    /// # Note
    ///
    /// The size of the indicator digraph grows exponentially with the
    /// arity of the function symbols in the condition and linearly with
    /// number of function symbols.
    pub fn indicator_graph<V: Copy + Eq + Hash>(&self, h: &AdjList<V>) -> AdjList<Term<V>> {
        // Construct for each function symbol the categorical power of H of
        // the corresponding arity, and take their disjoint union.
        let mut ind_edges: Vec<_> = self
            .ops
            .iter()
            .flat_map(|(symbol, arity)| {
                h.edges()
                    .kproduct_tuples(*arity)
                    .map(move |(u, v)| (Term::new(symbol, u), Term::new(symbol, v)))
            })
            .collect();

        if self.level_wise {
            // For every function symbol (say of arity k) we construct only the
            // subgraph of H^k consisting of all same-level k-tuples
            // (i.e., tuples in which all vertices are from the same level).
            if let Some(lvls) = levels(h) {
                ind_edges
                    .retain(|(u, _)| u.args().iter().map(|v| lvls.get(v).unwrap()).all_equal());
            }
        }
        let mut ind_graph = AdjList::from_edges(ind_edges);

        // Identify vertices that need to be inditified as dictated by the
        // h1-identities
        let mut unprocessed: IndexSet<_> = ind_graph.vertices().collect();
        let mut contracted = Vec::new();

        while let Some(u) = unprocessed.pop() {
            contracted.push(u.clone());

            while let Some(v) = contracted.pop() {
                for (lhs, rhs) in self.h1.iter().flat_map(|(a, b)| [(a, b), (b, a)]) {
                    if let Some(binding) = lhs.match_with(&v) {
                        let unbound_vars: Vec<_> = rhs
                            .args()
                            .iter()
                            .copied()
                            .filter(|v| binding.get(v).is_none())
                            .unique()
                            .collect();

                        for values in h.vertices().kproduct(unbound_vars.len()) {
                            let mut binding = binding.clone();
                            binding.extend(zip(unbound_vars.clone(), values));
                            let mapped = rhs.map(|x| *binding.get(&x).unwrap());

                            if unprocessed.remove(&mapped) {
                                ind_graph.contract_vertex(&u, &mapped);
                                contracted.push(mapped);
                            }
                        }
                    }
                }
            }
        }

        ind_graph
    }

    /// Obtains an instance of the graph homomorphism problem from the indicator
    /// graph of `h` to `h`.
    ///
    /// # Examples
    ///
    /// ```
    /// use tripolys::graph::AdjList;
    /// use tripolys::graph::classes::triad;
    /// use tripolys::algebra::Polymorphisms;
    ///
    /// let triad: AdjList<_> = triad("01001111,1010000,011000").unwrap();
    /// let mut problem = Polymorphisms::wnu(2).problem(&triad);
    ///
    /// assert!(!problem.solution_exists());
    /// ```
    pub fn problem<V: Copy + Eq + Hash>(&self, h: &AdjList<V>) -> Problem<Term<V>, V> {
        let indicator = self.indicator_graph(h);
        let mut problem = Problem::new(&indicator, h);

        // For every identity that is not height-one, find every vertex of H^Ind
        // that comes from a tuple of vertices of H matching the left-hand side
        // and set its value to the vertex of H given by the right-hand side.
        for v in indicator.vertices() {
            for (term, constant) in &self.non_h1 {
                if let Some(bindings) = term.match_with(&v) {
                    problem.precolor(v.clone(), *bindings.get(constant).unwrap());
                }
            }
        }

        if self.conservative {
            for v in indicator.vertices() {
                problem.set_list(v.clone(), v.args().to_vec());
            }
        }

        problem
    }

    /// Check if polymorphisms exist for the given graph `h` that satisfy the
    /// identity.
    ///
    /// # Examples
    ///
    /// ```
    /// use tripolys::graph::AdjList;
    /// use tripolys::graph::classes::triad;
    /// use tripolys::algebra::Polymorphisms;
    ///
    /// let triad: AdjList<_> = triad("01001111,1010000,011000").unwrap();
    /// let exists = Polymorphisms::wnu(2).exist(&triad);
    ///
    /// assert!(!exists);
    /// ```
    pub fn exist<V: Copy + Eq + Hash>(&self, h: &AdjList<V>) -> bool {
        self.problem(h).solution_exists()
    }

    pub fn find_all<V: Copy + Eq + Hash>(&self, h: &AdjList<V>) -> Vec<HashMap<Term<V>, V>> {
        self.problem(h).solve_all()
    }
}

fn hagemann_mitschke_chain(n: u32) -> String {
    assert!(n > 0, "Hagemann-Mitschke is only defined for n > 0");

    let mut result = String::from("p1(xyy)=x\n");

    for i in 1..n {
        result.push_str(&format!("p{}(xxy)=p{}(xyy)\n", i, i + 1));
    }
    result.push_str(&format!("p{n}(xxy)=y"));

    result
}

fn hobby_mckenzie(n: u32) -> String {
    // d0(x,y,z) = x
    let mut result = String::from("d(xyz)=x\n");

    for i in (0..n).step_by(2) {
        // d_i(x,y,y) = d_{i+1}(x,y,y) for even i < n
        result.push_str(&format!("d{}(xyy)=d{}(xyy)\n", i, i + 1));
    }

    for i in (1..n).step_by(2) {
        // d_i(x,x,y) = d_{i+1}(x,x,y) for odd i < n
        result.push_str(&format!("d{}(xxy)=d{}(xxy)\n", i, i + 1));
        // d_i(x,y,x) = d_{i+1}(x,y,x) for odd i < n
        result.push_str(&format!("d{}(xyx)=d{}(xyx)\n", i, i + 1));
    }

    // d_n(x,y,y) = p(x,y,y)
    result.push_str(&format!("d{}(xyy)=p(xyy)\n", n));
    // p(x,x,y) = e₀(x,x,y)
    result.push_str(&format!("p(xxy)=e{}(xxy)\n", 0));

    // e_i(x,x,y) = e_{i+1}(x,x,y) for odd i < n
    for i in (1..n).step_by(2) {
        result.push_str(&format!("e{}(xxy)=e{}(xxy)\n", i, i + 1));
    }

    for i in (0..n).step_by(2) {
        // e_i(x,y,y) = e_{i+1}(x,y,y) for even i < n
        result.push_str(&format!("e{}(xyy)=e{}(xyy)\n", i, i + 1));
        // e_i(x,y,x) = e_{i+1}(x,y,x) for even i < n
        result.push_str(&format!("e{}(xyx)=e{}(xyx)\n", i, i + 1));
    }

    // e_n(x,y,z) = z
    result.push_str(&format!("e{}(xyz)=z", n));

    result
}

fn jonsson_chain(n: u32) -> String {
    let mut result = String::from("j1(xxy)=x\n");

    for i in 1..=n {
        result += &format!("j{}(xyy)=j{}(xyy)\n", 2 * i - 1, 2 * i);
    }
    for i in 1..=(2 * n + 1) {
        result += &format!("j{}(xyx)=x\n", i);
    }
    for i in 1..=n {
        result += &format!("j{}(xxy)=j{}(xxy)\n", 2 * i, 2 * i + 1);
    }
    result += &format!("j{}(xyy)=y", 2 * n + 1);

    result
}

fn kearnes_kiss_chain(n: u32) -> String {
    assert!(n > 1, "Kearnes-Kiss chain is only defined for n > 1");
    // d_0(x,y,z) ≈ x
    let mut result = String::from("d0(xyz)=x\n");
    // Even
    for i in (0..n).step_by(2) {
        // d_i(x,y,y) ≈ d_{i+1}(x,y,y) for even i ∈ {0,1,…,n−1}
        result.push_str(&format!("d{}(xyy)=d{}(xyy)\n", i, i + 1));
        // d_i(x,y,x) ≈ d_{i+1}(x,y,x) for even i ∈ {0,1,…,n−1}
        result.push_str(&format!("d{}(xyx)=d{}(xyx)\n", i, i + 1));
    }
    // Odd
    for i in (1..n).step_by(2) {
        // d_i(x,x,y) ≈ d_{i+1}(x,x,y) for odd i ∈ {1,…,n−1}
        result.push_str(&format!("d{}(xxy)=d{}(xxy)\n", i, i + 1));
    }
    // d_n(x,y,z) ≈ z
    result.push_str(&format!("d{n}(xyz)=z"));

    result
}

fn no_name_chain(n: u32) -> String {
    let mut result = String::from("f0(xyyz)=x\n");

    for i in 0..n {
        result.push_str(&format!("f{}(xxyx)=f{}(xyyx)\n", i, i + 1));
        result.push_str(&format!("f{}(xxyy)=f{}(xyyy)\n", i, i + 1));
    }

    result.push_str(&format!("f{n}(xxyz)=z"));

    result
}

fn near_unamity(k: u32) -> String {
    assert!(k > 1, "Near-unamity is only defined for k > 1");
    weak_near_unamity(k) + "=x"
}

fn weak_near_unamity(k: u32) -> String {
    assert!(k > 1, "Weak-near-unamity is only defined for k > 1");

    let mut result = String::new();
    let term: Vec<_> = (0..k).map(|_| 'x').collect();

    for i in 0..k {
        if i != 0 {
            result.push('=');
        }
        let mut t = term.clone();
        t[i as usize] = 'y';
        result.push_str(&format!("f({})", String::from_iter(t)));
    }

    result
}

fn sigma(k: u32) -> String {
    let lhs: Vec<_> = (0..k).map(|i| i.to_string()).collect();
    let mut rhs = lhs.clone();
    rhs.rotate_right(1);
    format!(
        "s({})=s({})",
        String::from_iter(lhs),
        String::from_iter(rhs)
    )
}

fn totally_symmetric(k: u32) -> String {
    let mut result = String::new();

    for i in 2..=k {
        if i != 2 {
            result.push(',');
        }
        for (j, (u, v)) in (0..i)
            .permutations(i as usize)
            .cartesian_product(totally_symmetric_helper(k, i))
            .enumerate()
        {
            if j != 0 {
                result.push('=');
            }
            let identity: String = zip(u, v)
                .map(|(a, b)| (0..b).map(|_| a.to_string()).collect::<String>())
                .collect();
            result.push_str(&format!("f({})", identity));
        }
    }

    result
}

fn totally_symmetric_helper(sum: u32, n: u32) -> Vec<Vec<u32>> {
    fn inner(sum: u32, n: u32, sequence: &mut Vec<u32>, index: usize, result: &mut Vec<Vec<u32>>) {
        if sum == 0 && index == n as usize {
            result.push(sequence.clone());
            return;
        }

        if index == n as usize {
            return;
        }

        for i in 1..=sum {
            sequence[index] = i;
            inner(sum - i, n, sequence, index + 1, result);
        }
    }

    let mut result = Vec::new();
    let mut sequence = vec![0; n as usize];

    inner(sum, n, &mut sequence, 0, &mut result);

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::Polymorphisms;
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
        let wnu2 = Polymorphisms::wnu(2);
        let wnu2_exists = wnu2.exist(&graph) || wnu2.exist(&triad);
        assert!(!wnu2_exists);

        let kmm = Polymorphisms::kmm();
        let kmm_exists = kmm.exist(&graph) || kmm.exist(&triad);
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
        let wnu2_exists = Polymorphisms::wnu(2).exist(&graph);
        assert!(!wnu2_exists);

        let majority_exists = Polymorphisms::majority().exist(&graph);
        assert!(majority_exists);
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
        let majority = Polymorphisms::majority().exist(&graph);
        assert!(!majority);

        let homck2 = Polymorphisms::hobby_mckenzie(2).exist(&graph);
        assert!(homck2);

        let kk5 = Polymorphisms::kearnes_kiss(5).exist(&graph);
        assert!(kk5);
    }

    #[test]
    fn test_nl_hard() {
        let graph = AdjList::from_edges([
            (0, 1),
            (1, 2),
            (3, 2),
            (3, 4),
            (4, 5),
            (6, 0),
            (6, 7),
            (8, 7),
            (9, 8),
            (8, 10),
            (10, 11),
        ]);
        let hami = Polymorphisms::hagemann_mitschke(8).exist(&graph);
        assert!(hami);
    }

    #[test]
    fn test_parse_identities() {
        let input = "p(xyy)=q(yxx)=q(xxy), p(xyx)=q(xyx)";
        let error = "p(xyy)=q(yxx)=q(xxy), p(xyx)q(xyx)";
        let arity = "p(xyy)=q(yxx)=q(xxy), p(xyx)=q(xyxx)";
        let constant = "p(xyy)=q(yxx)=q(xxy), p(xyx)=q(xyx)=z";
        let empty = "";
        let malformed1 = "p(xyy)";
        let malformed2 = "x";

        assert!(Polymorphisms::parse(error).is_err());
        assert!(Polymorphisms::parse(input).is_ok());
        assert_eq!(
            Polymorphisms::parse(arity),
            Err(ParseError::AmbiguousArity("q".into()))
        );
        assert_eq!(
            Polymorphisms::parse(constant),
            Err(ParseError::UnboundConstant('z'))
        );
        assert_eq!(Polymorphisms::parse(empty), Err(ParseError::EmptyString));
        assert_eq!(
            Polymorphisms::parse(malformed1),
            Err(ParseError::MalformedEquation)
        );
        assert_eq!(
            Polymorphisms::parse(malformed2),
            Err(ParseError::MalformedEquation)
        );
    }
}
