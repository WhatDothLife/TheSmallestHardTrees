use super::iteralgebra::IterAlgebra;
use super::levels;

use crate::csp::Problem;
use crate::graph::traits::{Contract, Edges, Vertices};
use crate::graph::AdjList;

use indexmap::IndexSet;
use itertools::{chain, Itertools};
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::iter::zip;
use std::str::FromStr;

/// Represents a term of the form f(x,y,..,z).
#[derive(Clone, Hash, Eq, PartialEq)]
pub struct Term<T> {
    symbol: String,
    arguments: Vec<T>,
}

impl<T: Copy> Term<T> {
    /// Creates a new `Term` with the given operation symbol and arguments.
    pub fn new<I>(symbol: &str, arguments: I) -> Term<T>
    where
        I: IntoIterator<Item = T>,
    {
        Term {
            symbol: symbol.to_owned(),
            arguments: Vec::from_iter(arguments),
        }
    }

    /// Returns the arity (i.e. number of arguments) of the `Term`.
    pub fn arity(&self) -> usize {
        self.arguments.len()
    }

    /// Returns the operation symbol of the `Term`.
    pub fn symbol(&self) -> &str {
        &self.symbol
    }

    /// Returns a slice of the arguments of the `Term`.
    pub fn arguments(&self) -> &[T] {
        &self.arguments
    }

    /// Maps a `Term<T>` to `Term<U>` by applying a function to the arguments.
    pub fn map<U, F>(&self, op: F) -> Term<U>
    where
        F: FnMut(T) -> U,
    {
        Term {
            symbol: self.symbol.clone(),
            arguments: self.arguments.clone().into_iter().map(op).collect(),
        }
    }

    /// Tries to match this `Term` with another `Term` `other`, by finding a substitution for the
    /// variables in the arguments of `self` that makes `self` equal to `other`. If successful,
    /// returns a `Some` containing the mapping of variable bindings. If not, returns `None`.
    pub fn match_with<U>(&self, other: &Term<U>) -> Option<HashMap<T, U>>
    where
        T: Eq + Hash,
        U: Copy + Eq + Hash,
    {
        if self.symbol() != other.symbol() {
            return None;
        }
        let mut map = HashMap::new();

        for (a, b) in zip(self.arguments(), other.arguments()) {
            if !map.contains_key(a) {
                map.insert(*a, *b);
            } else if let Some(&val) = map.get(a) {
                if val != *b {
                    return None;
                }
            } else {
                return None;
            }
        }
        Some(map)
    }
}

impl FromStr for Term<char> {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (symbol, rest) = s.trim().split_once('(').ok_or("Invalid term format")?;
        let args = rest.trim_end_matches(')').chars();
        Ok(Term::new(symbol, args))
    }
}
impl<T: Debug> Debug for Term<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}({:?})",
            self.symbol,
            self.arguments.iter().format(",")
        )
    }
}

impl<T: Display> Display for Term<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}({})", self.symbol, self.arguments.iter().format(","))
    }
}

/// Operations D<sup>3</sup> → D that must satisfy a system of linear identities.
#[derive(Clone, Debug)]
pub struct Polymorphisms {
    // Operation symbols and their arity
    pub(crate) ops: Vec<(String, usize)>,
    // Equations of the form f(x...z)=d
    pub(crate) non_h1: Vec<(Term<char>, char)>,
    // Equations of the form f(x...z)=f(a...c)
    pub(crate) h1: Vec<(Term<char>, Term<char>)>,
    // Whether the identities can be satisfied level-wise
    pub(crate) level_wise: bool,
    // Whether the polymorphisms must be conservative
    pub(crate) conservative: bool,
}

fn print_identities(identities: &Polymorphisms) {
    println!("Operation-symbols:");
    for (symbol, arity) in &identities.ops {
        println!("{symbol}, arity: {arity}");
    }

    println!("\nNon-height1 equations:");
    for (term, constant) in &identities.non_h1 {
        println!("{term}={constant}");
    }

    println!("\nHeight1 equations:");
    for (lhs, rhs) in &identities.h1 {
        println!("{lhs}={rhs}");
    }
}

/// Checks if both sides have exactly two variables
fn level_wise<V: Copy + Hash + Eq>(lhs: &Term<V>, rhs: &Term<V>) -> bool {
    lhs.arguments().iter().unique().count() == 2 && rhs.arguments().iter().unique().count() == 2
}

fn parse(s: &str) -> Result<Polymorphisms, String> {
    let mut operations = HashMap::new();
    let mut non_h1 = Vec::new();
    let mut h1: Vec<(Term<char>, Term<char>)> = Vec::new();

    for eq_str in s.trim().split([',', '\n']).filter(|x| !x.is_empty()) {
        let mut constant = None;
        let mut terms = Vec::new();

        for st in eq_str.split('=') {
            if let Ok(term) = Term::from_str(st) {
                if let Some(k) = operations.get(term.symbol()) {
                    if *k != term.arity() {
                        return Err(format!("{} has ambiguous arity", term.symbol()));
                    }
                } else {
                    operations.insert(term.symbol().to_owned(), term.arity());
                }
                terms.push(term);
            } else if let Some(c) = st.trim().chars().next() {
                if let Some(d) = constant {
                    return Err(format!(
                        "{} = {} only satisfied for one element structures",
                        c, d
                    ));
                }
                constant = Some(c);
            } else {
                return Err("Malformed equation".to_owned());
            }
        }
        if terms.len() == 0 {
            return Err("Equation is missing a term".to_owned());
        }
        if constant.is_none() && terms.len() == 1 {
            return Err("Equation is missing a term".to_owned());
        }

        if let Some(c) = constant {
            for term in &terms {
                if !term.arguments().contains(&c) {
                    return Err("Constant is not bound by term".to_owned());
                }
                non_h1.push((term.clone(), c));
            }
        }
        if terms.len() > 1 {
            h1.extend(terms.into_iter().tuple_combinations());
        }
    }

    let level_wise = h1
        .iter()
        .flat_map(|(lhs, rhs)| chain(lhs.arguments(), rhs.arguments()))
        .unique()
        .count()
        == 2
        && h1.iter().all(|(lhs, rhs)| level_wise(lhs, rhs));

    Ok(Polymorphisms {
        ops: operations.into_iter().collect(),
        non_h1,
        h1,
        level_wise,
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
    pub fn parse(s: &str) -> Result<Self, String> {
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
        // satisfied level-wise for any k.
        ids.level_wise = true;
        ids
    }

    /// f(a<sub>1</sub>,…,a<sub>n</sub>) ∈ {a<sub>1</sub>,…,a<sub>n</sub>} for all a<sub>i</sub> ∈ D
    pub fn conservative(mut self, flag: bool) -> Self {
        self.conservative = flag;
        self
    }

    /// f(a,a,…,a) = a
    pub fn idempotent(mut self, flag: bool) -> Self {
        if flag {
            for (symbol, arity) in &self.ops {
                self.non_h1
                    .push((Term::new(symbol, (0..*arity).map(|_| 'x')), 'x'));
            }
        }
        self
    }

    pub fn indicator_graph<V: Copy + Eq + Hash>(&self, graph: &AdjList<V>) -> AdjList<Term<V>> {
        let mut ind_edges: Vec<_> = self
            .ops
            .iter()
            .flat_map(|(symbol, arity)| {
                graph
                    .edges()
                    .kproduct_tuples(*arity)
                    .map(move |(u, v)| (Term::new(symbol, u), Term::new(symbol, v)))
            })
            .collect();

        if self.level_wise {
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
                for v in height1_neighbors(self, &x, graph.vertices().collect()) {
                    if queue.remove(&v) {
                        ind_graph.contract_vertex(u.clone(), v.clone());
                        queue_u.push(v);
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
    /// let mut problem = Polymorphisms::kmm().problem(&triad);
    ///
    /// assert!(!problem.solution_exists());
    /// ```
    pub fn problem<V: Copy + Eq + Hash>(&self, h: &AdjList<V>) -> Problem<Term<V>, V> {
        let indicator = self.indicator_graph(h);
        let mut problem = Problem::new(&indicator, h);

        for v in indicator.vertices() {
            for (term, constant) in &self.non_h1 {
                if let Some(bindings) = term.match_with(&v) {
                    problem.precolor(v.clone(), *bindings.get(constant).unwrap());
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
    /// let exists = Polymorphisms::kmm().exist(&triad);
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
        result += &format!("j{}(yxy)=x\n", i);
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

fn height1_neighbors<V>(condition: &Polymorphisms, term: &Term<V>, vertices: Vec<V>) -> Vec<Term<V>>
where
    V: Copy + Eq + Hash,
{
    let mut res = Vec::new();

    for (lhs, rhs) in condition.h1.iter().flat_map(|(a, b)| [(a, b), (b, a)]) {
        if let Some(binding) = lhs.match_with(term) {
            res.extend(neighbors(rhs, binding, vertices.clone()));
        }
    }

    res
}

fn neighbors<U, V>(term: &Term<U>, mapping: HashMap<U, V>, vertices: Vec<V>) -> Vec<Term<V>>
where
    U: Copy + Hash + Eq,
    V: Copy,
{
    let unbound_vars: Vec<_> = term
        .arguments()
        .iter()
        .copied()
        .filter(|v| mapping.get(v).is_none())
        .unique()
        .collect();

    vertices
        .into_iter()
        .kproduct(unbound_vars.len())
        .map(|values| {
            let mut mapping = mapping.clone();
            mapping.extend(zip(unbound_vars.clone(), values));
            term.map(|x| *mapping.get(&x).unwrap())
        })
        .collect()
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
}
