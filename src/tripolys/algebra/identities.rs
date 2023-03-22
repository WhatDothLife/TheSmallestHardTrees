use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::iter::zip;
use std::str::FromStr;

use itertools::Itertools;

use super::iteralgebra::IterAlgebra;

/// Represents a term of the form f(x,y,..,z).
#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub struct Term<T> {
    symbol: char,
    arguments: Vec<T>,
}

impl<T: Copy> Term<T> {
    /// Creates a new `Term` with the given symbol and arguments.
    pub fn new<I>(symbol: char, arguments: I) -> Term<T>
    where
        I: IntoIterator<Item = T>,
    {
        Term {
            symbol,
            arguments: Vec::from_iter(arguments),
        }
    }

    /// Returns the arity (i.e. number of arguments) of the `Term`.
    pub fn arity(&self) -> usize {
        self.arguments.len()
    }

    /// Returns the symbol of the `Term`.
    pub fn symbol(&self) -> char {
        self.symbol
    }

    /// Returns a slice of the arguments of the `Term`.
    pub fn arguments(&self) -> &[T] {
        &self.arguments
    }

    /// Tries to match this `Term` with another `Term` `other`, by finding a substitution for the
    /// variables in the arguments of `self` that makes `self` equal to `other`. If successful,
    /// returns a `Some` containing the mapping of variable bindings. If not, returns `None`.
    pub fn match_with<U>(&self, other: &Term<U>) -> Option<HashMap<T, U>>
    where
        T: Eq + Hash,
        U: Copy + Eq + Hash,
    {
        // If there is a variable-value pair that contradicts a previously established
        // binding for the same variable, the function returns `None`. Otherwise, it
        // returns `Some` containing the map of variable bindings.
        fn bind<U, T>(v1: &[U], v2: &[T]) -> Option<HashMap<U, T>>
        where
            U: Eq + Hash + Copy,
            T: Eq + Hash + Copy,
        {
            if v1.len() != v2.len() {
                return None;
            }
            let mut map = HashMap::new();
            let mut set = HashSet::new();

            for (a, b) in zip(v1, v2) {
                if !map.contains_key(a) && !set.contains(b) {
                    map.insert(*a, *b);
                    set.insert(*b);
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

        if self.symbol() != other.symbol() {
            return None;
        }
        bind(&self.arguments(), &other.arguments())
    }
}

impl FromStr for Term<char> {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (symbol, vars) = s.trim().split_once('(').ok_or("Invalid term format")?;
        let pattern = vars.trim_end_matches(')').chars().collect();

        let symbol = symbol
            .chars()
            .next()
            .ok_or("Invalid function symbol format")?;
        if !symbol.is_ascii_alphabetic() {
            return Err("Function symbol must be alphabetic".to_string());
        }

        Ok(Term {
            symbol,
            arguments: pattern,
        })
    }
}

impl<T: Display> Display for Term<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}({})", self.symbol, self.arguments.iter().format(","))
    }
}

/// A collection of linear identities.
#[derive(Clone, Debug)]
pub struct Identities {
    /// Operation symbols and their arity
    operations: Vec<(char, usize)>,
    /// Equations of the form f(x...z)=d
    non_h1: Vec<(Term<char>, char)>,
    /// Equations of the form f(x...z)=f(a...c)
    h1: Vec<(Term<char>, Term<char>)>,
}

impl Identities {
    pub fn operations(&self) -> Vec<(char, usize)> {
        self.operations.clone()
    }

    pub fn non_h1_equations(&self) -> Vec<(Term<char>, char)> {
        self.non_h1.clone()
    }

    pub fn h1_equations(&self) -> Vec<(Term<char>, Term<char>)> {
        self.h1.clone()
    }

    pub fn level_wise(&self) -> bool {
        let mut variables = self
            .h1
            .iter()
            .flat_map(|(a, b)| [a, b])
            .map(|t| t.arguments());
        let total = variables.clone().flatten().unique().count() == 2;
        let sides = variables.all(|vars| vars.iter().unique().count() == 2);
        sides && total
    }
}

fn print_identities(identities: &Identities) {
    println!("Operation-symbols:");
    for (symbol, arity) in &identities.operations {
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

impl FromStr for Identities {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut operations = HashMap::new();
        let mut non_height1 = Vec::new();
        let mut height1: Vec<(Term<char>, Term<char>)> = Vec::new();

        for eq_str in s.split([',', '\n']) {
            let mut constant = None;
            let mut terms = Vec::new();

            for st in eq_str.split('=') {
                if let Ok(term) = Term::from_str(st) {
                    if let Some(k) = operations.get(&term.symbol()) {
                        if *k != term.arity() {
                            return Err(format!("{} has ambiguous arity", term.symbol()));
                        }
                    } else {
                        operations.insert(term.symbol(), term.arity());
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
                    non_height1.push((term.clone(), c));
                }
            }
            if terms.len() > 1 {
                height1.extend(terms.into_iter().tuple_combinations());
            }
        }

        Ok(Identities {
            operations: operations.into_iter().collect(),
            non_h1: non_height1,
            h1: height1,
        })
    }
}

macro_rules! identities {
    ($( $name:ident => $eq:expr ),*) => {
        impl Identities {
            $(
                #[doc = $eq]
                pub fn $name() -> Self {
                    Self::from_str($eq).unwrap()
                }
            )*
        }
    };
}

identities!(
    majority => "m(xxy)=m(xyx)=m(yxx)=m(xxx)=x",
    wnu2 => "f(xy)=f(yx)",
    wnu3 => "f(xxy)=f(xyx)=f(yxx)",
    wnu4 => "f(xxxy)=f(xxyx)=f(xyxx)=f(yxxx)",
    wnu34 => "g(xxy)=g(xyx)=g(yxx),f(xxxy)=f(xxyx)=f(xyxx)=f(yxxx),g(yxx)=f(yxxx)" ,
    nu3 => "f(xxy)=f(xyx)=f(yxx)=f(xxx)",
    nu4 => "f(xxxy)=f(xxyx)=f(xyxx)=f(yxxx)=f(xxxx)",
    nu5 => "f(xxxxy)=f(xxxyx)=f(xxyxx)=f(xyxxx)=f(yxxxx)=f(xxxxx)",
    nu6 => "f(xxxxxy)=f(xxxxyx)=f(xxxyxx)=f(xxyxxx)=f(xyxxxx)=f(yxxxxx)=f(xxxxxx)" ,
    nu7 => "f(xxxxxxy)=f(xxxxxyx)=f(xxxxyxx)=f(xxxyxxx)=f(xxyxxxx)=f(xyxxxxx)=f(yxxxxxx)=f(xxxxxxx)" ,
    kmm => "p(xyy)=q(yxx)=q(xxy),p(xyx)=q(xyx)",
    siggers => "s(area)=s(rare)",
    sigma2 => "f(xy)=f(yx)",
    sigma3 => "f(xyz)=f(zxy)",
    sigma5 => "f(abcde)=f(bcdea)",
    ts3 => "f(xyz)=f(zxy)=f(yxz),f(xxy)=f(xyy)",
    ts5 => "f(abcde)=f(bcdea)=f(bacde),f(aacde)=f(accde)",
    fs3 => "f(xyz)=f(zxy)=f(yxz)",
    hm2maj => "p(yyx)=p(xxx),p(xyy)=q(xxy),q(xyy)=q(xxx),p(xyx)=p(xxx)=q(xyx)" ,
    minority => "m(yyy)=m(xxy)=m(xyx)=m(yxx)=y",
    sym_majority => "t(xyz)=t(yxz)=t(yzx),t(xxy)=t(xxx)",
    constant => "f(x)=f(y),x=y",
    edge4 => "f(yyxx)=f(yxyx)=f(xxxx)=f(xxxy)",
    edge5 => "f(yyxxx)=f(yxyxx)=f(xxxxx)=f(xxxyx)=f(xxxxy)",
    pix2 => "p(xyy)=p(xxx)=p(xyx),p(xxy)=q(xyy),q(yxy)=q(xxy)=q(yyy)" ,
    sn123 => "f(000412)=f(341323)",
    sp313 => "f(0124456)=f(1233567)", // already unsat for P2
    sn1234 => "f(0000412567=f3415323673)", // arity too high
    st4 => "f(000112)=f(123233", // should be equivalent to HM2
    nufs3 => "f(xxy)=f(xyx)=f(yxx)=f(xxx,fxyz)=f(zxy)=f(yxz)",
    nufs4 => "f(xxxy)=f(xxxx),f(abcd)=f(bcda)=f(bacd)",
    nufs5 => "f(xxxxy)=f(xxxxx),f(abcde)=f(bcdea)=f(bacde)",
    nufs6 => "f(xxxxxy)=f(xxxxxx),f(abcdef)=f(bcdefa)=f(bacdef)",
    nufs7 => "f(xxxxxxy)=f(xxxxxxx),f(abcdefg)=f(bcdefga)=f(bacdefg)",
    nufs8 => "f(xxxxxxxy)=f(xxxxxxxx),f(abcdefgh)=f(bcdefgha)=f(bacdefgh)",
    gfs1 => "f(aax)=f(bbx)=f(xaa)", //HM1?
    gfs2 => "f(aaxy)=f(bbyx)=f(xaay)",
    gfs3 => "f(aaxyz)=f(bbyxz)=f(bbyzx)=f(xaayz)",
    gfs4 => "f(aaxyzu)=f(bbyxzu)=f(bbyzux)=f(xaayzu)",
    gfs5 => "f(aaxyzuv)=f(bbyxzuv)=f(bbyzuvx)=f(xaayzuv)",
    gfs6 => "f(aaxyzuvw)=f(bbyxzuvw)=f(bbyzuvwx)=f(xaayzuvw)",
    gfs2_3 => "f(aaxyzcc)=f(bbyxzdd)=f(bbyzxdd)=f(xaayzcc)=f(bbxyddz)",
    g2 => "f(aaxy)=f(bbxy)=f(xaay)=f(yaxa)",
    g3 => "f(aaxyz)=f(bbxyz)=f(xaayz)=f(yaxaz)=f(zaxya)",
    gs3 => "f(xxxx)=f(xxxy),f((123x)=f(231x)",
    hm1 => "m(xxx)=m(xyy)=m(yyx)",
    hm2 => "p(yyx)=p(xxx),p(xyy)=q(xxy),q(xyy)=q(xxx)",
    hm3 => "p(yyx)=p(xxx),p(xyy)=q(xxy),q(xyy)=r(xxy),r(xyy)=r(xxx)" ,
    hm4 => "p(yyx)=p(xxx),p(xyy)=q(xxy),q(xyy)=r(xxy),r(xyy)=s(xxy),s(xyy)=s(xxx)" ,
    hm5 => "p(yyx)=p(xxx),p(xyy)=q(xxy),q(xyy)=r(xxy),r(xyy)=s(xxy),s(xyy)=t(xxy),t(xyy)=t(xxx)" ,
    hm6 => "p(yyx)=p(xxx),p(xyy)=q(xxy),q(xyy)=r(xxy),r(xyy)=s(xxy),s(xyy)=t(xxy),t(xyy)=u(xxy),u(xyy)=u(xxx)",
    hm7 => "p(yyx)=p(xxx),p(xyy)=q(xxy),q(xyy)=r(xxy),r(xyy)=s(xxy),s(xyy)=t(xxy),t(xyy)=u(xxy),u(xyy)=v(xxy),v(xyy)=v(xxx)",
    hm8 => "p(yyx)=p(xxx),p(xyy)=q(xxy),q(xyy)=r(xxy),r(xyy)=s(xxy),s(xyy)=t(xxy),t(xyy)=u(xxy),u(xyy)=v(xxy),v(xyy)=w(xxy),w(xyy)=w(xxx)",
    hm9 => "p(yyx)=p(xxx),p(xyy)=q(xxy),q(xyy)=r(xxy),r(xyy)=s(xxy),s(xyy)=t(xxy),t(xyy)=u(xxy),u(xyy)=v(xxy),v(xyy)=w(xxy),w(xyy)=a(xxy),a(xyy)=a(xxx)"
);

// txyz=t(yxz,txxy=t(xyx=t(yxx=t(xxx]],2SymMaj)
// identities!(0xyyz=0xxxx,2xxyz=2zzzz,0xxyx=1xyyx,1xxyx=2xyyx,0xxyy=1xyyy,1xxyy=2xyyy]], NNT)
// identities!(tabcxyz=t(bcaxyz=t(bacxyz=t(abcxzy,taaaxyz=t(abbxyz,tabcxyy=t(abcxxx,tabcxxy=t(abcyyx]],Min+xv(y+z))
// identities!(fxyabc=fyxabc=fxybac=fxybca,f(xyabb=fxyaaa]],S2+Min)

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::Polymorphism;
    use crate::graph::classes::triad;

    #[test]
    fn test_wnu2() {
        let triad = triad("01001111,1010000,011000").unwrap();
        let condition = Identities::wnu2();
        let exists = Polymorphism::new(condition)
            .idempotent(true)
            .meta_problem(&triad)
            .solution_exists();
        assert!(!exists);
    }

    #[test]
    fn test_kmm() {
        let triad = triad("01001111,1010000,011000").unwrap();
        let condition = Identities::kmm();
        let exists = Polymorphism::new(condition)
            .idempotent(true)
            .meta_problem(&triad)
            .solution_exists();
        assert!(!exists);
    }

    #[test]
    fn test_level_wise() {
        assert!(!Identities::siggers().level_wise());
        assert!(!Identities::fs3().level_wise());
        assert!(Identities::wnu2().level_wise());
        assert!(Identities::wnu3().level_wise());
        assert!(Identities::kmm().level_wise());
    }
}
