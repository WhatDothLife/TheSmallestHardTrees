use itertools::Itertools;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::iter::zip;
use std::str::FromStr;

/// Represents a term of the form f(x<sub>1</sub>,x<sub>2</sub>,..,x<sub>k</sub>).
#[derive(Clone, Hash, Eq, PartialEq)]
pub struct Term<T> {
    symbol: String,
    arguments: Vec<T>,
}

impl<T: Copy + Hash + Eq> Term<T> {
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
    pub fn args(&self) -> &[T] {
        &self.arguments
    }

    /// Returns the number of unique arguments of the `Term`.
    pub fn arg_count(&self) -> usize {
        self.arguments.iter().unique().count()
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

        for (a, b) in zip(self.args(), other.args()) {
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
