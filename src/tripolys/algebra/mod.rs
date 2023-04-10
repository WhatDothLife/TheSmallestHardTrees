//! Concepts that are related to universal algebra.

mod iteralgebra;
mod polymorphism;
mod term;
mod utils;

pub use polymorphism::*;
pub use term::*;
pub use utils::*;

#[cfg(test)]
mod test;
