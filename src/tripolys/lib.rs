//! # Tripolys
//!
//! `tripolys` is a program for checking homomorphisms and testing polymorphism
//! conditions of directed graphs. It also implements an algorithm to generate
//! orientations of trees, and core orientations of trees.

#![feature(is_sorted)]

pub mod algebra;
pub mod graph;
pub mod csp;
pub mod tree;
