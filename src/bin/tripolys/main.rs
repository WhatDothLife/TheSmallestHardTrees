//! # Tripolys
//!
//! `tripolys` is a program for checking homomorphisms and testing polymorphism
//! conditions of directed graphs. It also implements an algorithm to generate
//! orientations of trees, and core orientations of trees.

use std::error::Error;
use std::fmt::Debug;

use clap::{App, AppSettings};
use colored::*;
use tripolys::graph::{
    classes::*,
    formats::{from_csv, from_triad},
};
use tripolys::solve::solver::SolveStats;

mod dot;
mod endomorphism;
mod generate;
mod homomorphism;
mod polymorphism;

type CmdResult = Result<(), Box<dyn Error>>;

pub fn cli() -> App<'static, 'static> {
    App::new("Tripolys")
        .setting(AppSettings::ArgRequiredElseHelp)
        .setting(AppSettings::DeriveDisplayOrder)
        .setting(AppSettings::DisableVersion)
        .setting(AppSettings::VersionlessSubcommands)
        .author("Michael W. <michael.wernthaler@posteo.de>")
        .about("A program for checking homomorphisms and testing polymorphism conditions of directed graphs.")
        .subcommands([
            endomorphism::cli(),
            homomorphism::cli(),
            polymorphism::cli(),
            generate::cli(),
            dot::cli(),
        ])
}

/// Print error message to stderr and terminate
fn error(message: &str) -> ! {
    eprintln!("{} {}", "error:".red().bold(), message);
    std::process::exit(1);
}

fn main() {
    let args = cli().get_matches();

    let result = match args.subcommand() {
        ("endomorphism", Some(matches)) => endomorphism::command(matches),
        ("homomorphism", Some(matches)) => homomorphism::command(matches),
        ("polymorphism", Some(matches)) => polymorphism::command(matches),
        ("dot", Some(matches)) => dot::command(matches),
        ("generate", Some(matches)) => generate::command(matches),
        _ => Ok(()),
    };

    match result {
        Err(e) => error(&e.to_string()),
        Ok(()) => {}
    }
}

fn parse_graph<G>(s: &str) -> Result<G, Box<dyn Error>>
where
    G: FromIterator<(usize, usize)>,
{
    if let Ok(class) = from_class(s) {
        return Ok(class);
    }
    if let Ok(triad) = from_triad(s) {
        return Ok(triad);
    }
    if let Ok(mut file) = std::fs::File::open(s) {
        if let Ok(g) = from_csv(&mut file) {
            return Ok(g);
        }
    }
    Err(Box::new(ParseGraphError))
}

fn from_class<G: FromIterator<(usize, usize)>>(class: &str) -> Result<G, ClassNotFound> {
    if let Some(g) = class.chars().next() {
        if let Ok(n) = &class[1..].parse::<usize>() {
            match g {
                'k' => return Ok(complete_digraph(*n)),
                'c' => return Ok(directed_cycle(*n)),
                'p' => return Ok(directed_path(*n)),
                't' => return Ok(transitive_tournament(*n)),
                _ => return Err(ClassNotFound),
            }
        }
    }
    Err(ClassNotFound)
}

#[derive(Debug)]
pub struct ParseGraphError;

impl std::fmt::Display for ParseGraphError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Could not parse graph from the given argument")
    }
}

impl std::error::Error for ParseGraphError {}

#[derive(Debug)]
pub struct ClassNotFound;

impl std::fmt::Display for ClassNotFound {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "No graph class registered with that name")
    }
}

impl std::error::Error for ClassNotFound {}

fn print_stats(ss: &SolveStats) {
    println!("Statistics:");
    println!("- {: <14} {:?}s", "t(ac3):", ss.ac3_time.as_secs_f32());
    println!("- {: <14} {:?}s", "t(mac3):", ss.mac3_time.as_secs_f32());
    println!("- {: <14} {}", "#backtracks:", ss.backtracks);
    println!("- {: <14} {}", "#cons. checks:", ss.ccks);
}
