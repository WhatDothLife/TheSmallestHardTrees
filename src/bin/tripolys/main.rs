//! # Tripolys
//!
//! `tripolys` is a program for checking homomorphisms and testing polymorphism
//! conditions of directed graphs. It also implements an algorithm to generate
//! orientations of trees, and core orientations of trees.

#![feature(is_some_and)]

use std::error::Error;

use clap::{App, AppSettings};
use colored::*;
use tripolys::csp::Stats;
use tripolys::graph::classes::*;
use tripolys::graph::traits::Build;
use tripolys::graph::utils::parse_edge_list;

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

fn parse_graph<G>(s: &str) -> Result<G, &str>
where
    G: Build<Vertex = usize>,
{
    if let Ok(class) = from_class(s) {
        return Ok(class);
    }
    if let Ok(triad) = triad(s) {
        return Ok(triad);
    }
    if let Ok(graph) = parse_edge_list(s) {
        return Ok(graph);
    }
    Err("Could not parse graph from the given argument")
}

fn from_class<G>(class: &str) -> Result<G, &str>
where
    G: Build<Vertex = usize>,
{
    if let Some(g) = class.chars().next() {
        if let Ok(n) = &class[1..].parse::<usize>() {
            match g {
                'k' => return Ok(complete_digraph(*n)),
                'c' => return Ok(directed_cycle(*n)),
                'p' => return Ok(directed_path(*n)),
                't' => return Ok(transitive_tournament(*n)),
                _ => return Err("No graph class registered with that name"),
            }
        }
    }
    Err("No graph class registered with that name")
}

#[rustfmt::skip]
fn print_stats(stats: Stats) {
    println!("Statistics:");
    println!("- {: <20} {:.1?}", "AC3 time:", stats.ac3_time);
    println!("- {: <20} {:.1?}", "MAC3 time:", stats.mac3_time);
    println!("- {: <20} {:.1?}", "Total time:", stats.mac3_time + stats.ac3_time);
    println!("- {: <20} {:?}", "#backtracks:", stats.backtracks);
    println!("- {: <20} {:?}", "#assignments:", stats.assignments);
    println!("- {: <20} {:?}", "#consistency checks:", stats.ccks);
}
