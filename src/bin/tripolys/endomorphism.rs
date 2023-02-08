use clap::{App, Arg, ArgGroup, ArgMatches, SubCommand};
use colored::*;
use itertools::Itertools;
use tripolys::{csp::Problem, graph::AdjList};

use crate::{parse_graph, print_stats, CmdResult};

pub fn cli() -> App<'static, 'static> {
    SubCommand::with_name("endomorphism")
        .about("Study the endomorphisms of a graph H")
        .arg(
            Arg::with_name("find")
                .short("f")
                .long("find")
                .help("Find a smallest core of H"),
        )
        .arg(
            Arg::with_name("check")
                .short("c")
                .long("check")
                .help("Check if H is a core"),
        )
        .group(
            ArgGroup::with_name("variant")
                .args(&["find", "check"])
                .required(true),
        )
        .arg(
            Arg::with_name("graph")
                .short("g")
                .long("graph")
                .takes_value(true)
                .value_name("H")
                .required(true)
                .help("The graph to check"),
        )
}

pub fn command(args: &ArgMatches) -> CmdResult {
    let graph = args.value_of("graph").unwrap();
    let h: AdjList<usize> = parse_graph(graph)?;

    println!("\n> Checking graph...");
    let mut problem = Problem::new(&h, &h);
    let mut sols = Vec::new();
    problem.solve_all(|sol| sols.push(sol));

    let mut injective = true;
    for sol in &sols {
        if !sol.iter().all_unique() {
            injective = false;
            break;
        }
    }
    if injective {
        println!("{}", format!("  ✓ {graph} is a core\n").green());
    } else {
        println!("{}", format!("  ! {graph} is not a core\n").red());
        if args.is_present("find") {
            let (_, i) = sols
                .iter()
                .enumerate()
                .map(|(i, sol)| (sol.iter().unique().count(), i))
                .min()
                .unwrap();

            println!("> Homomorphism:");
            for (j, sol) in sols[i].iter().enumerate() {
                println!("  {} -> {}", j, *sol);
            }
        }
    }

    print_stats(problem.stats().unwrap());

    Ok(())
}
