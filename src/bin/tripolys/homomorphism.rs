use std::{collections::HashMap, fmt::Debug, num::ParseIntError};

use clap::{App, AppSettings, Arg, ArgMatches, SubCommand};
use colored::Colorize;
use tripolys::{csp::Problem, graph::AdjList};

use crate::{parse_graph, print_stats, CmdResult};

pub fn cli() -> App<'static, 'static> {
    SubCommand::with_name("homomorphism")
        .setting(AppSettings::DeriveDisplayOrder)
        .about("Check for a homomorphism from G to H")
        .arg(
            Arg::with_name("from")
                .short("f")
                .long("from")
                .value_name("G")
                .takes_value(true)
                .required(true)
                .help("Check for a homomorphism from graph G..."),
        )
        .arg(
            Arg::with_name("to")
                .short("t")
                .long("to")
                .value_name("H")
                .takes_value(true)
                .required(true)
                .help("...to graph H"),
        )
        .arg(
            Arg::with_name("precolor")
                .short("p")
                .long("precolor")
                .value_name("PRECOLORING")
                .takes_value(true)
                .conflicts_with("lists")
                .help("...with precoloring for some vertices [v->p(v)]"),
        )
        .arg(
            Arg::with_name("lists")
                .short("l")
                .long("lists")
                .value_name("LISTS")
                .takes_value(true)
                .conflicts_with("precolor")
                .help("...with lists for each vertex v [i: l(i) given by comma-seperated values]"),
        )
}

pub fn command(args: &ArgMatches) -> CmdResult {
    let g: AdjList<usize> = parse_graph(args.value_of("from").unwrap())?;
    let h: AdjList<usize> = parse_graph(args.value_of("to").unwrap())?;

    let mut problem = Problem::new(g, h);

    if let Some(p) = args.value_of("precolor") {
        let precoloring = parse_precoloring(p)?;

        for (v, d) in precoloring {
            problem.precolor(v, d);
        }
    }

    if let Some(l) = args.value_of("lists") {
        let lists = parse_lists(l)?;

        for (v, d) in lists.into_iter().enumerate() {
            problem.set_list(v, d);
        }
    }

    println!("\n> Checking for homomorphism...");

    if problem.solution_exists() {
        println!("{}", "  ✓ Exists\n".to_string().green());
    } else {
        println!("{}", "  ! Doesn't exist\n".to_string().red());
    };

    print_stats(problem.stats());

    Ok(())
}

fn parse_lists(s: &str) -> Result<Vec<Vec<usize>>, &str> {
    s.split(['\n', ';'])
        .map(|l| {
            l.split(',')
                .map(|v| v.parse::<usize>())
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| "Couldn't parse lists")
}

fn parse_precoloring(s: &str) -> Result<HashMap<usize, usize>, &str> {
    s.split(['\n', ','])
        .map(|l| {
            l.split_once(":").map(|(a, b)| {
                a.parse::<usize>()
                    .and_then(|u| b.parse::<usize>().map(|v| (u, v)))
                    .map_err(|_| "Couldn't parse precoloring")
            })
        })
        .collect::<Option<Result<HashMap<_, _>, _>>>()
        .ok_or("Couldn't parse precoloring")?
}
