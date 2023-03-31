use clap::{App, AppSettings, Arg, ArgGroup, ArgMatches, SubCommand};
use colored::*;
use csv::WriterBuilder;
use rayon::prelude::*;
use serde::ser::SerializeStruct;
use serde::{Serialize, Serializer};
use tripolys::algebra::Identities;
use tripolys::algebra::Polymorphism;
use tripolys::csp::Stats;
use tripolys::graph::utils::{edge_list, parse_edge_list};
use tripolys::graph::AdjList;

use crate::{parse_graph, print_stats, CmdResult};

const AVAILABLE_CONDITIONS: [&str; 5] = [
    "majority    majority",
    "k-nu        k-ary near-unamity",
    "k-wnu       k-ary weak near-unamity",
    "kmm         Kearnes-Marković-McKenzie",
    // "n-j         Jónsson chain of length n",
    // "n-kk        Kearnes-Kiss chain of length n",
    // "n-homck     Hobby-McKenzie chain of length n",
    // "n-hami      Hagemann-Mitschke chain of length n",
    // "n-ts        Totally symmetric of arity n",
    "siggers     siggers",
];

pub fn cli() -> App<'static, 'static> {
    SubCommand::with_name("polymorphism")
        .setting(AppSettings::DeriveDisplayOrder)
        .about("Study the polymorphisms of digraphs")
        .arg(
            Arg::with_name("idempotent")
                .short("I")
                .long("idempotent")
                .help("Require idempotence"),
        )
        .arg(
            Arg::with_name("conservative")
                .short("C")
                .long("conservative")
                .help("Require conservativity"),
        )
        .arg(
            Arg::with_name("list")
                .short("l")
                .long("list")
                .help("List available conditions"),
        )
        .arg(
            Arg::with_name("no-stats")
                .long("no-stats")
                .help("Prevent the program from recording statistics"),
        )
        .arg(
            Arg::with_name("condition")
                .short("c")
                .long("condition")
                .takes_value(true)
                .value_name("NAME")
                .help("Name of the condition the polymorphism must satisfy [see all conditions with --list]")
                .required_unless("list"),
        )
        .arg(
            Arg::with_name("graph")
                .short("g")
                .long("graph")
                .takes_value(true)
                .value_name("H")
                .help("Search for polymorphisms of graph H [e.g. 0111,00,0 / graph.csv]..."),
        )
        .arg(
            Arg::with_name("input")
                .short("i")
                .long("input")
                .requires("output")
                .takes_value(true)
                .value_name("PATH")
                .help("...or of every graph in file at PATH (one edge-list per line)"),
        )
        .arg(
            Arg::with_name("output")
                .short("o")
                .long("output")
                .requires("input")
                .takes_value(true)
                .value_name("PATH")
                .help("...and write the results to file at PATH"),
        )
        .arg(
            Arg::with_name("filter")
                .short("f")
                .long("filter")
                .requires("input")
                .takes_value(true)
                .value_name("PREDICATE")
                .possible_values(&["deny", "admit"])
                .help("Filter graphs from output"),
        )
        .group(
            ArgGroup::with_name("variant")
                .args(&["input", "graph"])
        )
}

pub fn command(args: &ArgMatches) -> CmdResult {
    if args.is_present("list") {
        println!("\nAvailable conditions:");
        for condition in &AVAILABLE_CONDITIONS {
            println!(" - {}", condition);
        }
        return Ok(());
    }

    let condition = parse_condition(args.value_of("condition").unwrap())?;
    let conservative = args.is_present("conservative");
    let idempotent = args.is_present("idempotent");
    let no_stats = args.is_present("no-stats");

    let polymorphism = Polymorphism::new(condition)
        .conservative(conservative)
        .idempotent(idempotent);

    let filter = args.value_of("filter").map(|v| match v {
        "deny" => false,
        "admit" => true,
        &_ => unreachable!(),
    });

    if let Some(graph) = args.value_of("graph") {
        let h: AdjList<usize> = parse_graph(graph)?;
        let mut problem = polymorphism.meta_problem(&h);

        println!("\n> Checking for polymorphisms...");

        if problem.solution_exists() {
            println!("{}", "  ✓ Exists\n".to_string().green());
        } else {
            println!("{}", "  ! Doesn't exist\n".to_string().red());
        };

        if !no_stats {
            print_stats(problem.stats());
        }

        return Ok(());
    }

    let input = args.value_of("input").unwrap();
    let output = args.value_of("output").unwrap();
    let content = std::fs::read_to_string(input)?;
    let mut lines = content.lines();

    if input.ends_with("csv") {
        lines.next();
    }
    let graphs = lines
        .map(|line| parse_edge_list(line.split(';').next().unwrap()))
        .collect::<Result<Vec<AdjList<usize>>, _>>()?;

    println!("  > Checking for polymorphisms...",);
    let t_start = std::time::Instant::now();

    let results: Vec<Record> = graphs
        .into_par_iter()
        .map(|h| {
            let mut problem = polymorphism.meta_problem(&h);
            let found = problem.solution_exists();
            let graph = edge_list(h);

            Record {
                graph,
                found,
                stats: if !no_stats {
                    Some(problem.stats())
                } else {
                    None
                },
            }
        })
        .filter(|record| !filter.is_some_and(|x| x ^ record.found))
        .collect();

    let t_end = t_start.elapsed();
    println!("    - total_time: {t_end:?}");
    println!("  > Writing results...",);

    let mut wtr = WriterBuilder::new()
        .has_headers(true)
        .delimiter(b';')
        .from_path(output)?;

    for record in results {
        wtr.serialize(record)?;
    }

    Ok(())
}

/// A struct which allows to store recorded data during the polymorphism search.
#[derive(Debug, Default)]
struct Record {
    pub graph: String,
    pub found: bool,
    pub stats: Option<Stats>,
}

impl Serialize for Record {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut state = serializer.serialize_struct("Record", 3)?;

        state.serialize_field("graph", &self.graph)?;
        state.serialize_field("found", &self.found)?;

        if let Some(stats) = self.stats {
            state.serialize_field("backtracks", &stats.backtracks)?;
            state.serialize_field("ac3_time", &format!("{:.1?}", stats.ac3_time))?;
            state.serialize_field("mac3_time", &format!("{:.1?}", stats.mac3_time))?;
            state.serialize_field(
                "total_time",
                &format!("{:.1?}", stats.mac3_time + stats.ac3_time),
            )?;
        }

        state.end()
    }
}

fn parse_condition(s: &str) -> Result<Identities, String> {
    match &*s.to_ascii_lowercase() {
        "majority" => Ok(Identities::majority()),
        "siggers" => Ok(Identities::siggers()),
        "kmm" => Ok(Identities::kmm()),
        _ => {
            if let Some((pr, su)) = s.split_once('-') {
                if let Ok(pr) = pr.parse() {
                    match su {
                        "wnu" => Ok(Identities::wnu(pr)),
                        "nu" => Ok(Identities::nu(pr)),
                        // "j" => Ok(Identities::jonsson(pr)),
                        // "hami" => Ok(Identities::hagemann_mitschke(pr)),
                        // "kk" => Ok(Identities::kearnes_kiss(pr)),
                        // "homck" => Ok(Identities::hobby_mckenzie(pr)),
                        // "nn" => Ok(Identities::no_name(pr)),
                        // "ts" => Ok(Identities::totally_symmetric(pr)),
                        &_ => Err("unknown Condition, cannot convert from str".to_owned()),
                    }
                } else {
                    Err("unknown Condition, cannot convert from str".to_owned())
                }
            } else {
                Err("unknown Condition, cannot convert from str".to_owned())
            }
        }
    }
}
