use clap::{App, AppSettings, Arg, ArgGroup, ArgMatches, SubCommand};
use colored::*;
use csv::WriterBuilder;
use itertools::Itertools;
use rayon::prelude::*;
use serde::ser::SerializeStruct;
use serde::{Serialize, Serializer};
use tripolys::algebra::Polymorphisms;
use tripolys::csp::{Problem, Stats};
use tripolys::graph::traits::{Vertices, Edges};
use tripolys::graph::AdjList;
use tripolys::graph::{edge_list, parse_edge_list};

use crate::{parse_graph, print_stats, CmdResult};

const AVAILABLE_CONDITIONS: [&str; 10] = [
    "majority    majority",
    "k-nu        k-ary near-unamity",
    "k-wnu       k-ary weak near-unamity",
    "kmm         Kearnes-Marković-McKenzie",
    "n-j         Jónsson chain of length n",
    "n-kk        Kearnes-Kiss chain of length n",
    "n-homck     Hobby-McKenzie chain of length n",
    "n-hami      Hagemann-Mitschke chain of length n",
    "n-ts        Totally symmetric of arity n",
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

    let no_stats = args.is_present("no-stats");
    let condition = args.value_of("condition").unwrap();
    let conservative = args.is_present("conservative");
    let idempotent = args.is_present("idempotent");

    let polymorphism = parse_condition(condition)?
        .conservative(conservative)
        .idempotent(idempotent);

    let filter = args.value_of("filter").map(|v| match v {
        "deny" => false,
        "admit" => true,
        &_ => unreachable!(),
    });

    if let Some(graph) = args.value_of("graph") {
        let h: AdjList<usize> = parse_graph(graph)?;
        let t_start = std::time::Instant::now();
        let h_ind = polymorphism.indicator_graph(&h);
        let t_end = t_start.elapsed();
        let mut problem = Problem::new(&h_ind, &h);

        for v in h_ind.vertices() {
            for (term, constant) in polymorphism.non_height1() {
                if let Some(bindings) = term.match_with(&v) {
                    problem.set_value(v.clone(), *bindings.get(constant).unwrap());
                }
            }
        }
        if idempotent {
            for v in h_ind.vertices() {
                if v.args().iter().all_equal() {
                    problem.set_value(v.clone(), v.args()[0]);
                }
            }
        }
        if conservative {
            for v in h_ind.vertices() {
                problem.set_list(v.clone(), v.args().to_owned());
            }
        }

        println!("\n> Checking for polymorphisms...");

        if problem.solution_exists() {
            println!("{}", "  ✓ Exists\n".to_string().green());
        } else {
            println!("{}", "  ! Doesn't exist\n".to_string().red());
        };

        if !no_stats {
            print_stats(problem.stats());
            println!("- {: <20} {:.1?}", "indicator time:", t_end);
            println!("- {: <20} {:?}", "#indicator vertices:", h_ind.vertex_count());
            println!("- {: <20} {:?}", "#indicator edges:", h_ind.edge_count());
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
            let mut problem = polymorphism.problem(&h);

            Record {
                graph: edge_list(h),
                found: problem.solution_exists(),
                stats: if !no_stats {
                    Some(problem.stats())
                } else {
                    None
                },
            }
        })
        .filter(|record| {
            !(match filter {
                None => false,
                Some(x) => x ^ record.found,
            })
        })
        .collect();

    let t_end = t_start.elapsed();
    println!("    - total_time: {t_end:?}");
    println!("  > Writing results...",);

    let mut wtr = WriterBuilder::new()
        .has_headers(false)
        .delimiter(b';')
        .from_path(output)?;
    let mut header = vec!["graph", condition];
    if !no_stats {
        header.extend(&["backtracks", "ac3_time", "mac3_time", "total_time"]);
    }
    wtr.write_record(&header)?;

    for record in results {
        wtr.serialize(record)?;
    }

    Ok(())
}

/// A struct which stores recorded data during the polymorphism search.
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

fn parse_condition(s: &str) -> Result<Polymorphisms, String> {
    match s.to_ascii_lowercase().as_str() {
        "majority" => Ok(Polymorphisms::majority()),
        "siggers" => Ok(Polymorphisms::siggers()),
        "kmm" => Ok(Polymorphisms::kmm()),
        _ => {
            if let Some((pr, su)) = s.split_once('-') {
                if let Ok(pr) = pr.parse() {
                    match su {
                        "wnu" => Ok(Polymorphisms::wnu(pr)),
                        "nu" => Ok(Polymorphisms::nu(pr)),
                        "j" => Ok(Polymorphisms::jonsson(pr)),
                        "hami" => Ok(Polymorphisms::hagemann_mitschke(pr)),
                        "kk" => Ok(Polymorphisms::kearnes_kiss(pr)),
                        "homck" => Ok(Polymorphisms::hobby_mckenzie(pr)),
                        "nn" => Ok(Polymorphisms::no_name(pr)),
                        "ts" => Ok(Polymorphisms::totally_symmetric(pr)),
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
