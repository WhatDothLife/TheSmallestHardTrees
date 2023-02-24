use clap::{App, AppSettings, Arg, ArgGroup, ArgMatches, SubCommand};
use colored::*;
use csv::WriterBuilder;
use rayon::prelude::*;
use serde::ser::SerializeStruct;
use serde::{Serialize, Serializer};
use tripolys::csp::SolveStats;
use tripolys::graph::formats::{edge_list, from_edge_list};
use tripolys::graph::AdjList;

use std::path::Path;
use std::str::FromStr;
use std::time::Duration;

use tripolys::algebra::{Condition, MetaProblem};

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
    "siggers     Siggers (consider testing for kmm, it is faster)",
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
            Arg::with_name("condition")
                .short("c")
                .long("condition")
                .takes_value(true)
                .value_name("NAME")
                .help("Name of the condition the polymorphism must satisfy [see all conditions with --list]")
                .required_unless("list"),
        )
        .arg(
            Arg::with_name("level-wise")
                .short("L")
                .long("level-wise")
                .help("Test for level-wise satisfiability"),
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

    let condition = Condition::from_str(args.value_of("condition").unwrap())?;
    let conservative = args.is_present("conservative");
    let idempotent = args.is_present("idempotent");
    let level_wise = args.is_present("level-wise");

    let polymorphism = MetaProblem::new(condition)
        .conservative(conservative)
        .idempotent(idempotent)
        .level_wise(level_wise);

    let filter = args.value_of("filter").map(|v| match v {
        "deny" => false,
        "admit" => true,
        &_ => unreachable!(),
    });

    if let Some(graph) = args.value_of("graph") {
        let h: AdjList<usize> = parse_graph(graph)?;
        let mut problem = polymorphism.problem(&h)?;

        println!("\n> Checking for polymorphisms...");

        if problem.solution_exists() {
            println!("{}", "  ✓ Exists\n".to_string().green());
        } else {
            println!("{}", "  ! Doesn't exist\n".to_string().red());
        };

        print_stats(problem.stats().unwrap());

        return Ok(());
    }

    let input_path = args.value_of("input").unwrap();
    let output_path = args.value_of("output").unwrap();
    let content = std::fs::read_to_string(input_path)?;
    let mut lines = content.lines();

    if input_path.ends_with("csv") {
        lines.next();
    }
    let graphs: Vec<_> = lines
        .map(|line| from_edge_list::<AdjList<usize>>(line.split(';').next().unwrap()))
        .collect();

    let log = std::sync::Mutex::new(SearchLog::new());
    println!("  > Checking for polymorphisms...",);
    let tstart = std::time::Instant::now();

    graphs.into_par_iter().for_each(|h| {
        let mut problem = polymorphism.problem(&h).unwrap();
        let found = problem.solution_exists();

        if filter.map_or(true, |v| !(v ^ found)) {
            log.lock()
                .unwrap()
                .add(edge_list(h), found, problem.stats().unwrap());
        }
    });
    let tend = tstart.elapsed();
    println!("    - total_time: {tend:?}");
    println!("  > Writing results...",);
    log.lock().unwrap().write_csv(&output_path)?;

    Ok(())
}

/// A struct which allows to store recorded data during the polymorphism search.
#[derive(Debug, Default)]
struct Record {
    /// String representation of the inspected tree
    pub graph: String,
    /// Whether the polymorphism was found
    pub found: bool,
    /// Number of times the search-algorithm backtracked
    pub backtracks: u32,
    /// Time it took for the initial run of arc-consistency
    pub ac3_time: Duration,
    /// Time it took for the backtracking-search
    pub mac3_time: Duration,
    /// Total sum of ac_time and search_time
    pub total_time: Duration,
}

impl Serialize for Record {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut state = serializer.serialize_struct("Record", 6)?;
        state.serialize_field("tree", &self.graph)?;
        state.serialize_field("found", &self.found)?;
        state.serialize_field("backtracks", &self.backtracks)?;
        state.serialize_field("ac3_time", &format!("{:?}", self.ac3_time))?;
        state.serialize_field("mac3_time", &format!("{:?}", self.mac3_time))?;
        state.serialize_field("total_time", &format!("{:?}", self.total_time))?;
        state.end()
    }
}

/// Stores stats and prints them to csv.
#[derive(Debug, Default)]
pub struct SearchLog(Vec<Record>);

impl SearchLog {
    pub fn new() -> SearchLog {
        SearchLog::default()
    }

    pub fn add(&mut self, graph: String, found: bool, stats: SolveStats) {
        let record = Record {
            graph,
            found,
            backtracks: stats.backtracks,
            ac3_time: stats.ac3_time,
            mac3_time: stats.mac3_time,
            total_time: stats.ac3_time + stats.mac3_time,
        };
        self.0.push(record);
    }

    pub fn write_csv<P: AsRef<Path>>(&self, path: P) -> Result<(), std::io::Error> {
        let mut wtr = WriterBuilder::new()
            .has_headers(true)
            .delimiter(b';')
            .from_path(&path)?;
        for record in &self.0 {
            wtr.serialize(record)?;
        }
        Ok(())
    }
}
