use clap::{Arg, ArgGroup, Command};
use colored::*;
use csv::WriterBuilder;
use itertools::Itertools;
use rayon::prelude::*;
use serde::ser::SerializeStruct;
use serde::{Serialize, Serializer};
use tripolys::algebra::Polymorphisms;
use tripolys::csp::{Problem, Stats};
use tripolys::graph::traits::Digraph;
use tripolys::graph::AdjList;
use tripolys::graph::{edge_list, generators::*, parse_edge_list};

use std::error::Error;

type CmdResult = Result<(), Box<dyn Error>>;

const AVAILABLE_CONDITIONS: [&str; 10] = [
    "majority    majority",
    "k-nu        k-ary near-unamity",
    "k-wnu       k-ary weak near-unamity",
    "kmm         Kearnes-Marković-McKenzie",
    "n-j         Jónsson chain of length n",
    "n-kk        Kearnes-Kiss chain of length n",
    "n-homck     Hobby-McKenzie chain of length n",
    "n-hami      Hagemann-Mitschke chain of length n",
    "n-ts        Totally symmetric of arity n",
    "siggers     siggers",
];

fn main() {
    let args = Command::new("polymorphism")
        .about("Study the polymorphisms of digraphs")
        .arg(
            Arg::new("idempotent")
                .short('I')
                .long("idempotent")
                .action(clap::ArgAction::SetTrue)
                .help("Require idempotence"),
        )
        .arg(
            Arg::new("conservative")
                .short('C')
                .long("conservative")
                .action(clap::ArgAction::SetTrue)
                .help("Require conservativity"),
        )
        .arg(
            Arg::new("list")
                .short('l')
                .long("list")
                .action(clap::ArgAction::SetTrue)
                .help("List available conditions"),
        )
        .arg(
            Arg::new("no-stats")
                .long("no-stats")
                .action(clap::ArgAction::SetTrue)
                .help("Prevent the program from recording statistics"),
        )
        .arg(
            Arg::new("condition")
                .short('c')
                .long("condition")
                .value_name("NAME")
                .help("Name of the condition the polymorphism must satisfy")
                .long_help(
                    "Name of the condition the polymorphism must satisfy, or a custom set of identities.\n\nAvailable conditions:\n  majority    majority\n  k-nu        k-ary near-unanimity\n  k-wnu       k-ary weak near-unanimity\n  kmm         Kearnes-Marković-McKenzie\n  n-j         Jónsson chain of length n\n  n-kk        Kearnes-Kiss chain of length n\n  n-homck     Hobby-McKenzie chain of length n\n  n-hami      Hagemann-Mitschke chain of length n\n  n-ts        Totally symmetric of arity n\n  siggers     Siggers\n\nCustom identities can be passed directly, separated by ',':\n  -c 'p(xyy)=q(yxx)=q(xxy),p(xyx)=q(xyx)'"
                )
                .required_unless_present("list"),
        )
        .arg(
            Arg::new("graph")
                .short('g')
                .long("graph")
                .value_name("H")
                .help("Check a single graph H (edge list or file containing one edge list)")
                .long_help("Check a single graph H for polymorphisms.\n\nH can be an inline edge list or a path to a file containing one edge list:\n  -g \"[(0,1),(1,2),(2,0)]\"\n  -g graph.edges\n\nFor bulk testing of many graphs use --input."),
        )
        .arg(
            Arg::new("input")
                .short('i')
                .long("input")
                .requires("output")
                .value_name("PATH")
                .help("Run on every graph in a file (one edge list per line) and write results to --output"),
        )
        .arg(
            Arg::new("output")
                .short('o')
                .long("output")
                .requires("input")
                .value_name("PATH")
                .help("...and write the results to file at PATH"),
        )
        .arg(
            Arg::new("filter")
                .short('f')
                .long("filter")
                .requires("input")
                .value_name("PREDICATE")
                .value_parser(["deny", "admit"])
                .help("Filter graphs from output"),
        )
        .group(ArgGroup::new("variant").args(["input", "graph"]))
        .get_matches();

    if let Err(e) = run(&args) {
        eprintln!("error: {e}");
        std::process::exit(1);
    }
}

fn run(args: &clap::ArgMatches) -> CmdResult {
    if args.get_flag("list") {
        println!("\nAvailable conditions:");
        for condition in &AVAILABLE_CONDITIONS {
            println!(" - {}", condition);
        }
        return Ok(());
    }

    let no_stats = args.get_flag("no-stats");
    let condition = args.get_one::<String>("condition").unwrap().as_str();
    let conservative = args.get_flag("conservative");
    let idempotent = args.get_flag("idempotent");

    let polymorphism = parse_condition(condition)?
        .conservative(conservative)
        .idempotent(idempotent);

    let filter = args.get_one::<String>("filter").map(|v| match v.as_str() {
        "deny" => false,
        "admit" => true,
        _ => unreachable!(),
    });

    if let Some(graph) = args.get_one::<String>("graph") {
        let h: AdjList<usize> = parse_graph(graph)?;
        let t_start = std::time::Instant::now();
        let h_ind = polymorphism.indicator_graph(&h);
        let t_end = t_start.elapsed();
        let mut problem = Problem::new(&h_ind, &h);

        for v in h_ind.vertices() {
            for (term, constant) in polymorphism.non_height1() {
                if let Some(bindings) = term.match_with(&v) {
                    problem.precolor(v.clone(), *bindings.get(constant).unwrap());
                }
            }
        }
        if idempotent {
            for v in h_ind.vertices() {
                if v.args().iter().all_equal() {
                    problem.precolor(v.clone(), v.args()[0]);
                }
            }
        }
        if conservative {
            for v in h_ind.vertices() {
                problem.set_list(v.clone(), v.args().to_owned());
            }
        }

        println!("\n> Checking for polymorphisms...");

        let (solution, stats) = problem.solve_first();
        if solution.is_some() {
            println!("{}", "  ✓ Exists\n".to_string().green());
        } else {
            println!("{}", "  ! Doesn't exist\n".to_string().red());
        };

        if !no_stats {
            print_stats(stats);
            println!("- {: <20} {:.1?}", "indicator time:", t_end);
            println!("- {: <20} {:?}", "#indicator vertices:", h_ind.vertex_count());
            println!("- {: <20} {:?}", "#indicator edges:", h_ind.edge_count());
        }

        return Ok(());
    }

    let input = args.get_one::<String>("input").unwrap().as_str();
    let output = args.get_one::<String>("output").unwrap().as_str();
    let content = std::fs::read_to_string(input)?;
    let mut lines = content.lines();

    if input.ends_with("csv") {
        lines.next();
    }
    let graphs = lines
        .map(|line| parse_edge_list(line.split(';').next().unwrap()))
        .collect::<Result<Vec<AdjList<usize>>, _>>()?;

    println!("  > Checking for polymorphisms...");
    let t_start = std::time::Instant::now();

    let results: Vec<Record> = graphs
        .into_par_iter()
        .map(|h| {
            let mut problem = polymorphism.problem(&h);
            let (solution, stats) = problem.solve_first();

            Record {
                graph: edge_list(h),
                found: solution.is_some(),
                stats: if !no_stats { Some(stats) } else { None },
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
    println!("  > Writing results...");

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
        state.serialize_field("found", if self.found { "admit" } else { "deny" })?;

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

fn parse_graph<G>(s: &str) -> Result<G, String>
where
    G: tripolys::graph::traits::Build<Vertex = usize>,
{
    if let Some(g) = s.chars().next() {
        if let Ok(n) = &s[1..].parse::<usize>() {
            match g {
                'k' => return Ok(complete_digraph(*n)),
                'c' => return Ok(directed_cycle(*n)),
                'p' => return Ok(directed_path(*n)),
                't' => return Ok(transitive_tournament(*n)),
                _ => {}
            }
        }
    }
    if let Ok(content) = std::fs::read_to_string(s) {
        return parse_edge_list(content.trim());
    }
    if let Ok(t) = triad(s) {
        return Ok(t);
    }
    parse_edge_list(s)
}

#[rustfmt::skip]
fn print_stats(stats: Stats) {
    println!("Statistics:");
    println!("- {: <20} {:?}", "#backtracks:", stats.backtracks);
    println!("- {: <20} {:?}", "#assignments:", stats.assignments);
    println!("- {: <20} {:?}", "#consistency checks:", stats.ccks);
    println!("- {: <20} {:.1?}", "ac3 time:", stats.ac3_time);
    println!("- {: <20} {:.1?}", "mac3 time:", stats.mac3_time);
}

fn parse_condition(s: &str) -> Result<Polymorphisms, String> {
    match s.to_ascii_lowercase().as_str() {
        "majority" => return Ok(Polymorphisms::majority()),
        "siggers" => return Ok(Polymorphisms::siggers()),
        "kmm" => return Ok(Polymorphisms::kmm()),
        _ => {}
    }
    if let Some((pr, su)) = s.split_once('-') {
        if let Ok(pr) = pr.parse() {
            match su {
                "wnu" => return Ok(Polymorphisms::wnu(pr)),
                "nu" => return Ok(Polymorphisms::nu(pr)),
                "j" => return Ok(Polymorphisms::jonsson(pr)),
                "hami" => return Ok(Polymorphisms::hagemann_mitschke(pr)),
                "kk" => return Ok(Polymorphisms::kearnes_kiss(pr)),
                "homck" => return Ok(Polymorphisms::hobby_mckenzie(pr)),
                "nn" => return Ok(Polymorphisms::no_name(pr)),
                "ts" => return Ok(Polymorphisms::totally_symmetric(pr)),
                _ => {}
            }
        }
    }
    Polymorphisms::parse_identities(s).map_err(|e| e.to_string())
}
