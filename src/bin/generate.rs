use clap::{Arg, Command};
use csv::WriterBuilder;
use tripolys::graph::edge_list;
use tripolys::tree::{Config, Stats, Tree, TreeGenerator};

use std::error::Error;
use std::fs::{create_dir_all, File};
use std::io::{BufWriter, Write};
use std::path::PathBuf;

type CmdResult = Result<(), Box<dyn Error>>;

fn main() {
    let args = Command::new("generate")
        .about("Generate orientations of trees")
        .arg(
            Arg::new("core")
                .short('c')
                .long("core")
                .action(clap::ArgAction::SetTrue)
                .help("Whether the generated graphs should be cores"),
        )
        .arg(
            Arg::new("triad")
                .short('t')
                .long("triad")
                .action(clap::ArgAction::SetTrue)
                .help("Whether the generated graphs should be triads"),
        )
        .arg(
            Arg::new("no-write")
                .short('n')
                .long("no-write")
                .action(clap::ArgAction::SetTrue)
                .help("Prevent the program from writing to disk"),
        )
        .arg(
            Arg::new("start")
                .short('s')
                .long("start")
                .value_name("NUM")
                .required(true)
                .help("Number of nodes to start at"),
        )
        .arg(
            Arg::new("end")
                .short('e')
                .long("end")
                .value_name("NUM")
                .required(true)
                .help("Number of nodes to end at (inclusive)"),
        )
        .arg(
            Arg::new("data_path")
                .short('d')
                .long("data_path")
                .value_name("PATH")
                .default_value("./data")
                .help("Path of the data directory"),
        )
        .arg(
            Arg::new("output")
                .short('o')
                .long("output")
                .value_name("FILE")
                .default_value("./output.csv")
                .help("Name of the csv output file"),
        )
        .get_matches();

    if let Err(e) = run(&args) {
        eprintln!("error: {e}");
        std::process::exit(1);
    }
}

fn run(args: &clap::ArgMatches) -> CmdResult {
    let no_write = args.get_flag("no-write");
    let data_path = PathBuf::from(args.get_one::<String>("data_path").unwrap());

    if !no_write && !data_path.is_dir() {
        return Err(format!("Directory {data_path:?} doesn't exist").into());
    }

    let start = args.get_one::<String>("start").unwrap().parse::<usize>()?;
    let end = args.get_one::<String>("end").unwrap().parse::<usize>()?;
    let core = args.get_flag("core");
    let triad = args.get_flag("triad");

    let config = Config { triad, core };

    let mut wtr = args
        .get_one::<String>("output")
        .map(|path| {
            let mut path = path.to_owned();
            if !path.ends_with(".csv") {
                path.push_str(".csv");
            }
            WriterBuilder::new().from_path(path)
        })
        .transpose()?;

    let mut generator = if no_write {
        TreeGenerator::new(config)
    } else {
        TreeGenerator::new(config).with_cache_dir(data_path.clone())
    };

    for n in start..=end {
        println!("> Vertices: {n}");
        println!("  > Generating trees...");

        let mut stats = Stats::default();
        stats.vertices = n as u32;
        let trees = generator.trees(n, &mut stats);

        if let Some(num_ac_calls) = stats.num_ac_calls {
            println!("    - {: <20} {:?}", "#ac calls:", num_ac_calls);
        }
        if let Some(time_ac_call) = stats.time_ac_call {
            println!("    - {: <20} {:.1?}", "t(ac call):", time_ac_call);
        }
        println!("    - {: <20} {:?}", "#trees:", stats.num_trees);
        println!("    - {: <20} {:.1?}", "t(total):", stats.time_total);

        if let Some(wtr) = wtr.as_mut() {
            wtr.serialize(stats)?;
        }

        if !no_write {
            let dir = data_path.join(dir_name(n));
            create_dir_all(&dir)?;

            let file = File::create(dir.join(file_name(core, triad)))?;
            let mut writer = BufWriter::new(file);

            for tree in trees {
                write_tree(&tree, &mut writer)?;
            }
        }
    }

    Ok(())
}

fn dir_name(n: usize) -> String {
    if n < 10 {
        String::from("0") + &n.to_string()
    } else {
        n.to_string()
    }
}

fn file_name(core: bool, triad: bool) -> &'static str {
    match (core, triad) {
        (true, true) => "core_triads.edges",
        (true, false) => "core_trees.edges",
        (false, true) => "triads.edges",
        (false, false) => "trees.edges",
    }
}

fn write_tree<W: Write>(tree: &Tree, writer: &mut W) -> std::io::Result<()> {
    writer.write_all(edge_list(tree).as_bytes())?;
    writer.write_all(b"\n")?;
    Ok(())
}
