use clap::{App, AppSettings, Arg, ArgMatches, SubCommand};
use tripolys::graph::utils::edge_list;
use tripolys::tree::*;

use std::fs::{create_dir_all, File};
use std::io::{BufWriter, Write};
use std::path::PathBuf;

use crate::CmdResult;

pub fn cli() -> App<'static, 'static> {
    SubCommand::with_name("generate")
        .setting(AppSettings::DeriveDisplayOrder)
        .about("Generate orientations of trees")
        .arg(
            Arg::with_name("core")
                .short("c")
                .long("core")
                .help("Whether the generated graphs should be cores"),
        )
        .arg(
            Arg::with_name("triad")
                .short("t")
                .long("triad")
                .help("Whether the generated graphs should be triads"),
        )
        .arg(
            Arg::with_name("no-write")
                .short("n")
                .long("no-write")
                .help("Prevent the program from writing to disk"),
        )
        .arg(
            Arg::with_name("start")
                .short("s")
                .long("start")
                .takes_value(true)
                .value_name("NUM")
                .help("Number of nodes to start at"),
        )
        .arg(
            Arg::with_name("end")
                .short("e")
                .long("end")
                .takes_value(true)
                .value_name("NUM")
                .help("Number of nodes to end at (inclusive)"),
        )
        .arg(
            Arg::with_name("data_path")
                .short("d")
                .long("data_path")
                .value_name("PATH")
                .takes_value(true)
                .default_value("./data")
                .help("Path of the data directory"),
        )
}

pub fn command(args: &ArgMatches) -> CmdResult {
    let no_write = args.is_present("no-write");
    let data_path = args.value_of("data_path").unwrap();
    let data_path = PathBuf::from(data_path);

    if !no_write && !data_path.is_dir() {
        return Err(format!("Directory {data_path:?} doesn't exist").into());
    }

    let start = args.value_of("start").unwrap().parse::<usize>()?;
    let end = args.value_of("end").unwrap().parse::<usize>()?;
    let core = args.is_present("core");
    let triad = args.is_present("triad");

    let config = Config { triad, core };

    let mut rooted_trees = vec![];

    for n in start..=end {
        println!("> Vertices: {n}");
        println!("  > Generating trees...");

        let mut stats = Stats::default();
        let trees = generate_trees(n, &mut rooted_trees, &config, &mut stats);

        if let Some(num_ac_calls) = stats.num_ac_calls {
            println!("    - {: <20} {:?}", "#ac calls:", num_ac_calls);
        }
        if let Some(time_ac_call) = stats.time_ac_call {
            println!("    - {: <20} {:.1?}", "t(ac call):", time_ac_call);
        }
        println!("    - {: <20} {:?}", "#trees:", stats.num_trees);
        println!("    - {: <20} {:.1?}", "t(total):", stats.time_total);

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
