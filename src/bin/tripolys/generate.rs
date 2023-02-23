use clap::{App, AppSettings, Arg, ArgMatches, SubCommand};
use tripolys::graph::formats::edge_list;
use tripolys::tree::*;

use std::fs::{create_dir_all, File};
use std::io::{BufWriter, Write};
use std::path::PathBuf;
use std::time::Instant;

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
    let data_path = args.value_of("data_path").unwrap();
    let path = PathBuf::from(data_path);

    if !path.is_dir() {
        return Err(format!("Directory {path:?} doesn't exist").into());
    }

    let start = args.value_of("start").unwrap().parse::<usize>()?;
    let end = args.value_of("end").unwrap().parse::<usize>()?;
    let core = args.is_present("core");
    let triad = args.is_present("triad");
    let no_write = args.is_present("no-write");

    let mut config = TreeGenConfig { triad, core };

    let mut rooted_trees = vec![];

    for n in start..=end {
        println!("> Vertices: {n}");
        println!("  > Generating trees...");

        let tstart = Instant::now();
        let trees = generate_trees(n, &mut rooted_trees, &mut config);
        let tend = tstart.elapsed();
        println!("    - total_time: {tend:?}");
        println!("    - Generated trees: {:?}", trees.len());

        if !no_write {
            let dir_name = if n < 10 {
                String::from("0") + &n.to_string()
            } else {
                n.to_string()
            };

            let dir = path.join(dir_name);
            create_dir_all(&dir)?;
            let file = File::create(dir.join(file_name(core, triad)))?;
            let mut writer = BufWriter::new(file);

            for tree in trees {
                writer.write_all(edge_list(&tree).as_bytes())?;
                writer.write_all(b"\n")?;
            }
        }
    }

    Ok(())
}

fn file_name(core: bool, triad: bool) -> &'static str {
    match (core, triad) {
        (true, true) => "core_triads.edges",
        (true, false) => "core_trees.edges",
        (false, true) => "triads.edges",
        (false, false) => "trees.edges",
    }
}

