use clap::{App, AppSettings, Arg, ArgMatches, SubCommand};
use tripolys::graph::formats::to_edge_list;
use tripolys::tree::generate::{generate_trees, TreeGenConfig, TreeGenStats};

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
                .short("core")
                .long("core")
                .help("Whether the generated graphs should be cores"),
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

    let config = TreeGenConfig {
        core,
        start,
        end,
        stats: Some(TreeGenStats::default()),
    };

    let mut rooted_trees = vec![];

    for n in start..=end {
        println!("\n> #vertices: {n}");
        println!("  > Generating trees...");

        let tstart = Instant::now();
        let trees = generate_trees(n, &mut rooted_trees, &config);
        let tend = tstart.elapsed();
        println!("    - total_time: {tend:?}");

        let dir_name = if n < 10 {
            String::from("0") + &n.to_string()
        } else {
            n.to_string()
        };

        let dir = path.join(dir_name);
        // if triad {
        //     path.push("triads");
        // }
        create_dir_all(&dir)?;
        let file_name = if core { "cores" } else { "trees" };
        let file = File::create(dir.join(file_name))?;
        let mut writer = BufWriter::new(file);

        for tree in trees {
            to_edge_list(&tree, &mut writer)?;
            writer.write_all(b"\n")?;
        }
    }

    Ok(())
}
