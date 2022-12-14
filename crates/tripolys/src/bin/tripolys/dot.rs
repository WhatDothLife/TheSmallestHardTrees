use clap::{App, AppSettings, Arg, ArgMatches, SubCommand};
use tripolys::digraph::{formats::to_dot, AdjMatrix};

use crate::{parse_graph, CmdResult};

pub fn cli() -> App<'static, 'static> {
    SubCommand::with_name("dot")
        .setting(AppSettings::Hidden)
        .about("Convert a graph to dot format")
        .arg(
            Arg::with_name("graph")
                .short("G")
                .long("graph")
                .takes_value(true)
                .value_name("GRAPH")
                .help("The graph to print"),
        )
        .arg(
            Arg::with_name("out")
                .short("o")
                .long("out")
                .takes_value(true)
                .value_name("FILE")
                .help("Name of the output file"),
        )
}

pub fn command(args: &ArgMatches) -> CmdResult {
    let graph: AdjMatrix = parse_graph(args.value_of("graph").unwrap())?;
    let mut f = std::fs::File::create(args.value_of("out").unwrap())?;
    to_dot(&graph, &mut f)?;

    Ok(())
}
