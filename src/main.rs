use std::{env, fs, path::Path, process::exit};

use crate::{builder::build, parser::parse, tokenizer::tokenize};

mod tokenizer;
mod parser;
mod builder;

fn main() {
    let args: Vec<String> = env::args().collect();

    let program_directory_string = args.get(1);

    let program_directory = match program_directory_string {
        Some(directory) => Path::new(directory),
        None => {
            eprintln!("Path to the Neutrino file not provided");
            exit(2)
        },
    };

    let program_content = fs::read_to_string(program_directory).unwrap_or_else(|err| {
        eprintln!("Error reading provided file\n{err}");
        exit(err.raw_os_error().unwrap_or(1))
    });

    let tokens = tokenize(&program_content);
    let syntax_tree = parse(&tokens);
    let ir = build(&syntax_tree);

    // Pass ir to most likely LLVM, i'll figure it out later.
}
