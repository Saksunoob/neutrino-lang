use std::{env, fs, path::Path, process::exit};

use crate::lexer::tokenize;

mod lexer;
mod parser;

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

    if !program_directory.extension().is_some_and(|ext| ext == "nu"){
        eprintln!("File is not a neutrino file, should end with .nu");
        exit(1);
    }

    let program_content = fs::read_to_string(program_directory).unwrap_or_else(|err| {
        eprintln!("Error reading provided file\n{err}");
        exit(err.raw_os_error().unwrap_or(1))
    });

    let tokens = tokenize(&program_content);
    
    println!("Tokens:\n{tokens}")
}
