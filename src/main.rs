use std::{env, fs, path::Path, process::{exit, Command}};

use crate::{codegen::generate, lexer::tokenize, parser::parse};

mod lexer;
mod parser;
mod codegen;

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
    println!("Tokens:\n{tokens}");
    let syntax_tree = match parse(tokens) {
        Ok(syntax_tree) => syntax_tree,
        Err(err) => {
            eprintln!("{err}");
            exit(1)
        },
    };
    let asm = generate(syntax_tree);

    let _ = fs::write("output.asm", asm);

    if compile("output.asm", "output.exe") {
        let test_status = Command::new("./output.exe")
        .status().unwrap();

        println!("Program exited with {}", test_status)
    }
    

    if compile("test.asm", "test.exe") {
        let test_status = Command::new("./test.exe")
        .status().unwrap();

        println!("Program exited with {}", test_status)
    }
}

fn compile(from: impl ToString, to: impl ToString) -> bool {
    let from = from.to_string();
    let to = to.to_string();

    let _ = fs::remove_file(&to);
    let _ = fs::remove_file("output.o");

    // Run NASM and get it's status
    let nasm_status = Command::new("./mingw64/bin/nasm.exe")
        .args(["-fwin64", &from, "-o", "output.o"])
        .status();

    // Check if the assembly process was successful
    match nasm_status {
        Ok(status) => { // Got a status (File found)
            if !status.success() { // NASM returned 0
                eprintln!("Error assembling program \"{from}\"\nNASM didn't exit successfully");
                return false;
            }
        },
        Err(err) => { // File not found
            eprintln!("Error assembling program \"{from}\"\n{err}");
            return false;
        },
    }

    // Run GCC with NASM's output
    let gcc_status = Command::new("./mingw64/bin/gcc.exe")
        .args(["output.o", "-o", &to])
        .status();

    // Check if the linking process was successful
    match gcc_status {
        Ok(status) => { // Got a status (File found)
            if !status.success() { // GCC returned 0
                eprintln!("Error linking program \"{from}\"\nGCC didn't exit successfully");
                return false;
            }
        },
        Err(err) => { // File not found
            eprintln!("Error linking program \"{from}\"\n{err}");
            return false;
        },
    }

    // Remove intermediary file
    let _ = fs::remove_file("output.o");

    // Compilation successful
    return true
}
