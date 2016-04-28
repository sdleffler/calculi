extern crate clap;
extern crate lambda;

use std::fmt::Display;
use std::io::{self, BufRead, Write};

use clap::{App, Arg, SubCommand};

fn enter_repl<T: Display, F: Fn(&str) -> Result<T, String>>(parse_and_exec: F) {
    let stdin = io::stdin();
    println!("");
    loop {
        let mut line = String::new();
        print!("> ");
        io::stdout().flush().unwrap();
        stdin.lock().read_line(&mut line).unwrap();
        let res = parse_and_exec(line.trim());
        match res {
            Ok(succ) => println!("{}", succ),
            Err(err) => println!("Error: {}", err),
        }
    }
}

fn enter_contextual_repl<C: Clone + Display + Default, T: Display, F: Fn(&str, &mut C) -> Result<T, String>>(parse_and_exec: F) {
    let stdin = io::stdin();
    println!("");
    let mut ctx = C::default();
    loop {
        let mut line = String::new();
        print!("> ");
        io::stdout().flush().unwrap();
        stdin.lock().read_line(&mut line).unwrap();
        let line = line.trim();
        if line == "?context" {
            println!("{}", ctx);
        } else {
            let res = parse_and_exec(line, &mut ctx);
            match res {
                Ok(succ) => println!("{}", succ),
                Err(err) => println!("Error: {}", err),
            }
        }
    }
}

fn main() {
    let matches = App::new("Sleffy's lambda calculus playground")
        .version("0.1")
        .author("Sean Leffler <sean@errno.com>")
        .about("Toys for playing with lambda calculi.")
        .subcommand(SubCommand::with_name("untyped")
            .arg(Arg::with_name("noctx")
                .short("n")
                .long("nocontext")
                .help("Interpret without a context (disables `let` assignments.)"))
            .about("Untyped lambda calculus interpreter."))
        .subcommand(SubCommand::with_name("simple")
            .about("Simply typed lambda calculus interpreter."))
        .subcommand(SubCommand::with_name("systemf"))
            .about("System F interpreter.").get_matches();

    if let Some(matches) = matches.subcommand_matches("untyped") {
        if matches.is_present("noctx") {
            println!("Entering non-contextual REPL.");
            enter_repl(lambda::untyped::evaluate);
        } else {
            enter_contextual_repl(lambda::untyped::evaluate_in_ctx);
        }
    } else if let Some(_) = matches.subcommand_matches("simple") {
        enter_repl(lambda::simple::evaluate)
    } else if let Some(_) = matches.subcommand_matches("systemf") {
        enter_contextual_repl(lambda::systemf::evaluate_in_ctx);
    }
}
