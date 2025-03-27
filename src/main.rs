use std::{env, process};

use gppvm::command::{self, CommandlineArguments};

fn main() {
    env::set_var("RUST_BACKTRACE", "1");

    let args: Vec<String> = env::args().into_iter().collect();
    let config = CommandlineArguments::new(args);
    let result = command::run(config);

    if let Err(msg) = result {
        println!("{msg}");
        process::exit(1);
    }
}
