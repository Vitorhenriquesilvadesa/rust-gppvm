#![allow(dead_code)]
use crate::compiler::{ self, CompilerArguments };

pub struct CommandlineArguments {
    args: Vec<String>,
}

pub struct VirtualMachineArguments {
    args: Vec<String>,
}

impl CommandlineArguments {
    pub fn new(args: Vec<String>) -> Self {
        Self { args }
    }
}

pub fn run(config: CommandlineArguments) -> Result<(), String> {
    if config.args.len() == 1 {
        return Err(String::from("Usage: gpp --help"));
    }

    match config.args[1].as_str() {
        "-c" => compiler::run(CompilerArguments::new(config.args[1..].to_vec())),
        "-v" => {
            println!("gppvm version 0.0.1 alpha");
            Ok(())
        }
        "-e" => todo!(),

        _ => { panic!("Unexpected argument.") }
    }
}
