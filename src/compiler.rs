#![allow(warnings)]

mod ast;
mod attributes;
pub mod bytecode_gen;
mod chunk;
mod decompiler;
mod errors;
mod expressions;
pub mod instructions;
mod ir_generator;
mod lexer;
mod parser;
mod semantic_types;
mod semantics;
mod statements;

use bytecode_gen::BytecodeGenerator;
use decompiler::Decompiler;
use errors::CompilerErrorReporter;
use ir_generator::IRGenerator;
use semantics::SemanticAnalyzer;

use std::cell::RefCell;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::time::Instant;
use std::{env, fs};
use std::{
    error::Error,
    io::{self, Read},
};

use crate::runtime::virtual_machine::VirtualMachine;
use crate::stdlib::StdLibrary;
use crate::{gpp_error, read_file_without_bom};

use self::{lexer::Lexer, parser::Parser};

pub struct CompilerArguments {
    args: Vec<String>,
}

#[derive(Clone)]
pub struct CompilerConfig {
    pub root: PathBuf,
}

impl CompilerConfig {
    fn new<P: Into<PathBuf>>(path: P) -> Self {
        Self { root: path.into() }
    }
}

impl CompilerArguments {
    pub fn new(args: Vec<String>) -> Self {
        Self { args }
    }
}

pub fn run(arguments: CompilerArguments) -> Result<(), String> {
    let path = format!(
        "{}{}{}",
        env::current_dir()
            .map_err(|e| e.to_string())?
            .to_str()
            .unwrap_or(""),
        std::path::MAIN_SEPARATOR,
        arguments.args[1].as_str()
    );

    let full_path = PathBuf::from(&path);
    let root = full_path
        .parent()
        .ok_or("Cannot get parent directory.")?
        .to_path_buf();

    let configuration = CompilerConfig::new(root);

    let source = match read_file_without_bom(&path) {
        Ok(s) => s,
        Err(msg) => {
            return Err(msg.to_string());
        }
    };

    let mut compiler = Compiler::new(arguments, configuration);

    let start = Instant::now();
    compiler.compile(source);

    println!("Compiler took: {:?}", start.elapsed());

    Ok(())
}

pub struct Compiler {
    lexer: lexer::Lexer,
    parser: parser::Parser,
    semantic_analyzer: semantics::SemanticAnalyzer,
    ir_generator: IRGenerator,
    reporter: Rc<RefCell<CompilerErrorReporter>>,
    pub args: CompilerArguments,
    pub config: CompilerConfig,
}

impl Compiler {
    pub fn new(args: CompilerArguments, config: CompilerConfig) -> Self {
        Compiler {
            lexer: Lexer::without_source(),
            parser: Parser::new(),
            semantic_analyzer: SemanticAnalyzer::new(),
            ir_generator: IRGenerator::new(),
            reporter: Rc::new(RefCell::new(CompilerErrorReporter::new())),
            args,
            config,
        }
    }

    pub fn compile(&mut self, source: String) {
        self.lexer.reset_internal_state(source);

        let tokens = self.lexer.scan_tokens(Rc::clone(&self.reporter));

        let stmts = self.parser.parse(Rc::clone(&self.reporter), tokens.clone());

        Self::handle_errors(&self.reporter.borrow());

        let semantic_code =
            self.semantic_analyzer
                .analyze(Rc::clone(&self.reporter), stmts.clone(), &self.config);
        let ir_code = self
            .ir_generator
            .generate(Rc::clone(&self.reporter), &semantic_code);

        Decompiler::decompile(&ir_code);

        let bytecode_generator = BytecodeGenerator::new();
        let bytecode = bytecode_generator.generate(&ir_code);

        let mut vm = VirtualMachine::new();
        vm.attach_bytecode(&bytecode);
        StdLibrary::register_std_libraries(&mut vm);
        vm.interpret();

        for error in self.reporter.borrow().get_errors() {
            eprintln!("Error: {} At line {:?}.", error.msg, error.line);
        }
    }

    fn handle_errors(reporter: &CompilerErrorReporter) {
        if reporter.has_errors() {
            for error in reporter.get_errors() {
                match error.line {
                    Some(line) => {
                        println!("\x1b[31mError\x1b[0m: {}. At line {}.", error.msg, line);
                    }
                    None => {
                        println!("\x1b[31mError\x1b[0m: {}.", error.msg);
                    }
                }
            }

            gpp_error!("The compiler stopped because an error occurred during one of the compilation phases.");
        }
    }
}
