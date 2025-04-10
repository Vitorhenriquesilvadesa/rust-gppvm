#![allow(warnings)]

mod errors;
mod lexer;
mod parser;
mod semantics;
mod statements;
mod expressions;
mod ir_generator;
pub mod bytecode_gen;
pub mod instructions;
mod ast;
mod chunk;
mod decompiler;

use bytecode_gen::BytecodeGenerator;
use decompiler::Decompiler;
use errors::CompilerErrorReporter;
use ir_generator::IRGenerator;
use semantics::SemanticAnalyzer;

use std::cell::RefCell;
use std::rc::Rc;
use std::time::Instant;
use std::{ env, fs };
use std::{ error::Error, io::{ self, Read } };

use crate::read_file_without_bom;
use crate::runtime::virtual_machine::VirtualMachine;

use self::{ lexer::Lexer, parser::Parser };

pub struct CompilerArguments {
    args: Vec<String>,
}

impl CompilerArguments {
    pub fn new(args: Vec<String>) -> Self {
        Self { args }
    }
}

pub fn run(config: CompilerArguments) -> Result<(), String> {
    let path = format!(
        "{}\\{}",
        env
            ::current_dir()
            .map_err(|e| e.to_string())?
            .to_str()
            .unwrap_or(""),
        config.args[1].as_str()
    );

    println!("{}", path);

    let source = match read_file_without_bom(&path) {
        Ok(s) => s,
        Err(msg) => {
            return Err(msg.to_string());
        }
    };

    let mut compiler = Compiler::new();

    let start = Instant::now();
    compiler.compile(source);

    // println!("Compiler took: {:?}", start.elapsed());

    Ok(())
}

pub struct Compiler {
    lexer: lexer::Lexer,
    parser: parser::Parser,
    semantic_analyzer: semantics::SemanticAnalyzer,
    ir_generator: IRGenerator,
    reporter: Rc<RefCell<CompilerErrorReporter>>,
}

impl Compiler {
    pub fn new() -> Self {
        Compiler {
            lexer: Lexer::without_source(),
            parser: Parser::new(),
            semantic_analyzer: SemanticAnalyzer::new(),
            ir_generator: IRGenerator::new(),
            reporter: Rc::new(RefCell::new(CompilerErrorReporter::new())),
        }
    }

    pub fn compile(&mut self, source: String) {
        self.lexer.reset_internal_state(source);

        let tokens = self.lexer.scan_tokens(Rc::clone(&self.reporter));
        let stmts = self.parser.parse(Rc::clone(&self.reporter), tokens.clone());
        let semantic_code = self.semantic_analyzer.analyze(
            Rc::clone(&self.reporter),
            stmts.clone()
        );
        let ir_code = self.ir_generator.generate(Rc::clone(&self.reporter), &semantic_code);

        Decompiler::decompile(&ir_code);

        let bytecode_generator = BytecodeGenerator::new();
        let bytecode = bytecode_generator.generate(&ir_code);

        let mut vm = VirtualMachine::new();
        vm.interpret(&bytecode);

        for error in self.reporter.borrow().get_errors() {
            eprintln!("Error: {} At line {:?}.", error.msg, error.line);
        }
    }
}
