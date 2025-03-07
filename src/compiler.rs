#![allow(warnings)]

mod errors;
mod instructions;
mod lexer;
mod parser;
mod semantics;

use semantics::SemanticAnalyzer;

use std::time::Instant;
use std::{env, fs};
use std::{
    error::Error,
    io::{self, Read},
};

use crate::read_file_without_bom;

use self::{lexer::Lexer, parser::Parser};

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
        env::current_dir()
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

    println!("Compiler took: {:?}", start.elapsed());

    Ok(())
}

pub struct Compiler {
    lexer: lexer::Lexer,
    parser: parser::Parser,
    semantic_analyzer: semantics::SemanticAnalyzer,
}

impl Compiler {
    pub fn new() -> Self {
        Compiler {
            lexer: Lexer::without_source(),
            parser: Parser::new(),
            semantic_analyzer: SemanticAnalyzer::new(),
        }
    }

    pub fn compile(&mut self, source: String) {
        self.lexer.reset_internal_state(source);

        let tokens = self.lexer.scan_tokens();
        let stmts = self.parser.parse(tokens.clone());
        let intermediate_repr = self.semantic_analyzer.analyze(stmts.clone());
    }
}
