mod errors;
mod instructions;
mod lexer;
mod parser;
mod semantics;

use semantics::SemanticAnalyzer;

use self::{lexer::Lexer, parser::Parser};

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
