mod lexer;
mod parser;

use self::{lexer::Lexer, parser::Parser};

pub struct Compiler {
    lexer: lexer::Lexer,
    parser: parser::Parser,
}

impl Compiler {
    pub fn new() -> Self {
        Compiler {
            lexer: Lexer::without_source(),
            parser: Parser::new(),
        }
    }

    pub fn compile(&mut self, source: String) {
        self.lexer.reset_internal_state(source);

        let tokens = self.lexer.scan_tokens();

        for token in tokens {
            println!("{:?}", token)
        }
    }
}
