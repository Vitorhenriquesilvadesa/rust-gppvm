mod lexer;

use lexer::Lexer;

pub struct Compiler {
    lexer: lexer::Lexer,
}

impl Compiler {
    pub fn new() -> Self {
        Compiler {
            lexer: Lexer::without_source(),
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
