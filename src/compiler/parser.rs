use super::lexer::Token;

pub struct Parser {
    tokens: Vec<Token>,
    current: usize,
}

impl Parser {
    pub fn new() -> Self {
        Parser {
            current: 0,
            tokens: Vec::new(),
        }
    }
}
