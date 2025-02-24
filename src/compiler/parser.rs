use core::panic;

use super::lexer::{Literal, Token, TokenKind};

pub struct Parser {
    tokens: Vec<Token>,
    expressions: Vec<Expression>,
    current: usize,
}

#[derive(Debug, Clone)]
pub enum Expression {
    Literal(Token),
}

impl Parser {
    pub fn new() -> Self {
        Parser {
            current: 0,
            tokens: Vec::new(),
            expressions: Vec::new(),
        }
    }

    pub fn parse(&mut self, tokens: Vec<Token>) -> &Vec<Expression> {
        self.reset_internal_state(tokens);

        while !self.is_at_end() {
            let expr = self.expression();
            self.expressions.push(expr);
        }

        &self.expressions
    }

    fn expression(&mut self) -> Expression {
        self.literal()
    }

    fn literal(&mut self) -> Expression {
        if self.try_eat(&[
            TokenKind::Identifier,
            TokenKind::Literal(Literal::Number),
            TokenKind::Literal(Literal::Boolean),
            TokenKind::Literal(Literal::String),
        ]) {
            return Expression::Literal(self.previous());
        } else {
            panic!("Invalid expression {:?}.", self.previous());
        }
    }

    fn is_at_end(&self) -> bool {
        self.peek().kind == TokenKind::EndOfFile
    }

    fn previous(&self) -> Token {
        self.tokens[self.current - 1].clone()
    }

    fn reset_internal_state(&mut self, tokens: Vec<Token>) {
        self.tokens = tokens;
    }

    fn consume(&mut self, kind: &[TokenKind], msg: String) -> bool {
        match self.try_eat(kind) {
            true => true,
            false => {
                panic!("{}", msg);
            }
        }
    }

    fn try_eat(&mut self, kind: &[TokenKind]) -> bool {
        for k in kind {
            if *k == self.peek().kind {
                self.advance();
                return true;
            }
        }

        false
    }

    fn advance(&mut self) -> Token {
        self.current += 1;
        self.tokens[self.current].clone()
    }

    fn peek(&self) -> Token {
        self.tokens[self.current].clone()
    }
}
