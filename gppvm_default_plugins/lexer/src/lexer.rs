use std::{ cell::RefCell, collections::HashMap, rc::Rc };

use gppvm_core::{ CompilerContext, Stage, StageKind };
use shared_components::{
    reporter::CompilerErrorReporter,
    token::*,
    util::create_keywords,
    CompilationError,
};

#[derive(Debug)]
pub struct Lexer {
    source: Vec<char>,
    line: usize,
    column: usize,
    start: usize,
    length: usize,
    tokens: Vec<Token>,
    keywords: HashMap<String, TokenKind>,
    reporter: Rc<RefCell<CompilerErrorReporter>>,
}

impl Default for Lexer {
    fn default() -> Self {
        Self {
            source: Default::default(),
            line: Default::default(),
            column: Default::default(),
            start: Default::default(),
            length: Default::default(),
            tokens: Default::default(),
            keywords: Default::default(),
            reporter: Default::default(),
        }
    }
}

impl Stage for Lexer {
    fn get_name(&self) -> &'static str {
        "lexer"
    }

    fn state(&self) -> gppvm_core::stage::StageKind {
        StageKind::Lexer
    }

    fn run(&mut self, ctx: &mut CompilerContext) {
        self.reset_internal_state(ctx.source.clone());
        let tokens = self.scan_tokens(ctx.reporter.clone());
        ctx.tokens = Some(tokens.clone());
    }
}

#[allow(dead_code)]
impl Lexer {
    pub fn new(source: String) -> Self {
        Lexer {
            source: source.chars().collect(),
            line: 1,
            column: 1,
            start: 0,
            length: 0,
            tokens: Vec::new(),
            keywords: create_keywords(),
            reporter: Rc::new(RefCell::new(CompilerErrorReporter::new())),
        }
    }

    pub fn without_source() -> Self {
        Lexer {
            source: Vec::new(),
            column: 1,
            length: 0,
            line: 1,
            start: 0,
            tokens: Vec::new(),
            keywords: create_keywords(),
            reporter: Rc::new(RefCell::new(CompilerErrorReporter::new())),
        }
    }

    pub fn reset_internal_state(&mut self, source: String) {
        self.source = source.chars().collect();
        self.column = 1;
        self.length = 0;
        self.start = 0;
        self.line = 1;
        self.tokens = Vec::new();
        self.keywords = create_keywords();
    }

    pub fn scan_tokens(&mut self, reporter: Rc<RefCell<CompilerErrorReporter>>) -> &Vec<Token> {
        self.reporter = reporter.clone();

        while !self.is_at_end() {
            self.scan_token();
        }

        self.make_token_with_lexeme(TokenKind::EndOfFile, String::from("\0"));

        &self.tokens
    }

    fn sync_cursors(&mut self) {
        self.start += self.length;
        self.length = 0;
    }

    fn scan_token(&mut self) {
        self.sync_cursors();

        let c: char = match self.advance() {
            None => '\0',
            Some(character) => character,
        };

        match c {
            '\n' => {
                self.column = 1;
                self.line += 1;
            }
            ' ' | '\t' => {}
            '\r' => {}
            '#' => self.make_token(TokenKind::Punctuation(PunctuationKind::Hash)),
            '[' => self.make_token(TokenKind::Punctuation(PunctuationKind::LeftBracket)),
            ']' => self.make_token(TokenKind::Punctuation(PunctuationKind::RightBracket)),
            '(' => self.make_token(TokenKind::Punctuation(PunctuationKind::LeftParen)),
            ')' => self.make_token(TokenKind::Punctuation(PunctuationKind::RightParen)),
            '{' => self.make_token(TokenKind::Punctuation(PunctuationKind::LeftBrace)),
            '}' => self.make_token(TokenKind::Punctuation(PunctuationKind::RightBrace)),
            '+' => self.make_token(TokenKind::Operator(OperatorKind::Plus)),
            '-' => {
                if self.try_eat('>') {
                    self.make_token(TokenKind::Operator(OperatorKind::Arrow))
                } else {
                    self.make_token(TokenKind::Operator(OperatorKind::Minus))
                }
            }
            '*' => {
                if self.try_eat('*') {
                    if self.try_eat('=') {
                        self.make_token(TokenKind::Operator(OperatorKind::DoubleStarEqual));
                    } else {
                        self.make_token(TokenKind::Operator(OperatorKind::DoubleStar));
                    }
                } else {
                    self.make_token(TokenKind::Operator(OperatorKind::Star));
                }
            }
            '|' => self.make_token(TokenKind::Operator(OperatorKind::BitwiseOr)),
            '&' => self.make_token(TokenKind::Operator(OperatorKind::BitwiseAnd)),
            '/' => {
                if self.try_eat('/') {
                    self.comment();
                } else {
                    self.make_token(TokenKind::Operator(OperatorKind::Slash))
                }
            }
            ',' => self.make_token(TokenKind::Punctuation(PunctuationKind::Comma)),
            ':' => self.make_token(TokenKind::Punctuation(PunctuationKind::Colon)),
            ';' => self.make_token(TokenKind::Punctuation(PunctuationKind::SemiColon)),
            '>' => {
                if self.try_eat('=') {
                    self.make_token(TokenKind::Operator(OperatorKind::GreaterEqual));
                } else {
                    self.make_token(TokenKind::Operator(OperatorKind::Greater));
                }
            }
            '<' => {
                if self.try_eat('=') {
                    self.make_token(TokenKind::Operator(OperatorKind::LessEqual));
                } else {
                    self.make_token(TokenKind::Operator(OperatorKind::Less));
                }
            }
            '=' => {
                if self.try_eat('=') {
                    self.make_token(TokenKind::Operator(OperatorKind::EqualEqual));
                } else {
                    self.make_token(TokenKind::Operator(OperatorKind::Equal));
                }
            }
            '"' => self.string('"').expect("Error in string."),
            '\'' => self.string('\'').expect("Error in string."),
            '.' => self.make_token(TokenKind::Punctuation(PunctuationKind::Dot)),

            _ =>
                match c {
                    '_' => {
                        if self.is_alpha_numeric(self.peek_next()) {
                            self.identifier().expect("Error in identifier.");
                        } else {
                            self.make_token(TokenKind::Underscore);
                        }
                    }
                    _ if self.is_digit(c) => self.number(),
                    _ if self.is_alpha(c) => self.identifier().expect("Error in identifier."),
                    _ => {
                        self.reporter
                            .borrow_mut()
                            .report_error(
                                CompilationError::new(
                                    format!("Invalid character '{}' at line {}", c, self.line),
                                    Some(self.line)
                                )
                            );
                    }
                }
        }
    }

    fn identifier(&mut self) -> Result<(), String> {
        loop {
            if !(self.is_alpha_numeric(self.peek()) || self.peek() == '_') {
                break;
            }
            self.advance();
        }

        let lexeme: String = self.source[self.start..self.start + self.length].iter().collect();
        let kind = self.keywords.get(&lexeme).cloned().unwrap_or(TokenKind::Identifier);

        self.make_token_with_lexeme(kind, lexeme);
        Ok(())
    }

    fn number(&mut self) {
        while self.is_digit(self.peek()) {
            self.advance();
        }

        let mut is_float = false;

        if self.check('.') && self.is_digit(self.peek_next()) {
            self.advance();

            while self.is_digit(self.peek()) {
                self.advance();
            }

            is_float = true;
        }

        let lexeme: String = self.source[self.start..self.start + self.length].iter().collect();

        if is_float {
            self.make_token_with_lexeme(TokenKind::Literal(Literal::Float), lexeme);
        } else {
            self.make_token_with_lexeme(TokenKind::Literal(Literal::Int), lexeme);
        }
    }

    fn is_alpha_numeric(&self, c: char) -> bool {
        self.is_digit(c) || self.is_alpha(c)
    }

    fn is_digit(&self, c: char) -> bool {
        c >= '0' && c <= '9'
    }

    fn is_alpha(&self, c: char) -> bool {
        (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
    }

    fn string(&mut self, end: char) -> Result<(), String> {
        loop {
            let c = self.peek();

            if c == end {
                break;
            }
            if c == '\n' {
                self.line += 1;
                self.column = 0;
            } else {
                self.column += 1;
            }
            self.advance();
        }

        if self.is_at_end() {
            return Err(format!("Unterminated string at line {}.", self.line));
        }

        self.advance();

        let value: String = self.source[self.start + 1..self.start + self.length - 1]
            .iter()
            .collect();
        self.make_token_with_lexeme(TokenKind::Literal(Literal::String), value);

        Ok(())
    }

    fn make_token(&mut self, kind: TokenKind) {
        let lexeme: String = self.source[self.start..self.start + self.length].iter().collect();
        self.make_token_with_lexeme(kind, lexeme);
    }

    fn make_token_with_lexeme(&mut self, kind: TokenKind, lexeme: String) {
        let token = Token::new(kind, lexeme, self.line, self.column);
        self.tokens.push(token);
    }

    fn advance(&mut self) -> Option<char> {
        if self.is_at_end() {
            return None;
        }

        let c = self.source.get(self.start + self.length).cloned();
        self.length += 1;
        self.column += 1;
        c
    }

    fn try_eat(&mut self, c: char) -> bool {
        if self.is_at_end() {
            return false;
        }

        if !self.check(c) {
            return false;
        }

        self.advance();
        return true;
    }

    fn check(&self, c: char) -> bool {
        if self.is_at_end() {
            return false;
        }

        c.eq(&self.peek())
    }

    fn peek(&self) -> char {
        self.source
            .get(self.start + self.length)
            .cloned()
            .unwrap_or('\0')
    }

    fn peek_next(&self) -> char {
        self.source
            .get(self.start + self.length + 1)
            .cloned()
            .unwrap_or('\0')
    }

    fn is_at_end(&self) -> bool {
        return self.start + self.length >= self.source.len();
    }

    fn comment(&mut self) {
        while !(self.try_eat('\n') || self.is_at_end()) {
            self.advance();
        }
    }
}
