use std::{ collections::HashMap, error::Error, fmt::{ self, Display }, ops::Add };

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub enum TokenKind {
    Operator(OperatorKind),
    Keyword(KeywordKind),
    Punctuation(PunctuationKind),
    Literal(Literal),
    Identifier,
    EndOfFile,
    Underscore,
    Dot,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub enum OperatorKind {
    Plus,
    Minus,
    Star,
    Slash,
    EqualEqual,
    Less,
    Greater,
    NotEqual,
    And,
    Or,
    DoubleStarEqual,
    DoubleStar,
    GreaterEqual,
    LessEqual,
    Equal,
    Not,
    Arrow,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub enum KeywordKind {
    If,
    Else,
    Elif,
    For,
    While,
    Return,
    Def,
    Import,
    Lambda,
    Try,
    Except,
    Finally,
    Global,
    Type,
    Or,
    And,
    Let,
    In,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub enum PunctuationKind {
    Comma,
    Dot,
    Colon,
    SemiColon,
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Hash,
    LeftBracket,
    RightBracket,
    Slash,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub enum Literal {
    String,
    Int,
    Float,
    Boolean,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub struct Token {
    pub kind: TokenKind,
    pub lexeme: String,
    pub line: usize,
    pub column: usize,
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}: {:?}", self.kind, self.lexeme)
    }
}

impl Token {
    pub fn new(kind: TokenKind, lexeme: String, line: usize, column: usize) -> Self {
        Token {
            kind,
            lexeme,
            line,
            column,
        }
    }
}

#[derive(Debug)]
pub struct Lexer {
    source: String,
    line: usize,
    column: usize,
    start: usize,
    length: usize,
    tokens: Vec<Token>,
    keywords: HashMap<String, TokenKind>,
}

pub fn create_keywords() -> HashMap<String, TokenKind> {
    let mut keywords = HashMap::new();
    keywords.insert("def".to_string(), TokenKind::Keyword(KeywordKind::Def));
    keywords.insert("global".to_string(), TokenKind::Keyword(KeywordKind::Global));
    keywords.insert("let".to_string(), TokenKind::Keyword(KeywordKind::Let));
    keywords.insert("true".to_string(), TokenKind::Literal(Literal::Boolean));
    keywords.insert("false".to_string(), TokenKind::Literal(Literal::Boolean));
    keywords.insert("type".to_string(), TokenKind::Keyword(KeywordKind::Type));
    keywords.insert("import".to_string(), TokenKind::Keyword(KeywordKind::Import));
    keywords.insert("not".to_string(), TokenKind::Operator(OperatorKind::Not));
    keywords.insert("and".to_string(), TokenKind::Operator(OperatorKind::And));
    keywords.insert("or".to_string(), TokenKind::Operator(OperatorKind::Or));
    keywords.insert("if".to_string(), TokenKind::Keyword(KeywordKind::If));
    keywords.insert("else".to_string(), TokenKind::Keyword(KeywordKind::Else));
    keywords.insert("elif".to_string(), TokenKind::Keyword(KeywordKind::Elif));
    keywords.insert("def".to_string(), TokenKind::Keyword(KeywordKind::Def));
    keywords.insert("while".to_string(), TokenKind::Keyword(KeywordKind::While));
    keywords.insert("for".to_string(), TokenKind::Keyword(KeywordKind::For));
    keywords.insert("in".to_string(), TokenKind::Keyword(KeywordKind::In));
    keywords.insert("return".to_string(), TokenKind::Keyword(KeywordKind::Return));

    keywords
}

#[allow(dead_code)]
impl Lexer {
    pub fn new(source: String) -> Self {
        Lexer {
            source,
            line: 1,
            column: 1,
            start: 0,
            length: 0,
            tokens: Vec::new(),
            keywords: HashMap::new(),
        }
    }

    pub fn without_source() -> Self {
        Lexer {
            source: String::new(),
            column: 1,
            length: 0,
            line: 1,
            start: 0,
            tokens: Vec::new(),
            keywords: create_keywords(),
        }
    }

    pub fn reset_internal_state(&mut self, source: String) {
        self.source = source;
        self.column = 1;
        self.length = 0;
        self.start = 0;
        self.line = 1;
        self.tokens = Vec::new();
        self.keywords = create_keywords();
    }

    pub fn scan_tokens(&mut self) -> &Vec<Token> {
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
            '-' => if self.try_eat('>') {
                self.make_token(TokenKind::Operator(OperatorKind::Arrow))
            } else {
                self.make_token(TokenKind::Operator(OperatorKind::Minus))
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
            '/' => self.make_token(TokenKind::Punctuation(PunctuationKind::Slash)),
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
            '.' => self.make_token(TokenKind::Dot),

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
                        dbg!(&c);
                        panic!("Invalid character '{}' at line {}", c, self.line);
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

        let lexeme: String = self.source.chars().skip(self.start).take(self.length).collect();
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

        let lexeme: String = self.source.chars().skip(self.start).take(self.length).collect();

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

        let value: String = self.source
            .chars()
            .skip(self.start + 1)
            .take(self.length - 2)
            .collect();
        self.make_token_with_lexeme(TokenKind::Literal(Literal::String), value);

        Ok(())
    }

    fn make_token(&mut self, kind: TokenKind) {
        let lexeme: String = self.source.chars().skip(self.start).take(self.length).collect();

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

        let c = self.source.chars().nth(self.start + self.length);
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
            .chars()
            .nth(self.start + self.length)
            .unwrap_or('\0')
    }

    fn peek_next(&self) -> char {
        self.source
            .chars()
            .nth(self.start + self.length + 1)
            .unwrap_or('\0')
    }

    fn is_at_end(&self) -> bool {
        return self.start + self.length >= self.source.chars().count();
    }
}
