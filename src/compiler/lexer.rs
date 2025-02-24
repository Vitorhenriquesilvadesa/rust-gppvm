use std::collections::HashMap;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub enum TokenKind {
    Operator(Operator),
    Keyword(Keyword),
    Punctuation(Punctuation),
    Literal(Literal),
    Identifier,
    EndOfFile,
    NewLine,
    Indentation,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub enum Operator {
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
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub enum Keyword {
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
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub enum Punctuation {
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
    Number,
    Boolean,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct Token {
    pub kind: TokenKind,
    pub lexeme: String,
    pub line: usize,
    pub column: usize,
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
    is_line_indent: bool,
}

#[allow(dead_code)]
impl Lexer {
    pub fn new(source: String) -> Self {
        Lexer {
            source,
            line: 0,
            column: 0,
            start: 0,
            length: 0,
            tokens: Vec::new(),
            keywords: HashMap::new(),
            is_line_indent: true,
        }
    }

    pub fn without_source() -> Self {
        Lexer {
            source: String::new(),
            column: 0,
            length: 0,
            line: 0,
            start: 0,
            tokens: Vec::new(),
            keywords: Self::create_keywords(),
            is_line_indent: true,
        }
    }

    pub fn reset_internal_state(&mut self, source: String) {
        self.source = source;
        self.column = 0;
        self.length = 0;
        self.start = 0;
        self.line = 0;
        self.tokens = Vec::new();
        self.keywords = Self::create_keywords();

        self.keywords
            .insert(String::from("def"), TokenKind::Keyword(Keyword::Def));
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

    fn create_keywords() -> HashMap<String, TokenKind> {
        let mut keywords = HashMap::new();
        keywords.insert("def".to_string(), TokenKind::Keyword(Keyword::Def));
        keywords.insert("return".to_string(), TokenKind::Keyword(Keyword::Return));

        keywords
    }

    fn scan_token(&mut self) {
        self.sync_cursors();

        let c: char = match self.advance() {
            None => '\0',
            Some(character) => character,
        };

        match c {
            '\n' => {
                self.make_token(TokenKind::NewLine);
                self.column = 0;
                self.line += 1;
                self.is_line_indent = true;
            }
            ' ' | '\t' => {
                if self.is_line_indent {
                    self.make_token(TokenKind::Indentation);
                }
            }
            '\r' => {}
            '#' => self.make_token(TokenKind::Punctuation(Punctuation::Hash)),
            '[' => self.make_token(TokenKind::Punctuation(Punctuation::LeftBracket)),
            ']' => self.make_token(TokenKind::Punctuation(Punctuation::RightBracket)),
            '(' => self.make_token(TokenKind::Punctuation(Punctuation::LeftParen)),
            ')' => self.make_token(TokenKind::Punctuation(Punctuation::RightParen)),
            '{' => self.make_token(TokenKind::Punctuation(Punctuation::LeftBrace)),
            '}' => self.make_token(TokenKind::Punctuation(Punctuation::RightBrace)),
            '+' => self.make_token(TokenKind::Operator(Operator::Plus)),
            '-' => self.make_token(TokenKind::Operator(Operator::Minus)),
            '*' => {
                if self.eat('*') {
                    if self.eat('=') {
                        self.make_token(TokenKind::Operator(Operator::DoubleStarEqual));
                    } else {
                        self.make_token(TokenKind::Operator(Operator::DoubleStar));
                    }
                } else {
                    self.make_token(TokenKind::Operator(Operator::Star));
                }
            }
            '/' => self.make_token(TokenKind::Punctuation(Punctuation::Slash)),
            ',' => self.make_token(TokenKind::Punctuation(Punctuation::Comma)),
            ':' => self.make_token(TokenKind::Punctuation(Punctuation::Colon)),
            '>' => {
                if self.eat('=') {
                    self.make_token(TokenKind::Operator(Operator::GreaterEqual));
                } else {
                    self.make_token(TokenKind::Operator(Operator::Greater));
                }
            }
            '<' => {
                if self.eat('=') {
                    self.make_token(TokenKind::Operator(Operator::LessEqual));
                } else {
                    self.make_token(TokenKind::Operator(Operator::Less));
                }
            }
            '=' => {
                if self.eat('=') {
                    self.make_token(TokenKind::Operator(Operator::EqualEqual));
                } else {
                    self.make_token(TokenKind::Operator(Operator::Equal));
                }
            }
            '"' => self.string('"').expect("Error in string."),
            '\'' => self.string('\'').expect("Error in string."),

            _ => match c {
                _ if self.is_digit(c) => self.number(),
                _ if self.is_alpha(c) => self.identifier().expect("Error in identifier."),
                _ => {
                    dbg!(&c);
                    panic!("Invalid character '{}' at line {}", c, self.line);
                }
            },
        }
    }

    fn identifier(&mut self) -> Result<(), String> {
        loop {
            if !self.is_alpha_numeric(self.peek()) {
                break;
            }
            self.advance();
        }

        let lexeme: String = self
            .source
            .chars()
            .skip(self.start)
            .take(self.length)
            .collect();
        let kind = self
            .keywords
            .get(&lexeme)
            .cloned()
            .unwrap_or(TokenKind::Identifier);

        self.make_token_with_lexeme(kind, lexeme);
        Ok(())
    }

    fn number(&mut self) {
        while self.is_digit(self.peek()) {
            self.advance();
        }

        if self.check('.') && self.is_digit(self.peek_next()) {
            self.advance();

            while self.is_digit(self.peek()) {
                self.advance();
            }
        }

        let lexeme: String = self
            .source
            .chars()
            .skip(self.start)
            .take(self.length)
            .collect();

        self.make_token_with_lexeme(TokenKind::Literal(Literal::Number), lexeme);
    }

    fn is_alpha_numeric(&self, c: char) -> bool {
        self.is_digit(c) || self.is_alpha(c)
    }

    fn is_digit(&self, c: char) -> bool {
        c >= '0' && c <= '9'
    }

    fn is_alpha(&self, c: char) -> bool {
        c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z'
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

        let value: String = self
            .source
            .chars()
            .skip(self.start + 1)
            .take(self.length - 2)
            .collect();
        self.make_token_with_lexeme(TokenKind::Literal(Literal::String), value);

        Ok(())
    }

    fn make_token(&mut self, kind: TokenKind) {
        let lexeme: String = self
            .source
            .chars()
            .skip(self.start)
            .take(self.length)
            .collect();

        self.make_token_with_lexeme(kind, lexeme);
    }

    fn make_token_with_lexeme(&mut self, kind: TokenKind, lexeme: String) {
        if !matches!(lexeme.as_str(), " " | "\t") {
            self.is_line_indent = false;
        }

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

    fn eat(&mut self, c: char) -> bool {
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
