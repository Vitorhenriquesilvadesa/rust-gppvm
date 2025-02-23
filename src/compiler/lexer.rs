#[derive(Debug)]
#[allow(dead_code)]
pub enum TokenKind {
    And,
    As,
    Assert,
    Attribute,
    Break,
    Colon,
    Comma,
    Continue,
    Def,
    DivideEqual,
    Dot,
    DoubleStar,
    DoubleStarEqual,
    Elif,
    Else,
    EndOfFile,
    Equal,
    EqualEqual,
    Except,
    False,
    Finally,
    Float,
    For,
    From,
    Greater,
    GreaterEqual,
    Hash,
    If,
    Import,
    In,
    Indentation,
    Internal,
    Is,
    Lambda,
    LeftBrace,
    LeftBracket,
    LeftParen,
    Less,
    LessEqual,
    Minus,
    MinusEqual,
    NewLine,
    Not,
    NotEqual,
    None,
    Or,
    Pass,
    Plus,
    PlusEqual,
    Pragma,
    Print,
    Raise,
    Return,
    RightBrace,
    RightBracket,
    RightParen,
    Slash,
    Star,
    StarEqual,
    String,
    True,
    Try,
    Type,
    While,
    With,
    Yield,
}

#[derive(Debug)]
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

pub struct Lexer {
    source: String,
    line: usize,
    column: usize,
    start: usize,
    length: usize,
    tokens: Vec<Token>,
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
        }
    }

    pub fn reset_internal_state(&mut self, source: String) {
        self.source = source;
        self.column = 0;
        self.length = 0;
        self.start = 0;
        self.line = 0;
        self.tokens = Vec::new();
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

    fn scan_token(&mut self) -> Token {
        self.sync_cursors();

        let c: char = match self.advance() {
            None => '\0',
            Some(character) => character,
        };

        match c {
            '#' => self.make_token(TokenKind::Hash),
            '[' => self.make_token(TokenKind::LeftBracket),
            ']' => self.make_token(TokenKind::RightBracket),
            '(' => self.make_token(TokenKind::LeftParen),
            ')' => self.make_token(TokenKind::RightParen),
            '{' => self.make_token(TokenKind::LeftBrace),
            '}' => self.make_token(TokenKind::RightBrace),
            '+' => self.make_token(TokenKind::Plus),
            '-' => self.make_token(TokenKind::Minus),
            '*' => {
                if self.eat('*') {
                    if self.eat('=') {
                        self.make_token(TokenKind::DoubleStarEqual);
                    } else {
                        self.make_token(TokenKind::DoubleStar);
                    }
                } else {
                    self.make_token(TokenKind::Star);
                }
            }
            '/' => self.make_token(TokenKind::Slash),
            ',' => self.make_token(TokenKind::Comma),
            ':' => self.make_token(TokenKind::Colon),
            '>' => {
                if self.eat('=') {
                    self.make_token(TokenKind::GreaterEqual);
                } else {
                    self.make_token(TokenKind::Greater);
                }
            }
            '<' => {
                if self.eat('=') {
                    self.make_token(TokenKind::LessEqual);
                } else {
                    self.make_token(TokenKind::Less);
                }
            }
            '=' => {
                if self.eat('=') {
                    self.make_token(TokenKind::EqualEqual);
                } else {
                    self.make_token(TokenKind::Equal);
                }
            }
            _ => {}
        }

        Token::new(TokenKind::Colon, String::from("test"), 0, 0)
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
        let token = Token::new(kind, lexeme, self.line, self.column);

        self.tokens.push(token);
    }

    fn advance(&mut self) -> Option<char> {
        if self.is_at_end() {
            return None;
        }

        let c = self.source.chars().nth(self.start + self.length);
        self.length += 1;
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

        c.eq(&self.peek().unwrap())
    }

    fn peek(&self) -> Option<char> {
        if self.is_at_end() {
            return None;
        }

        self.source.chars().nth(self.start + self.length)
    }

    fn is_at_end(&self) -> bool {
        return self.start + self.length >= self.source.len();
    }
}
