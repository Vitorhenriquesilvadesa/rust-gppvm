use core::panic;
use std::{
    arch::x86_64::_SIDD_SWORD_OPS,
    collections::HashMap,
    fmt::{self, Display},
    thread::current,
};

use super::lexer::{
    create_keywords, KeywordKind, Literal, OperatorKind, PunctuationKind, Token, TokenKind,
};

pub struct Parser {
    tokens: Vec<Token>,
    statements: Vec<Statement>,
    current: usize,
    keywords: HashMap<String, TokenKind>,
    indentations: Vec<u32>,
    scopes: Vec<Statement>,
}

#[derive(Debug, Clone)]
pub enum Expression {
    Literal(Token),
    Unary(Token, Box<Expression>),
    Arithmetic(Box<Expression>, Token, Box<Expression>),
    Logical(Box<Expression>, Token, Box<Expression>),
    Ternary(Box<Expression>, Box<Expression>, Box<Expression>),
    Assign(Token, Box<Expression>),
    Lambda,
    Get(Box<Expression>, Token),
    Variable(Token),
    Set(Box<Expression>, Token, Box<Expression>),
    Call(Box<Expression>, Token, Vec<Expression>),
    Tuple(Vec<Box<Expression>>),
    List(Vec<Box<Expression>>),
    Type(Vec<Token>),
}

#[derive(Debug, Clone)]
pub enum Statement {
    // region:  --- Statements
    If(Expression, Box<Statement>, Option<Box<Statement>>),
    While(Expression, Box<Statement>),
    ForEach(Expression, Expression),
    Expression(Expression),
    Match,
    Scope(Vec<Box<Statement>>),
    // endregion:  --- Statements

    // region:  --- Declarations
    Decorator,
    Type(Token, Vec<FieldDeclaration>),
    Function(Token, Vec<FieldDeclaration>, Box<Statement>),
    Global,
    Variable(Token, Option<Expression>),
    // endregion:  --- Statements
}

#[derive(Debug, Clone)]
pub struct FieldDeclaration {
    name: Token,
    kind: Expression,
}

pub enum CollectionKind {
    Tuple,
    List,
}

impl Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Statement::Expression(expr) => write!(f, "ExpressionStmt({:?})", expr),
            _ => Err(fmt::Error),
        }
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Literal(token) => write!(f, "{}", token),
            Expression::Unary(op, expr) => write!(f, "({} {})", op, expr),
            Expression::Arithmetic(left, op, right) => write!(f, "({} {} {})", left, op, right),
            Expression::Logical(left, op, right) => write!(f, "({} {} {})", left, op, right),
            Expression::Ternary(cond, then_expr, else_expr) => {
                write!(f, "Ternary({} ? {} : {})", cond, then_expr, else_expr)
            }
            Expression::Assign(var, expr) => write!(f, "({} = {})", var, expr),
            Expression::Lambda => write!(f, "(lambda)"),
            Expression::Get(object, field) => write!(f, "({}.{})", object, field),
            Expression::Set(object, field, value) => {
                write!(f, "Set({}.{} = {})", object, field, value)
            }
            Expression::Variable(name) => write!(f, "Variable({})", name),
            Expression::Call(callee, _, args) => write!(f, "Call({:?}, {:?})", callee, args),
            Expression::Tuple(values) => write!(f, "Tuple({:?})", values),
            Expression::List(values) => write!(f, "List({:?})", values),
            Expression::Type(types) => write!(f, "List({:?})", types),
        }
    }
}

impl FieldDeclaration {
    pub fn new(name: Token, kind: Expression) -> Self {
        FieldDeclaration { name, kind }
    }
}

impl Parser {
    pub fn new() -> Self {
        Parser {
            current: 0,
            tokens: Vec::new(),
            statements: Vec::new(),
            keywords: create_keywords(),
            indentations: vec![0u32],
            scopes: vec![Statement::Scope(vec![])],
        }
    }

    pub fn parse(&mut self, tokens: Vec<Token>) -> &Vec<Statement> {
        self.reset_internal_state(tokens);

        while !self.is_at_end() {
            let stmt = self.declaration();
            self.statements.push(stmt);
        }

        &self.statements
    }

    fn declaration(&mut self) -> Statement {
        match self.advance().kind {
            TokenKind::Keyword(keyword) => match keyword {
                KeywordKind::Type => self.type_declaration(),
                KeywordKind::Def => self.function_declaration(),
                _ => {
                    self.backtrack();
                    self.statement()
                }
            },
            _ => {
                self.backtrack();
                self.statement()
            }
        }
    }

    fn function_declaration(&mut self) -> Statement {
        let function_name = self.eat(
            TokenKind::Identifier,
            String::from("Expect function name after 'def'."),
        );

        self.eat(
            TokenKind::Punctuation(PunctuationKind::LeftParen),
            String::from(format!(
                "Expect '(' after function name, but got {}.",
                self.peek().lexeme
            )),
        );

        let mut params: Vec<FieldDeclaration> = Vec::new();

        if !self.check(&[TokenKind::Punctuation(PunctuationKind::RightParen)]) {
            let param_name = self.eat(TokenKind::Identifier, String::from("Expect param name."));

            self.eat(
                TokenKind::Punctuation(PunctuationKind::Colon),
                String::from("Expect ':' after param name."),
            );

            let param_type =
                vec![self.eat(TokenKind::Identifier, String::from("Expect param type."))];

            params.push(FieldDeclaration::new(
                param_name,
                Expression::Type(param_type),
            ));

            while self.try_eat(&[TokenKind::Punctuation(PunctuationKind::Comma)]) {
                let param_name =
                    self.eat(TokenKind::Identifier, String::from("Expect param name."));

                self.eat(
                    TokenKind::Punctuation(PunctuationKind::Colon),
                    String::from("Expect ':' after param name."),
                );

                let param_type =
                    vec![self.eat(TokenKind::Identifier, String::from("Expect param type."))];

                params.push(FieldDeclaration::new(
                    param_name,
                    Expression::Type(param_type),
                ));
            }
        }

        self.eat(
            TokenKind::Punctuation(PunctuationKind::RightParen),
            String::from("Expect ')' after function params."),
        );

        self.eat(
            TokenKind::Punctuation(PunctuationKind::LeftBrace),
            String::from(format!(
                "Expect '{{' before function body, but got {}.",
                self.peek().lexeme
            )),
        );

        let body = self.parse_scope();

        Statement::Function(function_name, params, Box::new(body))
    }

    fn type_declaration(&mut self) -> Statement {
        let type_name = self.eat(
            TokenKind::Identifier,
            String::from("Expect type name after 'type' keyword."),
        );

        self.eat(
            TokenKind::Punctuation(PunctuationKind::LeftBrace),
            String::from("Expect '{' after type name."),
        );

        let mut fields: Vec<FieldDeclaration> = Vec::new();

        if !self.check(&[TokenKind::Punctuation(PunctuationKind::RightBrace)]) {
            let mut field_name = self.eat(
                TokenKind::Identifier,
                String::from(format!(
                    "Expect field name, but got '{}'.",
                    self.peek().lexeme
                )),
            );

            self.eat(
                TokenKind::Punctuation(PunctuationKind::Colon),
                String::from("Expect ':' after field name."),
            );

            let mut field_type: Expression = Expression::Type(vec![self.advance()]);
            fields.push(FieldDeclaration::new(field_name, field_type));

            while self.try_eat(&[TokenKind::Punctuation(PunctuationKind::Comma)]) {
                if self.check(&[TokenKind::Punctuation(PunctuationKind::RightBrace)]) {
                    break;
                }

                field_name = self.eat(
                    TokenKind::Identifier,
                    String::from(format!(
                        "Expect field name, but got {}.",
                        self.peek().lexeme
                    )),
                );

                self.eat(
                    TokenKind::Punctuation(PunctuationKind::Colon),
                    String::from("Expect ':' after field name."),
                );

                field_type = Expression::Type(vec![self.advance()]);
                fields.push(FieldDeclaration::new(field_name, field_type));
            }
        }

        self.eat(
            TokenKind::Punctuation(PunctuationKind::RightBrace),
            String::from("Expect '}' after type fields."),
        );

        Statement::Type(type_name, fields)
    }

    fn statement(&mut self) -> Statement {
        match self.advance().kind {
            TokenKind::Keyword(keyword) => match keyword {
                KeywordKind::If => self.if_statement(),
                KeywordKind::While => self.while_statement(),
                KeywordKind::Let => self.variable_declaration(),

                _ => {
                    panic!("Invalid keyword '{}'.", self.peek().lexeme);
                }
            },
            _ => {
                self.backtrack();
                self.expression_statement()
            }
        }
    }

    fn variable_declaration(&mut self) -> Statement {
        let name = self.eat(
            TokenKind::Identifier,
            String::from("Expect identifier after 'let'."),
        );

        let mut value: Option<Expression> = None;

        if !self.check(&[TokenKind::Punctuation(PunctuationKind::SemiColon)]) {
            value = Some(self.expression());
        }

        self.eat(
            TokenKind::Punctuation(PunctuationKind::SemiColon),
            String::from("Expect ';' after variable declaration."),
        );

        Statement::Variable(name, value)
    }

    fn while_statement(&mut self) -> Statement {
        let condition = self.expression();
        self.eat(
            TokenKind::Punctuation(PunctuationKind::LeftBrace),
            String::from("Expect '{' after 'while' condition."),
        );

        let body = self.parse_scope();

        Statement::While(condition, Box::new(body))
    }

    fn if_statement(&mut self) -> Statement {
        let condition = self.expression();
        self.eat(
            TokenKind::Punctuation(PunctuationKind::LeftBrace),
            format!(
                "Expect '{{' after 'if' condition, but got {:?}. At line {}.",
                self.peek(),
                self.peek().line
            ),
        );

        let then_branch = self.parse_scope();

        let mut else_branch: Option<Box<Statement>> = None;

        if self.try_eat(&[TokenKind::Keyword(KeywordKind::Else)]) {
            self.eat(
                TokenKind::Punctuation(PunctuationKind::LeftBrace),
                String::from(format!(
                    "Expect '{{' after 'else' keyword, but got {:?}",
                    self.peek()
                )),
            );

            else_branch = Some(Box::new(self.parse_scope()));
        }

        Statement::If(condition, Box::new(then_branch), else_branch)
    }

    fn expression_statement(&mut self) -> Statement {
        let expr = self.expression();
        self.eat(
            TokenKind::Punctuation(PunctuationKind::SemiColon),
            String::from(format!(
                "Expect ';' after expression. At line {}.",
                self.peek().line
            )),
        );
        Statement::Expression(expr)
    }

    fn parse_scope(&mut self) -> Statement {
        let mut statements = Vec::<Box<Statement>>::new();

        while !self.try_eat(&[TokenKind::Punctuation(PunctuationKind::RightBrace)]) {
            statements.push(Box::new(self.statement()));
        }

        Statement::Scope(statements)
    }

    fn expression(&mut self) -> Expression {
        self.assignment()
    }

    fn assignment(&mut self) -> Expression {
        let expr = self.ternary();

        if self.try_eat(&[TokenKind::Operator(OperatorKind::Equal)]) {
            let equals = self.previous();
            let value = self.assignment();

            match expr {
                Expression::Variable(name) => {
                    return Expression::Assign(name, Box::new(value));
                }

                Expression::Get(object, name) => {
                    return Expression::Set(object, name, Box::new(value));
                }

                _ => {
                    panic!("Invalid assignment target at line {}.", equals);
                }
            }
        }

        expr
    }

    fn ternary(&mut self) -> Expression {
        let if_branch = self.or();

        if self.try_eat(&[TokenKind::Keyword(KeywordKind::If)]) {
            let condition = self.expression();

            self.eat(
                TokenKind::Keyword(KeywordKind::Else),
                String::from("Expect 'else' keyword after condition."),
            );

            let else_branch = self.expression();
            return Expression::Ternary(
                Box::new(condition),
                Box::new(if_branch),
                Box::new(else_branch),
            );
        }

        if_branch
    }

    fn or(&mut self) -> Expression {
        let mut expr = self.and();

        while self.try_eat(&[TokenKind::Operator(OperatorKind::Or)]) {
            let operator = self.previous();
            let right = self.and();
            expr = Expression::Logical(Box::new(expr), operator, Box::new(right));
        }

        expr
    }

    fn and(&mut self) -> Expression {
        let mut expr = self.equality();

        while self.try_eat(&[TokenKind::Operator(OperatorKind::And)]) {
            let operator = self.previous();
            let right = self.equality();
            expr = Expression::Logical(Box::new(expr), operator, Box::new(right));
        }

        expr
    }

    fn equality(&mut self) -> Expression {
        let mut expr = self.comparison();

        while self.try_eat(&[
            TokenKind::Operator(OperatorKind::EqualEqual),
            TokenKind::Operator(OperatorKind::NotEqual),
        ]) {
            let operator = self.previous();
            let right = self.comparison();
            expr = Expression::Arithmetic(Box::new(expr), operator, Box::new(right));
        }

        expr
    }

    fn comparison(&mut self) -> Expression {
        let mut expr = self.term();

        while self.try_eat(&[
            TokenKind::Operator(OperatorKind::Less),
            TokenKind::Operator(OperatorKind::LessEqual),
            TokenKind::Operator(OperatorKind::Greater),
            TokenKind::Operator(OperatorKind::GreaterEqual),
        ]) {
            let operator = self.previous();
            let right = self.term();
            expr = Expression::Arithmetic(Box::new(expr), operator, Box::new(right));
        }

        expr
    }

    fn term(&mut self) -> Expression {
        let mut expr = self.factor();

        while self.try_eat(&[
            TokenKind::Operator(OperatorKind::Minus),
            TokenKind::Operator(OperatorKind::Plus),
        ]) {
            let operator = self.previous();
            let right = self.factor();
            expr = Expression::Arithmetic(Box::new(expr), operator, Box::new(right));
        }

        expr
    }

    fn factor(&mut self) -> Expression {
        let mut expr = self.unary();

        while self.try_eat(&[
            TokenKind::Operator(OperatorKind::Star),
            TokenKind::Operator(OperatorKind::Slash),
        ]) {
            let operator = self.previous();
            let right = self.factor();
            expr = Expression::Arithmetic(Box::new(expr), operator, Box::new(right));
        }

        expr
    }

    fn unary(&mut self) -> Expression {
        if self.try_eat(&[
            TokenKind::Operator(OperatorKind::Minus),
            TokenKind::Operator(OperatorKind::Plus),
            TokenKind::Operator(OperatorKind::Not),
        ]) {
            let operator = self.previous();
            let expression = self.unary();
            return Expression::Unary(operator, Box::new(expression));
        }

        self.call()
    }

    fn call(&mut self) -> Expression {
        let mut expr = self.literal();

        loop {
            if self.try_eat(&[TokenKind::Punctuation(PunctuationKind::LeftParen)]) {
                expr = self.finish_call(expr);
            } else if self.try_eat(&[TokenKind::Punctuation(PunctuationKind::Dot)]) {
                let name = self.eat(
                    TokenKind::Identifier,
                    String::from("Expect property name after '.'."),
                );

                expr = Expression::Get(Box::new(expr), name);
            } else {
                break;
            }
        }

        expr
    }

    fn finish_call(&mut self, callee: Expression) -> Expression {
        let mut arguments = Vec::<Expression>::new();
        if !self.check(&[TokenKind::Punctuation(PunctuationKind::RightParen)]) {
            let mut has_args = true;

            while has_args {
                if arguments.iter().count() >= 255 {
                    panic!(
                        "Can't have more than 255 arguments. At line {}.",
                        self.peek().line
                    );
                }

                arguments.push(self.expression());

                if !self.check(&[TokenKind::Punctuation(PunctuationKind::Comma)]) {
                    has_args = false;
                }
            }
        }

        let paren = self.eat(
            TokenKind::Punctuation(PunctuationKind::RightParen),
            format!("Expect ')' after arguments. At line {}.", self.peek().line),
        );

        Expression::Call(Box::new(callee), paren, arguments)
    }

    fn literal(&mut self) -> Expression {
        if self.try_eat(&[
            TokenKind::Literal(Literal::Number),
            TokenKind::Literal(Literal::Boolean),
            TokenKind::Literal(Literal::String),
        ]) {
            return Expression::Literal(self.previous());
        }

        if self.try_eat(&[TokenKind::Identifier]) {
            return Expression::Variable(self.previous());
        }

        match self.advance().kind {
            TokenKind::Punctuation(punctuation) => match punctuation {
                PunctuationKind::LeftBracket => self.collection_expression(
                    PunctuationKind::RightBracket,
                    "Expect ']' after list values.",
                    CollectionKind::List,
                ),
                PunctuationKind::LeftParen => self.collection_expression(
                    PunctuationKind::RightParen,
                    "Expect ')' after tuple values.",
                    CollectionKind::List,
                ),
                _ => {
                    panic!("Invalid punctuation {:?}.", self.peek());
                }
            },
            _ => {
                panic!("Invalid expression {:?}.", self.peek());
            }
        }
    }

    fn collection_expression(
        &mut self,
        closing: PunctuationKind,
        error_msg: &str,
        kind: CollectionKind,
    ) -> Expression {
        let mut values: Vec<Box<Expression>> = Vec::new();

        values.push(Box::new(self.expression()));

        while self.try_eat(&[TokenKind::Punctuation(PunctuationKind::Comma)]) {
            values.push(Box::new(self.expression()));
        }

        self.eat(TokenKind::Punctuation(closing), error_msg.to_string());

        match kind {
            CollectionKind::List => Expression::List(values),
            CollectionKind::Tuple => Expression::Tuple(values),
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

    fn eat(&mut self, kind: TokenKind, msg: String) -> Token {
        match self.try_eat(&[kind]) {
            true => self.previous(),
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

    fn check(&mut self, kind: &[TokenKind]) -> bool {
        for k in kind {
            if *k == self.peek().kind {
                return true;
            }
        }

        false
    }

    fn advance(&mut self) -> Token {
        self.current += 1;
        self.previous()
    }

    fn peek(&self) -> Token {
        self.tokens[self.current].clone()
    }

    fn backtrack(&mut self) {
        self.current -= 1;
    }
}
