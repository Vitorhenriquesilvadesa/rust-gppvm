use core::panic;
use std::{
    collections::HashMap,
    fmt::{self, Display},
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
}

#[derive(Debug, Clone)]
pub enum Statement {
    // region:  --- Statements
    If(Expression, Box<Statement>, Option<Box<Statement>>),
    While,
    ForEach,
    Expression(Expression),
    Match,
    Scope(Option<Box<Statement>>, Vec<Box<Statement>>),
    // endregion:  --- Statements

    // region:  --- Declarations
    Decorator,
    Type,
    Function,
    Global,
    Variable,
    // endregion:  --- Statements
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
        }
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
            scopes: vec![Statement::Scope(None, vec![])],
        }
    }

    pub fn parse(&mut self, tokens: Vec<Token>) -> &Vec<Statement> {
        self.reset_internal_state(tokens);

        while !self.is_at_end() {
            let expr = self.statement();
            self.statements.push(expr);
        }

        &self.statements
    }

    fn statement(&mut self) -> Statement {
        while self.try_eat(&[TokenKind::NewLine]) {
            self.process_indentation();
        }

        println!(
            "Current indent: {}",
            self.indentations
                .get(self.indentations.iter().count() - 1)
                .unwrap()
        );

        match self.peek().kind {
            _ => self.expression_statement(),
        }
    }

    fn expression_statement(&mut self) -> Statement {
        let expr = self.expression();
        Statement::Expression(expr)
    }

    // fn if_statement(&mut self) -> Statement {
    //     let condition = self.expression();
    //     self.eat(
    //         TokenKind::Punctuation(PunctuationKind::Colon),
    //         format!(
    //             "Expect ':' after 'if' condition. At line {}.",
    //             self.peek().line
    //         ),
    //     );

    //     self.eat(
    //         TokenKind::NewLine,
    //         format!("Expect new line after ':'. At line {}.", self.peek().line),
    //     );

    //     let old_depth = self.scopes.iter().count();
    //     self.process_indentation();
    //     let new_depth = self.scopes.iter().count();

    //     if new_depth <= old_depth {
    //         panic!("Indentation error at line {}", self.peek().line);
    //     }
    // }

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
                    println!("\nChegou aqui com {}\n", expr);
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

        panic!("Invalid expression {:?}.", self.peek());
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
        self.tokens[self.current].clone()
    }

    fn peek(&self) -> Token {
        self.tokens[self.current].clone()
    }

    fn process_indentation(&mut self) {
        let mut count = 0u32;
        let mut token = self.peek();

        while token.kind == TokenKind::Indentation {
            count += 1;
            token = self.advance();
        }

        let current_level = self.indentations.last().copied().unwrap_or(0);

        if count > current_level {
            self.indentations.push(count);
        } else {
            while let Some(&last) = self.indentations.last() {
                if last == count {
                    break;
                }
                self.indentations.pop();
            }

            if self.indentations.is_empty() || self.indentations.last().copied().unwrap() != count {
                panic!("Indentation error.");
            }
        }
    }

    fn is_keyword(&self, lexeme: &String) -> bool {
        if let Some(_) = self.keywords.get(lexeme).copied() {
            return true;
        }

        false
    }
}
