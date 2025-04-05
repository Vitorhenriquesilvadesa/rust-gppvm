use std::{ fmt::{ self, Display }, rc::Rc };

use crate::token::Token;

use super::{ ast::FieldDeclaration, expressions::Expression };

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    // region:  --- Statements
    If(Token, Expression, Box<Statement>, Option<Box<Statement>>),
    While(Expression, Box<Statement>),
    ForEach(Token, Expression, Box<Statement>),
    Expression(Expression),
    Match,
    Scope(Vec<Rc<Statement>>),
    Import(Token),
    Return(Option<Expression>),
    // endregion:  --- Statements

    // region:  --- Declarations
    Decorator(Token, Vec<Expression>),
    Type(Token, Vec<Token>, Vec<FieldDeclaration>),
    Function(Token, Vec<FieldDeclaration>, Rc<Statement>, Expression),
    InternalFunction(Token, Token, Vec<FieldDeclaration>, Rc<Statement>, Expression),
    NativeFunction(Token, Vec<FieldDeclaration>, Expression),
    Global,
    Variable(Token, Option<Expression>),
    // endregion:  --- Statements

    // region:  --- For Compiler
    EndCode, // endregion:  --- For Compiler
}

impl Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Statement::Expression(expr) => write!(f, "ExpressionStmt({:?})", expr),
            _ => Err(fmt::Error),
        }
    }
}
