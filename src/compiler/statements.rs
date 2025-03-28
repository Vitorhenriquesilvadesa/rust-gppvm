use std::rc::Rc;

use super::{ ast::FieldDeclaration, expressions::Expression, lexer::Token };

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
    Global,
    Variable(Token, Option<Expression>),
    // endregion:  --- Statements

    // region:  --- For Compiler
    EndCode, // endregion:  --- For Compiler
}
