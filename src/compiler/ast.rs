use super::{ expressions::Expression, lexer::Token };

#[derive(Debug, Clone, PartialEq)]
pub struct FieldDeclaration {
    pub name: Token,
    pub kind: Expression,
}

impl FieldDeclaration {
    pub fn new(name: Token, kind: Expression) -> Self {
        FieldDeclaration { name, kind }
    }
}
