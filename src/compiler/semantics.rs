use crate::gpp_error;
use std::collections::HashMap;

use super::{
    lexer::Token,
    parser::{Expression, FieldDeclaration, Statement},
};

#[derive(Debug, Clone, Copy)]
pub enum Value {
    Int(i32),
    Float(f32),
    Boolean(bool),
}

impl Value {
    pub fn boolean(value: bool) -> Self {
        Value::Boolean(value)
    }

    pub fn float(value: f32) -> Self {
        Value::Float(value)
    }

    pub fn int(value: i32) -> Self {
        Value::Int(value)
    }

    pub fn as_int(&self) -> Option<i32> {
        if let Value::Int(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    pub fn as_float(&self) -> Option<f32> {
        if let Value::Float(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    pub fn as_boolean(&self) -> Option<bool> {
        if let Value::Boolean(v) = self {
            Some(*v)
        } else {
            None
        }
    }
}

struct TypeDecl {
    name: String,
    kind_id: u32,
}

impl TypeDecl {
    fn new(name: String, kind_id: u32) -> Self {
        Self { name, kind_id }
    }
}

struct SemanticValue {
    kind: Option<TypeDecl>,
    value: Value,
}

impl SemanticValue {
    fn new(kind: Option<TypeDecl>, value: Value) -> Self {
        Self { kind, value }
    }
}

struct StaticValue {
    kind: TypeDecl,
    value: Value,
}

impl StaticValue {
    fn new(kind: TypeDecl, value: Value) -> Self {
        Self { kind, value }
    }
}

struct ContextScope {
    names: HashMap<String, SemanticValue>,
}

impl ContextScope {
    fn new() -> Self {
        Self {
            names: HashMap::new(),
        }
    }
}

struct ContextStack {
    scopes: Vec<ContextScope>,
}

impl ContextStack {
    fn new() -> Self {
        Self { scopes: Vec::new() }
    }

    pub fn len(&self) -> usize {
        self.scopes.len()
    }
}

pub struct SemanticAnalyzer {
    statements: Vec<Statement>,
    context_stack: ContextStack,
    current_stmt: usize,
}

pub struct SymbolTable {
    names: HashMap<String, StaticValue>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            names: HashMap::new(),
        }
    }
}

pub struct IntermediateCode {}

impl IntermediateCode {
    pub fn new() -> Self {
        IntermediateCode {}
    }
}

impl SemanticAnalyzer {
    pub fn new() -> Self {
        Self {
            statements: Vec::new(),
            context_stack: ContextStack::new(),
            current_stmt: 0,
        }
    }

    pub fn analyze(&mut self, statements: Vec<Statement>) -> IntermediateCode {
        self.reset_internal_state(statements);

        while !self.is_at_end() {
            let stmt = self.current().unwrap().clone();
            self.analyze_stmt(stmt);
        }

        IntermediateCode::new()
    }

    fn analyze_stmt(&mut self, stmt: Statement) {
        match stmt {
            Statement::Expression(expr) => self.analyze_expr(expr.clone()),
            Statement::Decorator(hash_token, attribs) => {
                self.analyze_decorator(hash_token, attribs.clone())
            }
            Statement::Function(name, params, body) => self.analyze_function(name, params, *body),
            _ => gpp_error!("Statement {:?} not supported.", stmt),
        }
    }

    fn analyze_function(&mut self, name: Token, params: Vec<FieldDeclaration>, body: Statement) {
        if self.depth() != 0 {
            gpp_error!("Functions are only allowed in top level code.");
        }

        match body {
            Statement::Scope(stmts) => {
                for stmt in stmts {
                    self.analyze_stmt(*stmt);
                }
            }
            _ => gpp_error!("Statement {:?} is not allowed here.", body),
        }
    }

    fn analyze_decorator(&mut self, hash_token: Token, attributes: Vec<Expression>) {
        match self.next() {
            Statement::Function(name, params, body) => {}
            _ => gpp_error!(
                "Decorators are only accepted in function signatures. At line {}.",
                hash_token.line,
            ),
        }
    }

    fn analyze_expr(&mut self, expr: Expression) {}

    fn next(&self) -> Statement {
        match self.statements.get(self.current_stmt + 1) {
            None => Statement::EndCode,
            Some(stmt) => stmt.clone(),
        }
    }

    fn is_at_end(&self) -> bool {
        match self.current() {
            None => true,
            Some(stmt) => match stmt {
                Statement::EndCode => true,
                _ => false,
            },
        }
    }

    fn current(&self) -> Option<&Statement> {
        self.statements.get(self.current_stmt)
    }

    fn reset_internal_state(&mut self, statements: Vec<Statement>) {
        self.statements = statements;
        self.context_stack = ContextStack::new();
        self.current_stmt = 0;
    }

    fn depth(&self) -> usize {
        self.context_stack.len()
    }
}
