use std::collections::HashMap;

use super::parser::{Expression, Statement};

union Value {
    int: i32,
    float: f32,
    boolean: bool,
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
    scopes: ContextScope,
}

impl ContextStack {
    fn new(scopes: ContextScope) -> Self {
        Self { scopes }
    }
}

pub struct SemanticAnalyzer {
    statements: Statement,
    context_stack: ContextStack,
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

impl SemanticAnalyzer {
    pub fn new(statements: Statement, context_stack: ContextStack) -> Self {
        Self {
            statements,
            context_stack,
        }
    }
}
