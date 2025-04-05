#![allow(dead_code)]
#![allow(unused_variables)]
use std::collections::{ HashMap, HashSet };
use std::fmt::Display;

use crate::token::Token;

use crate::expressions::Expression;

#[derive(Debug, Clone, PartialEq)]
pub struct TypeComposition {
    mask: Vec<TypeDecl>,
}

#[derive(Debug, Clone)]
pub struct ObjectDescriptor {
    fields: HashMap<String, TypeComposition>,
}

#[derive(Debug, Clone)]
pub enum Value {
    Int(i32),
    Float(f32),
    Boolean(bool),
    String(String),
    Object(ObjectDescriptor),
    Kind,
    Internal,
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
        if let Value::Int(v) = self { Some(*v) } else { None }
    }

    pub fn as_float(&self) -> Option<f32> {
        if let Value::Float(v) = self { Some(*v) } else { None }
    }

    pub fn as_boolean(&self) -> Option<bool> {
        if let Value::Boolean(v) = self { Some(*v) } else { None }
    }

    pub fn as_object(&self) -> Option<ObjectDescriptor> {
        if let Value::Object(v) = self { Some(v.clone()) } else { None }
    }
}

#[derive(Clone, Debug)]
pub struct SemanticValue {
    pub kind: Option<TypeDescriptor>,
    pub value: Value,
    pub line: usize,
}

impl SemanticValue {
    pub fn new(kind: Option<TypeDescriptor>, value: Value, line: usize) -> Self {
        Self { kind, value, line }
    }
}

#[derive(Clone, Debug)]
pub struct StaticValue {
    pub kind: TypeDescriptor,
    pub value: Value,
}

impl StaticValue {
    pub fn new(kind: TypeDescriptor, value: Value) -> Self {
        Self { kind, value }
    }
}

#[derive(Clone, Debug)]
pub struct SymbolTable {
    pub names: HashMap<String, StaticValue>,
    pub functions: HashMap<String, FunctionPrototype>,
    pub native_functions: HashMap<String, FunctionPrototype>,
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self {
            names: HashMap::new(),
            functions: HashMap::new(),
            native_functions: HashMap::new(),
        }
    }
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            names: HashMap::new(),
            functions: HashMap::new(),
            native_functions: HashMap::new(),
        }
    }

    pub fn define(&mut self, name: String, value: StaticValue) {
        self.names.insert(name, value);
    }

    pub fn get(&self, name: &str) -> Option<&StaticValue> {
        self.names.get(name)
    }

    pub fn get_function(&mut self, name: &str) -> Option<&mut FunctionPrototype> {
        self.functions.get_mut(name)
    }

    pub fn define_function(&mut self, name: String, value: FunctionPrototype) {
        self.functions.insert(name, value);
    }
}

#[derive(Debug, Clone)]
pub struct AnnotatedAST {
    pub statements: Vec<AnnotatedStatement>,
}

impl AnnotatedAST {
    pub fn new(statements: Vec<AnnotatedStatement>) -> Self {
        Self { statements }
    }
}

#[derive(Debug, Clone)]
pub struct SemanticCode {
    pub table: SymbolTable,
    pub ast: AnnotatedAST,
}

impl SemanticCode {
    pub fn new(table: SymbolTable, ast: AnnotatedAST) -> Self {
        SemanticCode { table, ast }
    }

    pub fn get_table(&self) -> &SymbolTable {
        &self.table
    }
}

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

#[derive(Debug, Clone, PartialEq)]
pub struct FieldDescriptor {
    pub name: String,
    pub kind: TypeDescriptor,
}

impl FieldDescriptor {
    pub fn new(name: String, kind: TypeDescriptor) -> Self {
        Self { name, kind }
    }
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub struct Archetype {
    pub name: String,
}

impl std::fmt::Debug for Archetype {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.name)
    }
}

impl Display for Archetype {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Archetype {
    pub fn new(name: String) -> Self {
        Self { name }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct TypeDecl {
    pub name: String,
    pub kind_id: u32,
    pub archetypes: HashSet<Archetype>,
}

impl TypeDecl {
    pub fn new(name: String, kind_id: u32) -> Self {
        Self {
            name,
            kind_id,
            archetypes: HashSet::new(),
        }
    }

    pub fn implements_archetype(&self, arch: &Archetype) -> bool {
        self.archetypes.contains(arch)
    }

    pub fn add_archetype(&mut self, arch: Archetype) {
        self.archetypes.insert(arch);
    }
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct TypeDescriptor {
    pub name: String,
    pub id: u32,
    pub archetypes: HashSet<Archetype>,
    pub fields: HashMap<String, FieldDescriptor>,
}

impl TypeDescriptor {
    pub fn new(
        name: String,
        archetypes: HashSet<Archetype>,
        fields: HashMap<String, FieldDescriptor>,
        id: u32
    ) -> Self {
        Self {
            name,
            archetypes,
            fields,
            id,
        }
    }

    pub fn from_type_decl(decl: TypeDecl) -> Self {
        Self {
            archetypes: decl.archetypes,
            fields: HashMap::new(),
            name: decl.name,
            id: decl.kind_id,
        }
    }

    pub fn from_type_decl_with_fields(
        decl: TypeDecl,
        fields: HashMap<String, FieldDescriptor>
    ) -> Self {
        Self {
            archetypes: decl.archetypes,
            fields,
            name: decl.name,
            id: decl.kind_id,
        }
    }

    pub fn implements_archetype(&self, archetype: &Archetype) -> bool {
        self.archetypes.contains(archetype)
    }

    pub fn empty() -> TypeDescriptor {
        TypeDescriptor {
            name: String::new(),
            id: 0,
            archetypes: HashSet::new(),
            fields: HashMap::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionPrototype {
    pub name: String,
    pub params: Vec<FieldDeclaration>,
    pub arity: usize,
    pub return_kind: TypeDescriptor,
}

impl FunctionPrototype {
    pub fn new(
        name: String,
        params: Vec<FieldDeclaration>,
        arity: usize,
        return_kind: TypeDescriptor
    ) -> Self {
        Self {
            name,
            params,
            arity,
            return_kind,
        }
    }
}

impl std::hash::Hash for FunctionPrototype {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

#[derive(Debug, Clone)]
pub enum AnnotatedExpression {
    Literal(Token, TypeDescriptor),
    Unary(Token, Box<AnnotatedExpression>, TypeDescriptor),
    Group(Box<AnnotatedExpression>, TypeDescriptor),
    Arithmetic(Box<AnnotatedExpression>, Token, Box<AnnotatedExpression>, TypeDescriptor),
    Logical(Box<AnnotatedExpression>, Token, Box<AnnotatedExpression>, TypeDescriptor),
    Assign(Token, Box<AnnotatedExpression>, TypeDescriptor),
    Get(Box<AnnotatedExpression>, Token, TypeDescriptor),
    Variable(Token, TypeDescriptor),
    Call(FunctionPrototype, Token, Vec<Box<AnnotatedExpression>>, TypeDescriptor),
    CallNative(FunctionPrototype, Token, Vec<Box<AnnotatedExpression>>, TypeDescriptor),
    List(Vec<Box<AnnotatedExpression>>, TypeDescriptor),
    TypeComposition(TypeDescriptor),
    Attribute(Token, Vec<Box<AnnotatedExpression>>),
    Void,
}

#[derive(Debug, Clone)]
pub enum AnnotatedStatement {
    If(Token, AnnotatedExpression, Box<AnnotatedStatement>, Option<Box<AnnotatedStatement>>),
    ForEach(Token, AnnotatedExpression, Box<AnnotatedStatement>),
    Variable(Token, Option<AnnotatedExpression>),
    Type(TypeDescriptor),
    Function(FunctionPrototype, Box<AnnotatedStatement>),
    NativeFunction(FunctionPrototype),
    Scope(Vec<Box<AnnotatedStatement>>),
    Return(Option<AnnotatedExpression>),
    Decorator(Token, Vec<AnnotatedExpression>),
    Expression(AnnotatedExpression),
    While(AnnotatedExpression, Box<AnnotatedStatement>),
    Global,
    EndCode,
}
