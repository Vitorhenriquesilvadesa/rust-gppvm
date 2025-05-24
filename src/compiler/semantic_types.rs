use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

use super::{ast::FieldDeclaration, lexer::Token};

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

    pub fn as_object(&self) -> Option<ObjectDescriptor> {
        if let Value::Object(v) = self {
            Some(v.clone())
        } else {
            None
        }
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

#[derive(Debug, Clone, PartialEq)]
pub struct FieldDescriptor {
    pub name: String,
    pub kind: TypeDescriptor,
    pub id: u8,
}

impl FieldDescriptor {
    pub fn new(name: String, kind: TypeDescriptor, id: u8) -> Self {
        Self { name, kind, id }
    }
}

#[derive(Debug, Clone, PartialEq)]
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
        id: u32,
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
        fields: HashMap<String, FieldDescriptor>,
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

#[derive(Debug, Clone)]
pub struct ContextScope {
    pub names: HashMap<String, SemanticValue>,
}

impl ContextScope {
    pub fn new() -> Self {
        Self {
            names: HashMap::new(),
        }
    }

    pub fn contains_name(&self, name: &String) -> bool {
        self.names.contains_key(name)
    }

    pub fn name(&self, name: &String) -> Option<SemanticValue> {
        if self.contains_name(name) {
            Some(self.names.get(name).unwrap().clone())
        } else {
            None
        }
    }

    pub fn set_infered_kind(&mut self, name: &String, kind: TypeDescriptor) {
        self.names.get_mut(name).unwrap().kind = Some(kind);
    }

    pub fn declare_name(&mut self, name: &str, value: SemanticValue) {
        self.names.insert(name.to_string().clone(), value);
    }
}

#[derive(Debug, Clone)]
pub struct ContextStack {
    pub scopes: Vec<ContextScope>,
}

impl ContextStack {
    pub fn new() -> Self {
        Self { scopes: Vec::new() }
    }

    pub fn push_empty(&mut self) {
        self.scopes.push(ContextScope::new());
    }

    pub fn pop(&mut self) {
        self.scopes.pop();
    }

    pub fn len(&self) -> usize {
        self.scopes.len()
    }

    pub fn peek(&mut self) -> &mut ContextScope {
        self.scopes.last_mut().unwrap()
    }

    pub fn get(&mut self, i: usize) -> &mut ContextScope {
        self.scopes.get_mut(i).unwrap()
    }
}

#[derive(Eq, PartialEq)]
pub enum SymbolKind {
    Function,
    Kind,
    None,
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

#[derive(Debug, Clone)]
pub enum AnnotatedExpression {
    Literal(Token, TypeDescriptor),
    Unary(Token, Box<AnnotatedExpression>, TypeDescriptor),
    Group(Box<AnnotatedExpression>, TypeDescriptor),
    Arithmetic(
        Box<AnnotatedExpression>,
        Token,
        Box<AnnotatedExpression>,
        TypeDescriptor,
    ),
    Logical(
        Box<AnnotatedExpression>,
        Token,
        Box<AnnotatedExpression>,
        TypeDescriptor,
    ),
    Assign(Token, Box<AnnotatedExpression>, TypeDescriptor),
    Get(Box<AnnotatedExpression>, Token, TypeDescriptor),
    Variable(Token, TypeDescriptor),
    Call(
        FunctionPrototype,
        Token,
        Vec<Box<AnnotatedExpression>>,
        TypeDescriptor,
    ),
    CallNative(
        FunctionPrototype,
        Token,
        Vec<Box<AnnotatedExpression>>,
        TypeDescriptor,
    ),
    List(Vec<Box<AnnotatedExpression>>, TypeDescriptor),
    TypeComposition(TypeDescriptor),
    Attribute(Token, Vec<Box<AnnotatedExpression>>),
    Void,
    PostFix(Token, Box<AnnotatedExpression>),
    Set(
        Box<AnnotatedExpression>,
        Token,
        Box<AnnotatedExpression>,
        TypeDescriptor,
    ),
    ListGet(Box<AnnotatedExpression>, Box<AnnotatedExpression>),
}

#[derive(Debug, Clone)]
pub enum AnnotatedStatement {
    If(
        Token,
        AnnotatedExpression,
        Box<AnnotatedStatement>,
        Option<Box<AnnotatedStatement>>,
    ),
    BuiltinAttribute(Token, Vec<TypeDescriptor>),
    ForEach(Token, AnnotatedExpression, Box<AnnotatedStatement>),
    Variable(Token, Option<AnnotatedExpression>),
    Type(TypeDescriptor),
    Function(FunctionPrototype, Box<AnnotatedStatement>),
    Scope(Vec<Box<AnnotatedStatement>>),
    Return(Option<AnnotatedExpression>),
    Decorator(Token, Vec<AnnotatedExpression>),
    Expression(AnnotatedExpression),
    While(AnnotatedExpression, Box<AnnotatedStatement>),
    Global,
    EndCode,
    NativeFunction(FunctionPrototype),
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
        return_kind: TypeDescriptor,
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

impl std::hash::Hash for BuiltinAttribute {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

#[derive(Clone, Debug)]
pub struct BuiltinAttribute {
    pub name: String,
    pub args: Vec<TypeDescriptor>,
}

impl BuiltinAttribute {
    pub fn new(name: String, args: Vec<TypeDescriptor>) -> Self {
        Self { name, args }
    }
}

#[derive(Clone, Debug)]
pub struct SymbolTable {
    pub names: HashMap<String, StaticValue>,
    pub functions: HashMap<String, FunctionPrototype>,
    pub native_functions: HashMap<String, FunctionPrototype>,
    pub attributes: HashMap<String, BuiltinAttribute>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            names: HashMap::new(),
            functions: HashMap::new(),
            native_functions: HashMap::new(),
            attributes: HashMap::new(),
        }
    }

    pub fn get_attribute(&self, name: String) -> Option<&BuiltinAttribute> {
        return self.attributes.get(&name);
    }

    pub fn define_attribute(&mut self, name: String, args: Vec<TypeDescriptor>) {
        self.attributes
            .insert(name.clone(), BuiltinAttribute::new(name, args));
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
