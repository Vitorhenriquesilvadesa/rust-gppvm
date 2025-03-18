#![allow(warnings)]

use crate::gpp_error;
use std::{
    cmp::Ordering,
    collections::{ HashMap, HashSet },
    env,
    fmt::{ write, Display },
    process,
    string,
};

use super::{
    lexer::{ Literal, OperatorKind, PunctuationKind, Token, TokenKind },
    parser::{ Expression, FieldDeclaration, Statement },
};

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
struct Archetype {
    name: String,
}

impl Display for Archetype {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Archetype {
    fn new(name: String) -> Self {
        Self { name }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldDescriptor {
    name: String,
    kind: TypeDescriptor,
}

impl FieldDescriptor {
    pub fn new(name: String, kind: TypeDescriptor) -> Self {
        Self { name, kind }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeDescriptor {
    name: String,
    id: u32,
    archetypes: HashSet<Archetype>,
    fields: HashMap<String, FieldDescriptor>,
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

    fn implements_archetype(&self, archetype: &Archetype) -> bool {
        self.archetypes.contains(archetype)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct TypeDecl {
    name: String,
    kind_id: u32,
    archetypes: HashSet<Archetype>,
}

impl TypeDecl {
    fn new(name: String, kind_id: u32) -> Self {
        Self {
            name,
            kind_id,
            archetypes: HashSet::new(),
        }
    }

    fn implements_archetype(&self, arch: &Archetype) -> bool {
        self.archetypes.contains(arch)
    }

    fn add_archetype(&mut self, arch: Archetype) {
        self.archetypes.insert(arch);
    }
}

#[derive(Clone, Debug)]
struct SemanticValue {
    kind: Option<TypeDescriptor>,
    value: Value,
    line: usize,
}

impl SemanticValue {
    fn new(kind: Option<TypeDescriptor>, value: Value, line: usize) -> Self {
        Self { kind, value, line }
    }
}

#[derive(Clone, Debug)]
struct StaticValue {
    kind: TypeDescriptor,
    value: Value,
}

impl StaticValue {
    fn new(kind: TypeDescriptor, value: Value) -> Self {
        Self { kind, value }
    }
}

#[derive(Debug, Clone)]
struct ContextScope {
    names: HashMap<String, SemanticValue>,
}

impl ContextScope {
    fn new() -> Self {
        Self {
            names: HashMap::new(),
        }
    }

    pub fn contains_name(&self, name: &String) -> bool {
        self.names.contains_key(name)
    }

    fn name(&self, name: &String) -> Option<SemanticValue> {
        if self.contains_name(name) { Some(self.names.get(name).unwrap().clone()) } else { None }
    }

    fn set_infered_kind(&mut self, name: &String, kind: TypeDescriptor) {
        self.names.get_mut(name).unwrap().kind = Some(kind);
    }

    fn declare_name(&mut self, name: String, value: SemanticValue) {
        self.names.insert(name, value);
    }
}

#[derive(Debug, Clone)]
struct ContextStack {
    scopes: Vec<ContextScope>,
}

impl ContextStack {
    fn new() -> Self {
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

    fn peek(&mut self) -> &mut ContextScope {
        self.scopes.last_mut().unwrap()
    }

    fn get(&mut self, i: usize) -> &mut ContextScope {
        self.scopes.get_mut(i).unwrap()
    }
}

#[derive(Eq, PartialEq)]
enum SymbolKind {
    Function,
    Kind,
    None,
}

pub struct SemanticAnalyzer {
    statements: Vec<Statement>,
    context_stack: ContextStack,
    symbol_table: SymbolTable,
    current_stmt: usize,
    current_symbol: String,
    current_static_id: u32,
    current_symbol_kind: SymbolKind,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionPrototype {
    name: String,
    params: Vec<FieldDeclaration>,
    arity: usize,
    return_kind: TypeDescriptor,
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

#[derive(Debug, Clone)]
pub enum AnnotatedExpression {}

#[derive(Debug, Clone)]
pub enum AnnotatedStatement {
    // region:  --- Statements
    If(Token, AnnotatedExpression, Box<AnnotatedStatement>, Option<Box<AnnotatedStatement>>),
    While(AnnotatedExpression, Box<AnnotatedStatement>),
    ForEach(Token, AnnotatedExpression, Box<AnnotatedStatement>),
    Expression(AnnotatedExpression),
    Match,
    Scope(Vec<Box<AnnotatedStatement>>),
    Import(Token),
    Return(AnnotatedExpression, FunctionPrototype),
    // endregion:  --- Statements

    // region:  --- Declarations
    Decorator(Token, Vec<AnnotatedExpression>),
    Type(Token, Vec<Token>, Vec<FieldDeclaration>),
    Function(Token, Vec<FieldDeclaration>, Box<AnnotatedStatement>, AnnotatedExpression),
    Global,
    Variable(Token, Option<AnnotatedExpression>),
    // endregion:  --- Statements

    // region:  --- For Compiler
    EndCode, // endregion:  --- For Compiler
}

impl std::hash::Hash for FunctionPrototype {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

#[derive(Clone, Debug)]
pub struct SymbolTable {
    names: HashMap<String, StaticValue>,
    functions: HashMap<String, FunctionPrototype>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            names: HashMap::new(),
            functions: HashMap::new(),
        }
    }

    fn define(&mut self, name: String, value: StaticValue) {
        self.names.insert(name, value);
    }

    fn get(&self, name: &str) -> Option<&StaticValue> {
        self.names.get(name)
    }

    fn get_function(&mut self, name: &str) -> Option<&mut FunctionPrototype> {
        self.functions.get_mut(name)
    }

    fn define_function(&mut self, name: String, value: FunctionPrototype) {
        self.functions.insert(name, value);
    }
}

#[derive(Debug, Clone)]
pub struct SemanticCode {
    table: SymbolTable,
    statements: Vec<AnnotatedStatement>,
}

impl SemanticCode {
    pub fn new(table: SymbolTable, statements: Vec<AnnotatedStatement>) -> Self {
        SemanticCode { table, statements }
    }

    pub fn get_table(&self) -> &SymbolTable {
        &self.table
    }
}

impl SemanticAnalyzer {
    pub fn new() -> Self {
        let mut analyzer = Self {
            statements: Vec::new(),
            context_stack: ContextStack::new(),
            current_stmt: 0,
            current_symbol: String::new(),
            symbol_table: SymbolTable::new(),
            current_static_id: 0u32,
            current_symbol_kind: SymbolKind::None,
        };

        analyzer.initialize_predefined_types();

        analyzer
    }

    fn get_static_id(&mut self) -> u32 {
        self.current_static_id += 1;
        self.current_static_id
    }

    fn initialize_predefined_types(&mut self) {
        self.create_and_define_type("object", vec![]);
        self.create_and_define_type("bool", vec![]);
        self.create_and_define_type("number", vec![]);

        let number_descriptor = self.get_static_kind("number");
        self.add_field_to_defined_type("mod", &number_descriptor, &number_descriptor);

        self.create_and_define_type("float", vec!["number"]);
        self.create_and_define_type("int", vec!["number"]);

        let int_descriptor = self.get_static_kind("int");

        self.create_and_define_type("iterator", vec![]);
        let iterator_descriptor = self.get_static_kind("iterator");

        self.add_field_to_defined_type("length", &iterator_descriptor, &int_descriptor);

        self.create_and_define_type("str", vec!["iterator"]);
        self.create_and_define_type("tuple", vec!["iterator"]);
        self.create_and_define_type("list", vec!["iterator"]);
    }

    fn add_field_to_defined_type(
        &mut self,
        name: &str,
        target_descriptor: &TypeDescriptor,
        field_descriptor: &TypeDescriptor
    ) {
        let fields = &mut self.symbol_table.names
            .get_mut(&target_descriptor.name)
            .unwrap().kind.fields;

        fields.insert(
            name.to_string(),
            FieldDescriptor::new(field_descriptor.name.clone(), field_descriptor.clone())
        );
    }

    fn create_and_define_type(&mut self, name: &str, archetypes: Vec<&str>) {
        let mut type_decl = TypeDecl::new(name.to_string(), self.get_static_id());

        if "object".cmp(&type_decl.name) != Ordering::Equal {
            type_decl.add_archetype(Archetype::new("object".to_string()));
        }

        type_decl.add_archetype(Archetype::new(name.to_string().clone()));

        for archetype_name in &archetypes {
            type_decl.add_archetype(Archetype::new(archetype_name.to_string()));
        }

        let mut type_descriptor = TypeDescriptor::from_type_decl(type_decl);

        for archetype_name in &archetypes {
            let kind = self.get_static_kind(&archetype_name);

            for (name, field_descriptor) in &kind.fields {
                type_descriptor.fields.insert(name.clone(), field_descriptor.clone());
            }
        }

        let static_value = StaticValue::new(type_descriptor, Value::Kind);
        self.define_symbol(name.to_string(), static_value);
    }

    fn define_symbol(&mut self, name: String, value: StaticValue) {
        self.symbol_table.define(name, value);
    }

    pub fn analyze(&mut self, statements: Vec<Statement>) -> SemanticCode {
        self.reset_internal_state(statements);

        let mut stmt: Statement;

        let mut annotated_stmts: Vec<AnnotatedStatement> = Vec::new();

        while !self.is_at_end() {
            stmt = self.current().unwrap().clone();
            annotated_stmts.push(self.analyze_stmt(stmt));
            self.advance();
        }

        if self.get_function("main") == None {
            gpp_error!("Missing 'main' function.");
        }

        SemanticCode::new(self.symbol_table.clone(), annotated_stmts)
    }

    fn analyze_stmt(&mut self, stmt: Statement) -> AnnotatedStatement {
        match stmt {
            Statement::Return(value) => self.analyze_return(value),
            Statement::Expression(expr) => self.analyze_expr_stmt(expr.clone()),
            Statement::Decorator(hash_token, attribs) => {
                self.analyze_decorator(hash_token, attribs.clone())
            }
            Statement::Type(name, archetypes, fields) => {
                self.analyze_type(name, archetypes, fields)
            }
            Statement::Function(name, params, body, return_kind) => {
                self.analyze_function(name, params, *body, return_kind)
            }
            Statement::Variable(name, value) => self.analyze_variable_declaration(name, value),
            Statement::ForEach(variable, condition, body) => {
                self.analyze_iterator(variable, condition, *body)
            }
            Statement::If(keyword, condition, body, else_branch) => {
                self.analyze_if_stmt(keyword, condition, body, else_branch)
            }
            _ => gpp_error!("Statement {:?} not supported.", stmt),
        }
    }

    fn analyze_iterator(&mut self, variable: Token, condition: Expression, body: Statement) {
        self.begin_scope();

        match condition.clone() {
            Expression::Variable(variable) => {
                self.assert_archetype_kind(
                    condition,
                    self.get_static_kind("iterator"),
                    "Expect iterator in 'for' loop.".to_string()
                );
            }

            Expression::Call(callee, paren, args) => {
                let kind = self.resolve_function_return_type(callee, paren, args);
                self.assert_kind_equals(
                    kind,
                    self.get_static_kind("iterator"),
                    "Expect iterator in for each declaration.".to_string()
                );
            }

            _ => {
                let iterator_kind: TypeDescriptor = self.resolve_iterator_kind(condition);
            }
        }

        match body {
            Statement::Scope(stmts) => {
                for stmt in stmts {
                    self.analyze_stmt(*stmt);
                }
            }
            _ => gpp_error!("Statement {:?} is not allowed here.", body),
        }

        self.end_scope();
    }

    fn analyze_variable_declaration(&mut self, name: Token, value: Option<Expression>) {
        let ctx_name = self.context().name(&name.lexeme);

        match ctx_name {
            Some(sm) =>
                gpp_error!(
                    "The name '{}' was previous declared in current scope.\nPrevious declaration at line {}.\nMultiple declarations of '{}' within the same scope are not allowed.",
                    name.lexeme,
                    sm.line,
                    name.lexeme
                ),
            None => {
                match value {
                    Some(expr) => {
                        self.analyze_expr(expr.clone());

                        let value = SemanticValue::new(
                            Some(self.resolve_expr_type(expr)),
                            Value::Internal,
                            name.line
                        );
                        let mut context = &mut self.context();
                        context.declare_name(name.lexeme, value);
                    }
                    None => {
                        let value = SemanticValue::new(None, Value::Internal, name.line);
                        let mut context = &mut self.context();
                        context.declare_name(name.lexeme, value);
                    }
                }
            }
        }
    }

    fn analyze_type(&mut self, name: Token, archetypes: Vec<Token>, fields: Vec<FieldDeclaration>) {
        self.require_depth(
            Ordering::Less,
            1,
            format!("Type declarations are only allowed in top level code. At line {}.", name.line)
        );

        if let Some(kind) = self.symbol_table.names.get(&name.lexeme) {
            gpp_error!("Duplicated type definition for '{}'. At line {}.", name.lexeme, name.line);
        }

        self.current_symbol_kind = SymbolKind::Kind;

        let mut decl = TypeDecl::new(name.lexeme.clone(), self.get_static_id());
        decl.add_archetype(Archetype::new("object".to_string()));
        decl.add_archetype(Archetype::new(name.lexeme.clone()));

        for archetype in archetypes {
            let kind = self.get_static_kind(&archetype.lexeme).archetypes.clone();

            for kind_arch in kind {
                decl.add_archetype(kind_arch);
            }
        }

        let mut type_fields: HashMap<String, FieldDescriptor> = HashMap::new();

        for field in &fields {
            if let Expression::TypeComposition(mask) = field.kind.clone() {
                let kind = self.resolve_type_composition(mask);
                let archetypes: Vec<Archetype> = kind.archetypes.clone().into_iter().collect();

                for archetype in archetypes {
                    self.get_static_kind(&archetype.name);
                }

                if type_fields.contains_key(&field.name.lexeme) {
                    gpp_error!(
                        "Field '{}' already declared at this point. At line {}.",
                        field.name.lexeme,
                        field.name.line
                    );
                }

                type_fields.insert(
                    field.name.lexeme.clone(),
                    FieldDescriptor::new(field.name.lexeme.clone(), kind.clone())
                );
            }
        }

        let type_descriptor = TypeDescriptor::from_type_decl_with_fields(decl, type_fields.clone());

        self.define_type(type_descriptor);

        let constructor = FunctionPrototype::new(
            name.lexeme.clone(),
            fields.clone(),
            type_fields.len(),
            self.get_user_defined_kind(name.lexeme.clone())
        );

        self.define_function(name.lexeme.clone(), constructor);
    }

    fn define_type(&mut self, descriptor: TypeDescriptor) {
        self.symbol_table.define(
            descriptor.name.clone(),
            StaticValue::new(descriptor, Value::Internal)
        );
    }

    fn analyze_function(
        &mut self,
        name: Token,
        params: Vec<FieldDeclaration>,
        body: Statement,
        return_kind: Expression
    ) {
        self.require_depth(
            Ordering::Less,
            1,
            format!("Functions are only allowed in top level code. At line {}.", name.line)
        );

        self.current_symbol_kind = SymbolKind::Function;

        let mut kind: TypeDescriptor;

        if let Expression::TypeComposition(mask) = return_kind {
            kind = self.resolve_type_composition(mask);
        } else {
            gpp_error!("Missing function return kind.");
        }

        let function_definition = FunctionPrototype::new(
            name.lexeme.clone(),
            params.clone(),
            params.len(),
            kind.clone()
        );

        self.define_function(name.lexeme.clone(), function_definition.clone());

        self.current_symbol = name.lexeme.clone();

        self.begin_scope();

        for arg in function_definition.params {
            let kind = self.resolve_expr_type(arg.kind);
            self.define_local(
                arg.name.lexeme.clone(),
                SemanticValue::new(Some(kind), Value::Internal, arg.name.line)
            );
        }

        match body {
            Statement::Scope(stmts) => {
                for stmt in stmts {
                    self.analyze_stmt(*stmt);
                }
            }
            _ => gpp_error!("Statement {:?} is not allowed here.", body),
        }

        self.end_scope();
    }

    fn require_depth(&mut self, comparator: Ordering, depth: usize, message: String) {
        let comparison_result = self.depth().cmp(&depth);

        if comparison_result != comparator {
            gpp_error!("{}", message);
        }
    }

    fn begin_scope(&mut self) {
        self.context_stack.push_empty();
    }

    fn end_scope(&mut self) {
        self.context_stack.pop();
    }

    fn analyze_decorator(&mut self, hash_token: Token, attributes: Vec<Expression>) {
        let next = self.next();

        match next {
            Statement::Function(name, params, body, return_kind) => {}
            _ =>
                gpp_error!(
                    "Decorators are only accepted in function signatures. \x1b[33mAt line {}.\x1b[0m\n\x1b[36mHint:\x1b[0m Move \x1b[32m'#[...]'\x1b[0m to before \x1b[35m'def {}(...) {{...}}'\x1b[0m",
                    hash_token.line,
                    self.current_symbol
                ),
        }
    }

    fn analyze_if_stmt(
        &mut self,
        keyword: Token,
        condition: Expression,
        body: Box<Statement>,
        else_branch: Option<Box<Statement>>
    ) {
        self.analyze_expr(condition.clone());
        self.assert_expression_kind(condition.clone(), self.get_static_kind("bool"), keyword);

        self.begin_scope();

        match *body {
            Statement::Scope(stmts) => {
                for stmt in stmts {
                    self.analyze_stmt(*stmt);
                }
            }
            _ => gpp_error!("Statement {:?} is not allowed here.", body),
        }

        self.end_scope();

        match else_branch {
            Some(stmt) =>
                match *stmt {
                    Statement::Scope(stmts) => {
                        self.begin_scope();

                        for stmt in stmts {
                            self.analyze_stmt(*stmt);
                        }

                        self.end_scope();
                    }
                    _ => gpp_error!("Statement {:?} is not allowed here.", stmt),
                }

            None => {}
        }
    }

    fn analyze_expr(&mut self, expr: Expression) -> AnnotatedExpression {
        match expr.clone() {
            Expression::Void => {}
            Expression::Literal(token) => self.analyze_literal(token),
            Expression::Unary(token, expression) => self.check_operation_valid(token, expression),
            Expression::Arithmetic(left, op, right) => {
                self.analyze_arithmetic_expr(left, op, right)
            }
            Expression::Logical(left, op, right) => self.analyze_logical_expr(*left, op, *right),
            Expression::Ternary(expression, expression1, expression2) => todo!(),
            Expression::Assign(token, expression) => {
                self.analyze_assignment_expr(token, expression)
            }
            Expression::Lambda => todo!(),
            Expression::Get(expression, token) => self.analyze_get_expr(expression, token),
            Expression::Variable(token) => self.analyze_variable_get_expr(token),
            Expression::Set(expression, token, expression1) => todo!(),
            Expression::Call(callee, paren, args) => {
                self.analyze_call_expression(callee, paren, args)
            }
            Expression::Tuple(expressions) => todo!(),
            Expression::List(expressions) => self.analyze_collection(expr),
            Expression::TypeComposition(names) => todo!(),
            Expression::Attribute(token, expressions) => todo!(),
            Expression::Group(expression) => self.analyze_expr(*expression.clone()),
        }
    }

    fn next(&self) -> Statement {
        match self.statements.get(self.current_stmt + 1) {
            None => Statement::EndCode,
            Some(stmt) => stmt.clone(),
        }
    }

    fn is_at_end(&self) -> bool {
        match self.current() {
            None => true,
            Some(stmt) =>
                match stmt {
                    Statement::EndCode => true,
                    _ => false,
                }
        }
    }

    fn current(&self) -> Option<&Statement> {
        self.statements.get(self.current_stmt)
    }

    fn previous(&self) -> Option<&Statement> {
        self.statements.get(self.current_stmt - 1)
    }

    fn advance(&mut self) -> Option<&Statement> {
        self.current_stmt += 1;
        self.previous()
    }

    fn reset_internal_state(&mut self, statements: Vec<Statement>) {
        self.statements = statements;
        self.context_stack = ContextStack::new();
        self.current_stmt = 0;
    }

    fn depth(&self) -> usize {
        self.context_stack.len()
    }

    fn context(&mut self) -> &mut ContextScope {
        self.context_stack.peek()
    }

    fn check_operation_valid(&mut self, token: Token, expression: Box<Expression>) {
        match token.kind {
            TokenKind::Operator(op) =>
                match op {
                    OperatorKind::Minus => {
                        let expr_type = self.resolve_expr_type(*expression.clone());

                        self.assert_archetype_kind(
                            *expression.clone(),
                            self.get_static_kind("number"),
                            "'-' operator only be applyed in numbers.".to_string()
                        );
                    }

                    OperatorKind::Not => {
                        let expr_type = self.resolve_expr_type(*expression.clone());

                        if expr_type.id != self.get_static_kind_id("bool") {
                            gpp_error!(
                                "Cannot apply 'not' operator in a '{}' instance. At line {}.",
                                expr_type.name,
                                token.line
                            );
                        }
                    }
                    _ => {}
                }

            _ => gpp_error!("Invalid unary operation at line {}.", token.line),
        }
    }

    fn resolve_expr_type(&mut self, expression: Expression) -> TypeDescriptor {
        match expression {
            Expression::List(elements) => self.get_static_kind("list"),
            Expression::Literal(token) =>
                match token.kind {
                    TokenKind::Identifier => self.resolve_identifier_type(token),
                    TokenKind::Literal(literal) =>
                        match literal {
                            Literal::String => self.get_symbol("str").unwrap().kind.clone(),
                            Literal::Float => self.get_symbol("float").unwrap().kind.clone(),
                            Literal::Int => self.get_symbol("int").unwrap().kind.clone(),
                            Literal::Boolean => self.get_symbol("bool").unwrap().kind.clone(),
                        }
                    _ => gpp_error!("Expect literal in line {}.", token.line),
                }
            Expression::Unary(_, expression) => self.resolve_expr_type(*expression),
            Expression::Arithmetic(left, op, right) => {
                if let TokenKind::Operator(operator) = op.kind {
                    match operator {
                        | OperatorKind::Plus
                        | OperatorKind::Minus
                        | OperatorKind::Star
                        | OperatorKind::Slash => {
                            return self.resolve_expr_type(*left);
                        }

                        | OperatorKind::Greater
                        | OperatorKind::GreaterEqual
                        | OperatorKind::Less
                        | OperatorKind::LessEqual
                        | OperatorKind::EqualEqual => {
                            return self.get_static_kind("bool");
                        }

                        _ => gpp_error!("Invalid arithmetic operator."),
                    }
                }

                gpp_error!("Invalid arithmetic operator.");
            }
            Expression::Logical(left, _, _) => {
                let left_type = self.resolve_expr_type(*left);

                if left_type != self.get_symbol("bool").unwrap().kind {
                    gpp_error!("Expected boolean type for logical expression.");
                }
                left_type
            }
            Expression::Ternary(cond, true_expr, false_expr) => {
                let cond_type = self.resolve_expr_type(*cond);
                let true_type = self.resolve_expr_type(*true_expr);
                let false_type = self.resolve_expr_type(*false_expr);

                if true_type != false_type {
                    gpp_error!("Types of both branches of the ternary expression must match.");
                }
                true_type
            }
            Expression::Variable(name) => self.resolve_identifier_type(name),
            Expression::Assign(_, expr) => self.resolve_expr_type(*expr),
            Expression::Lambda => { gpp_error!("Lambda expressions are currently not supported.") }
            Expression::TypeComposition(mask) => self.resolve_type_composition(mask),
            Expression::Call(callee, paren, args) => {
                self.resolve_function_return_type(callee, paren, args)
            }
            Expression::Get(object, token) => self.resolve_get_expr(object, token),
            Expression::Group(expression) => self.resolve_expr_type(*expression.clone()),
            _ => gpp_error!("Expression {expression:?} are not supported."),
        }
    }

    fn get_symbol(&self, name: &str) -> Option<&StaticValue> {
        self.symbol_table.get(name)
    }

    fn get_static_kind_id(&self, name: &str) -> u32 {
        self.symbol_table.get(name).unwrap().kind.id
    }

    fn resolve_identifier_type(&mut self, token: Token) -> TypeDescriptor {
        self.require_depth(
            Ordering::Greater,
            0,
            format!(
                "Get identifier value is only allowed inside functions. At line {}.",
                token.line
            )
        );

        let mut i = self.context_stack.len() - 1;

        loop {
            match self.context_stack.get(i).name(&token.lexeme) {
                Some(symbol) =>
                    match symbol.kind {
                        Some(kind) => {
                            return kind;
                        }
                        None =>
                            gpp_error!(
                                "The kind of '{}' are not known here. At line {}.",
                                token.lexeme,
                                token.line
                            ),
                    }
                None => {
                    i -= 1;
                    continue;
                }
            }
        }

        gpp_error!("The name '{}' are not declared here. At line {}.", token.lexeme, token.line);
    }

    fn get_name_in_depth(&mut self, name: &Token) -> Option<SemanticValue> {
        let mut i = self.context_stack.len() - 1;

        loop {
            match self.context_stack.get(i).name(&name.lexeme) {
                Some(symbol) => {
                    return Some(symbol);
                }
                None => {
                    if i == 0 {
                        break;
                    }
                    i -= 1;
                    continue;
                }
            }
        }

        gpp_error!("The name '{}' are not declared here. At line {}.", name.lexeme, name.line);
    }

    fn analyze_assignment_expr(&mut self, token: Token, expression: Box<Expression>) {
        let symbol = self.get_name_in_depth(&token);

        match symbol {
            Some(sv) => {
                self.analyze_expr(*expression.clone());

                let value_type = self.resolve_expr_type(*expression.clone());
                let symbol_type = sv.kind;

                match symbol_type {
                    Some(kind) => {
                        if kind.id != value_type.id {
                            gpp_error!(
                                "Cannot assign '{}' with '{}' instance. At line {}.",
                                kind.name,
                                value_type.name,
                                token.line
                            );
                        }
                    }
                    None => {
                        self.context().set_infered_kind(&token.lexeme, value_type);
                    }
                }
            }
            None => gpp_error!("The name '{}' are not declared here.", token.lexeme),
        }
    }

    fn assert_expression_kind(
        &mut self,
        expr: Expression,
        expected_kind: TypeDescriptor,
        location: Token
    ) {
        let expr_kind = self.resolve_expr_type(expr);

        if expr_kind.id != expected_kind.id {
            gpp_error!(
                "Expect '{}', but got '{}'. At line {}.",
                expected_kind.name,
                expr_kind.name,
                location.line
            );
        }
    }

    fn get_static_kind(&self, name: &str) -> TypeDescriptor {
        self.symbol_table.get(name).unwrap().kind.clone()
    }

    fn analyze_variable_get_expr(&self, token: Token) {}

    fn analyze_literal(&self, token: Token) {}

    fn analyze_arithmetic_expr(
        &mut self,
        left: Box<Expression>,
        token: Token,
        right: Box<Expression>
    ) {
        if !matches!(*left.clone(), Expression::Literal(literal)) {
            self.analyze_expr(*left.clone());
        }

        if !matches!(*right.clone(), Expression::Literal(literal)) {
            self.analyze_expr(*right.clone());
        }

        if let TokenKind::Operator(op) = token.kind {
            match op {
                | OperatorKind::Plus
                | OperatorKind::Minus
                | OperatorKind::Star
                | OperatorKind::Slash
                | OperatorKind::Greater
                | OperatorKind::GreaterEqual
                | OperatorKind::Less
                | OperatorKind::LessEqual => {
                    let left_kind = self.resolve_expr_type(*left.clone());
                    let right_kind = self.resolve_expr_type(*right.clone());

                    let msg = format!(
                        "Cannot apply arithmetic operation '{}' to '{}' and '{}'. At line {}.",
                        token.lexeme,
                        left_kind.name,
                        right_kind.name,
                        token.line
                    );

                    self.assert_archetype_kind(
                        *left.clone(),
                        self.get_static_kind("number"),
                        msg.clone()
                    );

                    self.assert_archetype_kind(
                        *right.clone(),
                        self.get_static_kind("number"),
                        msg.clone()
                    );
                }

                OperatorKind::EqualEqual => {
                    let expected_kind = self.resolve_expr_type(*left.clone());
                    self.assert_expression_kind(*right.clone(), expected_kind, token.clone());
                }

                _ =>
                    gpp_error!(
                        "Invalid arithmetic operator '{}'. At line {}.",
                        token.lexeme,
                        token.line
                    ),
            }
        }
    }

    fn is_same_kind(&self, a: TypeDecl, b: TypeDecl, msg: String) {
        if a.kind_id != b.kind_id {
            gpp_error!("{}", msg);
        }
    }

    /// Asserts that an expression's type conforms to a given archetype.
    ///
    /// # Parameters
    /// - `expr`: The expression whose type needs to be checked.
    /// - `archetype_source`: A `TypeDecl` representing the expected archetype(s).
    /// - `msg`: A custom error message to be included if the assertion fails.
    ///
    /// # Behavior
    /// - Resolves the type of the given expression.
    /// - Checks if the expression's type implements all required archetypes from `archetype_source`.
    /// - If the type does not conform, an error is raised with a detailed message.
    ///
    /// This function ensures that expressions match the expected type constraints, enforcing type safety.
    fn assert_archetype_kind(
        &mut self,
        expr: Expression,
        archetype_source: TypeDescriptor,
        msg: String
    ) {
        let expr_kind = self.resolve_expr_type(expr);

        let mut is_same = true;

        for archtype in archetype_source.archetypes.iter() {
            if !expr_kind.implements_archetype(archtype) {
                is_same = false;
            }
        }

        if !is_same {
            gpp_error!(
                "Expect {}, but got {}. Compiler message: {}",
                archetype_source.name,
                expr_kind.name,
                msg
            );
        }
    }

    /// Infers the type of a list based on its elements.
    ///
    /// # Parameters
    /// - `elements`: A slice of boxed expressions representing the elements of the list.
    ///
    /// # Returns
    /// - A `TypeDecl` representing the inferred type of the list.
    ///
    /// # Type Inference Process
    /// 1. If the list is empty, an error is raised because type inference is impossible.
    /// 2. If the list contains only one element, the type of that element is used as the list type.
    /// 3. Otherwise, the function:
    ///    - Resolves the type of each element.
    ///    - Collects all unique archetypes found across the elements.
    ///    - Identifies archetypes that are common to all elements.
    ///    - Determines the final list type based on these common archetypes.
    ///
    /// The inferred type is printed for debugging purposes before being returned.
    fn resolve_list_type(&mut self, elements: &[Box<Expression>]) -> TypeDescriptor {
        if elements.is_empty() {
            gpp_error!("Cannot infer type of empty list. At least one element is required.");
        }

        let first_type = self.resolve_expr_type(*elements[0].clone());

        if elements.len() == 1 {
            return first_type;
        }

        let mut common_archetypes: HashSet<Archetype> = first_type.archetypes.clone();

        for element in &elements[1..] {
            let element_type = self.resolve_expr_type(*element.clone());
            common_archetypes.retain(|arch| element_type.archetypes.contains(arch));
        }

        if common_archetypes.is_empty() {
            gpp_error!("Cannot infer list kind. No common archetypes found.");
        }

        let archetypes_vec: Vec<Archetype> = common_archetypes.into_iter().collect();

        let infered_type = self.get_by_archetype(&archetypes_vec);

        match infered_type {
            Some(kind) => {
                println!("Infered list kind: {}.", kind.name);
                kind
            }
            None => gpp_error!("Cannot find type with specified archetypes: {archetypes_vec:?}."),
        }
    }

    fn analyze_collection(&mut self, collection: Expression) {
        self.resolve_iterator_kind(collection);
    }

    fn analyze_call_expression(
        &mut self,
        callee: Box<Expression>,
        paren: Token,
        args: Vec<Expression>
    ) {
        if let Expression::Variable(name) = *callee {
            if self.current_symbol.clone() == name.lexeme.clone() {
                gpp_error!(
                    "Recursive calls are not allowed in current version. At line {}.",
                    name.line
                );
            }
            match self.get_function(&name.lexeme.clone()) {
                Some(prototype) => {
                    let prototype = prototype.clone();

                    if prototype.arity != args.len() {
                        gpp_error!(
                            "Expect {} arguments, but got {}. At line {}.",
                            prototype.arity,
                            args.len(),
                            paren.line
                        );
                    }

                    self.assert_function_args(prototype, args);
                }
                None =>
                    gpp_error!(
                        "Function '{}' are not declared in this scope.",
                        name.lexeme.clone()
                    ),
            }
        } else {
            gpp_error!("Call functions inside modules are currently not allowed.");
        }
    }

    fn define_function(&mut self, name: String, value: FunctionPrototype) {
        self.symbol_table.define_function(name, value);
    }

    fn resolve_function_return_type(
        &mut self,
        callee: Box<Expression>,
        paren: Token,
        args: Vec<Expression>
    ) -> TypeDescriptor {
        if let Expression::Variable(name) = *callee {
            let function = self.symbol_table.get_function(&name.lexeme.clone());

            match function {
                Some(prototype) => {
                    return prototype.return_kind.clone();
                }
                None =>
                    gpp_error!(
                        "Function '{}' are not declared in this scope.",
                        name.lexeme.clone()
                    ),
            }
        } else {
            gpp_error!("Call functions inside modules are currently not allowed.");
        }
    }

    fn assert_function_args(&mut self, prototype: FunctionPrototype, args: Vec<Expression>) {
        for (index, arg) in args.iter().enumerate() {
            let proto_arg_kind = self.resolve_expr_type(prototype.params[index].kind.clone());
            let passed_arg_kind = self.resolve_expr_type(arg.clone());

            self.assert_archetype_kind(
                arg.clone(),
                proto_arg_kind.clone(),
                format!(
                    "Expect '{}' to '{}' param, but got '{}'.",
                    proto_arg_kind.name,
                    prototype.params[index].name.lexeme,
                    passed_arg_kind.name
                ).to_string()
            );
        }
    }

    fn get_function(&mut self, name: &str) -> Option<&mut FunctionPrototype> {
        self.symbol_table.get_function(name)
    }

    fn resolve_type(&self, path: Vec<Token>) -> TypeDescriptor {
        if path.len() != 1 {
            gpp_error!("Modules are currently not supported. At line {}.", path[0].line);
        } else {
            self.get_static_kind(&path.first().unwrap().lexeme)
        }
    }

    fn define_local(&mut self, name: String, value: SemanticValue) {
        self.context().declare_name(name, value);
    }

    fn resolve_iterator_kind(&mut self, iterator: Expression) -> TypeDescriptor {
        let expr_kind = self.resolve_expr_type(iterator.clone());

        match iterator {
            Expression::List(elements) => self.resolve_list_type(&elements),
            Expression::Call(callee, paren, args) => {
                self.analyze_call_expression(callee.clone(), paren.clone(), args.clone());
                self.resolve_function_return_type(callee, paren, args)
            }
            _ => {
                gpp_error!("Expect list, but got {:?}.", iterator);
            }
        }
    }

    fn get_by_archetype(&mut self, sets: &[Archetype]) -> Option<TypeDescriptor> {
        let target_set: HashSet<_> = sets.iter().cloned().collect();

        match self.symbol_table.names.iter().find(|decl| decl.1.kind.archetypes == target_set) {
            Some((name, value)) => Some(value.kind.clone()),
            None => None,
        }
    }

    fn analyze_logical_expr(&mut self, left: Expression, op: Token, right: Expression) {
        self.assert_expression_kind(left, self.get_static_kind("bool"), op.clone());
        self.assert_expression_kind(right, self.get_static_kind("bool"), op.clone());
    }

    fn resolve_type_composition(&mut self, mask: Vec<Token>) -> TypeDescriptor {
        let mut archetypes = HashSet::<Archetype>::new();

        archetypes.insert(Archetype::new("object".to_string()));

        for name in &mask {
            let matched: Vec<Archetype> = self
                .get_static_kind(&name.lexeme)
                .archetypes.into_iter()
                .collect();

            for archetype in matched {
                archetypes.insert(archetype.clone());
            }
        }

        let archetypes: Vec<Archetype> = archetypes.into_iter().collect();

        match self.get_by_archetype(&archetypes) {
            None => gpp_error!("Cannot find type to match with specified archetype."),
            Some(kind) => kind,
        }
    }

    fn analyze_return(&mut self, value: Expression) -> AnnotatedStatement {
        self.require_depth(
            Ordering::Greater,
            0,
            "Return statement are only allowed inside functions.".to_string()
        );

        if self.current_symbol_kind != SymbolKind::Function {
            gpp_error!("Returns is only allowed inside functions.");
        }

        let function = self.current_symbol.clone();
        let return_kind = self.get_function(&function).unwrap().clone();

        let return_value = self.analyze_expr(value.clone());

        self.assert_archetype_kind(
            value,
            return_kind.return_kind.clone(),
            format!("Return of '{}' does not match with function signature.", function.clone())
        );

        AnnotatedStatement::Return(return_value, return_kind)
    }

    fn assert_kind_equals(&self, source: TypeDescriptor, target: TypeDescriptor, msg: String) {
        for i in target.archetypes {
            if !source.archetypes.contains(&i) {
                gpp_error!("{}", msg);
            }
        }
    }

    fn resolve_get_expr(&mut self, expression: Box<Expression>, token: Token) -> TypeDescriptor {
        let mut current_kind: Option<TypeDescriptor> = None;
        let mut current_expression = *expression.clone();
        let mut is_literal = false;

        let mut path = vec![token.clone()];

        while let Expression::Get(expr, name) = current_expression {
            path.push(name.clone());
            current_expression = *expr.clone();
        }

        if let Expression::Variable(name) = current_expression {
            path.push(name);
        } else {
            current_kind = Some(self.resolve_expr_type(current_expression).clone());
            is_literal = true;
        }

        let path: Vec<&Token> = path.iter().rev().collect();

        if is_literal {
            for (index, field) in path[0..].iter().enumerate() {
                current_kind = match &current_kind {
                    None => {
                        gpp_error!(
                            "{} cannot have '{}' field.",
                            path[index - 1],
                            field.lexeme.clone()
                        );
                    }

                    Some(type_descriptor) =>
                        match type_descriptor.fields.get(&field.lexeme) {
                            None => {
                                gpp_error!(
                                    "Variable '{}' is a '{}' instance and not have '{}' field.",
                                    path[index].lexeme.clone(),
                                    current_kind.unwrap().name,
                                    field.lexeme.clone()
                                );
                            }
                            Some(field_decl) => Some(field_decl.kind.clone()),
                        }
                };
            }
        } else {
            current_kind = match self.get_name_in_depth(&path[0]) {
                None => {
                    gpp_error!("The kind of {} is not known here.", &path[0].lexeme);
                }
                Some(semantic_value) => semantic_value.kind,
            };

            for (index, field) in path[1..].iter().enumerate() {
                current_kind = match &current_kind {
                    None => {
                        gpp_error!(
                            "{} cannot have '{}' field.",
                            path[index - 1],
                            field.lexeme.clone()
                        );
                    }

                    Some(type_descriptor) =>
                        match type_descriptor.fields.get(&field.lexeme) {
                            None => {
                                gpp_error!(
                                    "Variable '{}' is a '{}' instance and not have '{}' field.",
                                    path[index].lexeme.clone(),
                                    current_kind.unwrap().name,
                                    field.lexeme.clone()
                                );
                            }
                            Some(field_decl) => Some(field_decl.kind.clone()),
                        }
                };
            }
        }

        match &current_kind {
            None => gpp_error!("Not have field with name."),
            Some(kind) => self.get_static_kind(&kind.name),
        }
    }

    fn analyze_get_expr(&self, expression: Box<Expression>, token: Token) {}

    fn get_user_defined_kind(&self, name: String) -> TypeDescriptor {
        self.symbol_table.names.get(&name).unwrap().kind.clone()
    }

    fn check_type_exists(&self, name: &String) -> bool {
        self.symbol_table.names.contains_key(name)
    }

    fn analyze_expr_stmt(&mut self, expression: Expression) -> AnnotatedStatement {
        let expr = self.analyze_expr(expression);
        AnnotatedStatement::Expression(expr)
    }
}
