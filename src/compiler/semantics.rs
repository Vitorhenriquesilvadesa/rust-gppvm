#![allow(warnings)]

use crate::gpp_error;
use std::{ cmp::Ordering, collections::{ HashMap, HashSet }, string };

use super::{
    lexer::{ Literal, OperatorKind, PunctuationKind, Token, TokenKind },
    parser::{ Expression, FieldDeclaration, Statement },
};

#[derive(Debug, Clone, Copy)]
pub enum Value {
    Int(i32),
    Float(f32),
    Boolean(bool),
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
}

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
struct Archetype {
    name: String,
}

impl Archetype {
    fn new(name: String) -> Self {
        Self { name }
    }
}

#[derive(Clone, Debug, PartialEq)]
struct TypeDecl {
    name: String,
    kind_id: u32,
    archetypes: HashSet<Archetype>,
}

impl TypeDecl {
    fn new(name: String, kind_id: u32) -> Self {
        Self { name, kind_id, archetypes: HashSet::new() }
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
    kind: Option<TypeDecl>,
    value: Value,
    line: usize,
}

impl SemanticValue {
    fn new(kind: Option<TypeDecl>, value: Value, line: usize) -> Self {
        Self { kind, value, line }
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

#[derive(Clone)]
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

    fn set_infered_kind(&mut self, name: &String, kind: TypeDecl) {
        self.names.get_mut(name).unwrap().kind = Some(kind);
    }

    fn declare_name(&mut self, lexeme: String, value: SemanticValue) {
        self.names.insert(lexeme, value);
    }
}

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
}

pub struct SemanticAnalyzer {
    statements: Vec<Statement>,
    context_stack: ContextStack,
    symbol_table: SymbolTable,
    current_stmt: usize,
    current_symbol: String,
    current_static_id: u32,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionPrototype {
    name: String,
    params: Vec<FieldDeclaration>,
    arity: usize,
    return_kind: TypeDecl,
}

impl FunctionPrototype {
    pub fn new(
        name: String,
        params: Vec<FieldDeclaration>,
        arity: usize,
        return_kind: TypeDecl
    ) -> Self {
        Self { name, params, arity, return_kind }
    }
}

impl std::hash::Hash for FunctionPrototype {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

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

pub struct IntermediateCode {}

impl IntermediateCode {
    pub fn new() -> Self {
        IntermediateCode {}
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
        };

        analyzer.initialize_predefined_types();

        analyzer
    }

    fn get_static_id(&mut self) -> u32 {
        self.current_static_id += 1;
        self.current_static_id
    }

    fn initialize_predefined_types(&mut self) {
        self.create_and_define_type("bool", vec![]);
        self.create_and_define_type("str", vec!["iterator"]);
        self.create_and_define_type("float", vec![]);
        self.create_and_define_type("iterator", vec![]);
        self.create_and_define_type("list", vec!["iterator"]);
        self.create_and_define_type("tuple", vec!["iterator"]);
    }

    fn create_and_define_type(&mut self, name: &str, archetypes: Vec<&str>) {
        let mut type_decl = TypeDecl::new(name.to_string(), self.get_static_id());

        type_decl.add_archetype(Archetype::new(name.to_string().clone()));

        for archetype_name in archetypes {
            type_decl.add_archetype(Archetype::new(archetype_name.to_string()));
        }

        let static_value = StaticValue::new(type_decl, Value::Internal);
        self.define_symbol(name.to_string(), static_value);
    }

    fn define_symbol(&mut self, name: String, value: StaticValue) {
        self.symbol_table.define(name, value);
    }

    pub fn analyze(&mut self, statements: Vec<Statement>) -> IntermediateCode {
        self.reset_internal_state(statements);

        let mut stmt: Statement;

        while !self.is_at_end() {
            stmt = self.current().unwrap().clone();
            self.analyze_stmt(stmt);
            self.advance();
        }

        IntermediateCode::new()
    }

    fn analyze_stmt(&mut self, stmt: Statement) {
        match stmt {
            Statement::Expression(expr) => self.analyze_expr(expr.clone()),
            Statement::Decorator(hash_token, attribs) => {
                self.analyze_decorator(hash_token, attribs.clone())
            }
            Statement::Type(name, fields) => self.analyze_type(name, fields),
            Statement::Function(name, params, body, return_kind) =>
                self.analyze_function(name, params, *body, return_kind),
            Statement::Variable(name, value) => self.analyze_variable_declaration(name, value),
            Statement::ForEach(variable, condition, body) => {
                self.analyze_iterator(variable, condition, *body)
            }
            Statement::If(keyword, condition, body, else_branch) =>
                self.analyze_if_stmt(keyword, condition, body, else_branch),
            _ => gpp_error!("Statement {:?} not supported.", stmt),
        }
    }

    fn analyze_iterator(&mut self, variable: Token, condition: Expression, body: Statement) {
        self.assert_archetype_kind(
            condition,
            self.get_static_kind("iterator"),
            format!("Expect iterator. At line {}.", variable.line)
        );

        self.begin_scope();

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

    fn analyze_type(&mut self, name: Token, fields: Vec<FieldDeclaration>) {
        self.require_depth(
            Ordering::Less,
            1,
            format!("Type declarations are only allowed in top level code. At line {}.", name.line)
        );
    }

    fn analyze_function(
        &mut self,
        name: Token,
        params: Vec<FieldDeclaration>,
        body: Statement,
        return_kind: Token
    ) {
        self.require_depth(
            Ordering::Less,
            1,
            format!("Functions are only allowed in top level code. At line {}.", name.line)
        );

        let kind = self.get_static_kind(&return_kind.lexeme);

        let function_definition = FunctionPrototype::new(
            name.lexeme.clone(),
            params.clone(),
            params.len(),
            kind.clone()
        );

        self.define_function(name.lexeme.clone(), function_definition);

        self.current_symbol = name.lexeme.clone();
        self.begin_scope();

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

    fn analyze_expr(&mut self, expr: Expression) {
        match expr {
            Expression::Void => {}
            Expression::Literal(token) => self.analyze_literal(token),
            Expression::Unary(token, expression) => self.check_operation_valid(token, expression),
            Expression::Arithmetic(left, op, right) => {
                self.analyze_arithmetic_expr(left, op, right)
            }
            Expression::Logical(expression, op, expression1) => todo!(),
            Expression::Ternary(expression, expression1, expression2) => todo!(),
            Expression::Assign(token, expression) => {
                self.analyze_assignment_expr(token, expression)
            }
            Expression::Lambda => todo!(),
            Expression::Get(expression, token) => todo!(),
            Expression::Variable(token) => self.analyze_variable_get_expr(token),
            Expression::Set(expression, token, expression1) => todo!(),
            Expression::Call(callee, paren, args) => {
                self.analyze_call_expression(callee, paren, args)
            }
            Expression::Tuple(expressions) => todo!(),
            Expression::List(expressions) => self.analyze_collection(expressions),
            Expression::Type(tokens) => todo!(),
            Expression::Attribute(token, expressions) => todo!(),
            Expression::Group(expression) => todo!(),
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
            TokenKind::Operator(op) => {
                match op {
                    OperatorKind::Minus => {
                        let expr_type = self.resolve_expr_type(*expression.clone());

                        if expr_type.kind_id != self.get_static_kind_id("float") {
                            gpp_error!(
                                "Cannot apply '-' operator in a '{}' instance. At line {}.",
                                expr_type.name,
                                token.line
                            );
                        }
                    }

                    OperatorKind::Not => {
                        let expr_type = self.resolve_expr_type(*expression.clone());

                        if expr_type.kind_id != self.get_static_kind_id("bool") {
                            gpp_error!(
                                "Cannot apply 'not' operator in a '{}' instance. At line {}.",
                                expr_type.name,
                                token.line
                            );
                        }
                    }
                    _ => {}
                }
            }

            _ => gpp_error!("Invalid unary operation at line {}.", token.line),
        }
    }

    fn resolve_expr_type(&mut self, expression: Expression) -> TypeDecl {
        match expression {
            Expression::List(elements) => { self.resolve_list_type(elements) }
            Expression::Literal(token) => {
                match token.kind {
                    TokenKind::Identifier => { self.resolve_identifier_type(token) }
                    TokenKind::Literal(literal) => {
                        match literal {
                            Literal::String => self.get_symbol("str").unwrap().kind.clone(),
                            Literal::Number => self.get_symbol("float").unwrap().kind.clone(),
                            Literal::Boolean => self.get_symbol("bool").unwrap().kind.clone(),
                        }
                    }
                    _ => gpp_error!("Expect literal in line {}.", token.line),
                }
            }
            Expression::Unary(_, expression) => { self.resolve_expr_type(*expression) }
            Expression::Arithmetic(left, _, _) => { self.resolve_expr_type(*left) }
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
            Expression::Variable(name) => { self.resolve_identifier_type(name) }
            Expression::Assign(_, expr) => { self.resolve_expr_type(*expr) }
            Expression::Lambda => { gpp_error!("Lambda expressions are currently not supported.") }
            Expression::Type(path) => { self.resolve_type(path) }
            Expression::Call(callee, paren, args) =>
                self.resolve_function_return_type(callee, paren, args),
            _ => gpp_error!("Expression {expression:?} are not supported."),
        }
    }

    fn get_symbol(&self, name: &str) -> Option<&StaticValue> {
        self.symbol_table.get(name)
    }

    fn get_static_kind_id(&self, name: &str) -> u32 {
        self.symbol_table.get(name).unwrap().kind.kind_id
    }

    fn resolve_identifier_type(&mut self, token: Token) -> TypeDecl {
        match self.context().name(&token.lexeme) {
            Some(symbol) =>
                match symbol.kind {
                    Some(kind) => kind,
                    None =>
                        gpp_error!(
                            "The kind of '{}' are not known here. At line {}.",
                            token.lexeme,
                            token.line
                        ),
                }
            None =>
                gpp_error!(
                    "The name '{}' are not declared here. At line {}.",
                    token.lexeme,
                    token.line
                ),
        }
    }

    fn analyze_assignment_expr(&mut self, token: Token, expression: Box<Expression>) {
        let symbol = self.context().name(&token.lexeme);
        match symbol {
            Some(sv) => {
                self.analyze_expr(*expression.clone());

                let value_type = self.resolve_expr_type(*expression.clone());
                let symbol_type = sv.kind;

                match symbol_type {
                    Some(kind) => {
                        if kind.kind_id != value_type.kind_id {
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
        expected_kind: TypeDecl,
        location: Token
    ) {
        let expr_kind = self.resolve_expr_type(expr);

        if expr_kind.kind_id != expected_kind.kind_id {
            gpp_error!(
                "Expect '{}', but got '{}'. At line {}.",
                expected_kind.name,
                expr_kind.name,
                location.line
            );
        }
    }

    fn get_static_kind(&self, name: &str) -> TypeDecl {
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
        if let TokenKind::Operator(op) = token.kind {
            match op {
                | OperatorKind::Plus
                | OperatorKind::Minus
                | OperatorKind::Star
                | OperatorKind::Slash => {
                    let left_kind = self.resolve_expr_type(*left.clone());
                    let right_kind = self.resolve_expr_type(*right.clone());

                    let msg = format!(
                        "Cannot apply arithmetic operation '{}' to '{}' and '{}'. At line {}.",
                        token.lexeme,
                        left_kind.name,
                        right_kind.name,
                        token.line
                    );

                    self.is_same_kind(
                        left_kind.clone(),
                        self.get_static_kind("float"),
                        msg.clone()
                    );
                    self.is_same_kind(
                        right_kind.clone(),
                        self.get_static_kind("float"),
                        msg.clone()
                    );
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

    fn assert_archetype_kind(&mut self, expr: Expression, archetype_source: TypeDecl, msg: String) {
        let expr_kind = self.resolve_expr_type(expr);

        let mut is_same = true;

        for archtype in archetype_source.archetypes.iter() {
            if !expr_kind.implements_archetype(archtype) {
                is_same = false;
            }
        }

        if !is_same {
            gpp_error!("{}", msg);
        }
    }

    fn resolve_list_type(&self, elements: Vec<Box<Expression>>) -> TypeDecl {
        self.get_static_kind("list")
    }

    fn analyze_collection(&self, expressions: Vec<Box<Expression>>) {}

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
    ) -> TypeDecl {
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

    fn resolve_type(&self, path: Vec<Token>) -> TypeDecl {
        if path.len() != 1 {
            gpp_error!("Modules are currently not supported. At line {}.", path[0].line);
        } else {
            self.get_static_kind(&path.first().unwrap().lexeme)
        }
    }
}
