#![allow(warnings)]

use std::{
    cell::RefCell,
    clone,
    cmp::Ordering,
    collections::{ HashMap, HashSet },
    env,
    fmt::{ format, write, Display },
    process,
    rc::Rc,
    string,
};

use crate::gpp_error;

use super::{
    ast::FieldDeclaration,
    errors::{ CompilationError, CompilerErrorReporter },
    expressions::Expression,
    lexer::{ Literal, OperatorKind, PunctuationKind, Token, TokenKind },
    statements::Statement,
};

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

#[derive(Clone, PartialEq, Hash, Eq)]
struct Archetype {
    name: String,
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
    fn new(name: String) -> Self {
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

    fn empty() -> TypeDescriptor {
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

    fn declare_name(&mut self, name: &str, value: SemanticValue) {
        self.names.insert(name.to_string().clone(), value);
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
    reporter: Rc<RefCell<CompilerErrorReporter>>,
    void_instance: TypeDescriptor,
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

#[derive(Clone, Debug)]
pub struct SymbolTable {
    names: HashMap<String, StaticValue>,
    functions: HashMap<String, FunctionPrototype>,
    native_functions: HashMap<String, FunctionPrototype>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            names: HashMap::new(),
            functions: HashMap::new(),
            native_functions: HashMap::new(),
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
    PostFix(Token, Box<AnnotatedExpression>),
    Set(Box<AnnotatedExpression>, Token, Box<AnnotatedExpression>, TypeDescriptor),
    ListGet(Box<AnnotatedExpression>, Box<AnnotatedExpression>),
}

#[derive(Debug, Clone)]
pub enum AnnotatedStatement {
    If(Token, AnnotatedExpression, Box<AnnotatedStatement>, Option<Box<AnnotatedStatement>>),
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

impl SemanticAnalyzer {
    pub fn new() -> Self {
        let mut analyzer = Self {
            statements: Vec::new(),
            context_stack: ContextStack::new(),
            current_stmt: 0,
            current_symbol: String::new(),
            symbol_table: SymbolTable::new(),
            current_static_id: 1u32,
            current_symbol_kind: SymbolKind::None,
            reporter: Rc::new(RefCell::new(CompilerErrorReporter::new())),
            void_instance: TypeDescriptor::empty(),
        };
        let mut archetypes = HashSet::new();
        let fields = HashMap::new();

        analyzer.void_instance = TypeDescriptor::new("void".to_string(), archetypes, fields, 0);

        analyzer.initialize_predefined_types();

        analyzer
    }

    pub fn report_error(&mut self, error: CompilationError) {
        self.reporter.borrow_mut().report_error(error);
    }

    /// Returns the next available id for a new static type.
    /// # Returns
    /// A `u32` value with new given value.
    fn get_static_id(&mut self) -> u32 {
        self.current_static_id += 1;
        self.current_static_id
    }

    /// Initialize all native types that the language has
    /// by default in any compiled program, including `object`,
    /// `bool`, `number`, `float`, `int`, `iterator`, `str`,
    /// `tuple`, `list`.
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

        let kind = self.get_void_instance();

        // self.create_and_define_function(
        //     "print",
        //     vec![
        //         FieldDeclaration::new(
        //             Token::new(TokenKind::Identifier, "print".to_string(), 0, 0),
        //             Expression::Void
        //         )
        //     ],
        //     kind.clone()
        // );
    }

    /// Creates valid semantic data for standard native functions,
    /// ensuring that the semantic analyzer can complete the analysis
    /// without reporting errors for the defined native functions.
    ///
    /// # Arguments
    ///
    /// * `name` - A string slice containing the function name.
    /// * `params` - A `Vec` containing the description of function params names and kinds.
    /// * `kind` - The descriptor for function return kind.
    fn create_and_define_function(
        &mut self,
        name: &str,
        params: Vec<FieldDeclaration>,
        kind: TypeDescriptor
    ) {
        let arity = params.len();

        self.symbol_table.native_functions.insert(
            name.to_string(),
            FunctionPrototype::new(name.to_string(), params, arity, kind)
        );
    }

    /// Adds new field for native or user declared kind.
    ///
    /// # Arguments
    /// * `name` - A string slice with new field name.
    /// * `target_descriptor` - The descriptor of kind to be changed.
    /// * `field_descriptor` - The descriptor of new field.
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
            FieldDescriptor::new(
                field_descriptor.name.clone(),
                field_descriptor.clone(),
                fields.len() as u8
            )
        );
    }

    /// Defines a new native kind to existing kinds.
    ///
    /// # Arguments
    ///
    /// * `name` - A string slice with name of kind to be defined.
    /// * `archetypes` - A `Vec` with names of archetypes to
    /// compound new kind mask.
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

    /// Defines new user defined symbol
    ///
    /// # Arguments
    ///
    /// * `name` - A String containing the name of the symbol.
    /// * `value` - A fixed value with descriptor and `Value`
    /// for literals and instances.
    fn define_symbol(&mut self, name: String, value: StaticValue) {
        self.symbol_table.define(name, value);
    }

    /// Performs semantic analysis on the given abstract syntax tree (AST).
    ///
    /// This function traverses the AST and checks for semantic errors, such as
    /// undefined variables, type mismatches, and other rule violations. If any
    /// issues are found, they are reported accordingly.
    ///
    /// # Arguments
    ///
    /// * `ast` - A reference to the AST to be analyzed.
    ///
    /// # Returns
    ///
    /// A result indicating success or containing a list of semantic errors.
    pub fn analyze(
        &mut self,
        reporter: Rc<RefCell<CompilerErrorReporter>>,
        statements: Vec<Statement>
    ) -> SemanticCode {
        self.reset_internal_state(statements);

        self.reporter = reporter;

        let mut stmt: Statement;

        let mut annotated_statements: Vec<AnnotatedStatement> = Vec::new();

        while !self.is_at_end() {
            stmt = self.current().unwrap().clone();
            annotated_statements.push(self.analyze_stmt(&stmt));
            self.advance();
        }

        if self.get_function("main") == None {
            self.report_error(CompilationError::new("Missing 'main' function.".to_string(), None));
        }

        SemanticCode::new(self.symbol_table.clone(), AnnotatedAST::new(annotated_statements))
    }

    /// Analyzes a statement and performs semantic validation.
    ///
    /// This function processes different types of statements and ensures they adhere
    /// to semantic rules. It delegates specific checks to corresponding handlers
    /// based on the statement type.
    ///
    /// # Arguments
    ///
    /// * `stmt` - A reference to the statement to be analyzed.
    ///
    /// # Returns
    ///
    /// An `AnnotatedStatement` containing the analyzed and validated statement.
    fn analyze_stmt(&mut self, stmt: &Statement) -> AnnotatedStatement {
        match stmt {
            Statement::Return(value) => self.analyze_return(value),
            Statement::Expression(expr) => AnnotatedStatement::Expression(self.analyze_expr(expr)),
            Statement::Decorator(hash_token, attribs) => {
                self.analyze_decorator(hash_token, attribs)
            }
            Statement::Type(name, archetypes, fields) => {
                self.analyze_type(name, archetypes, fields)
            }
            Statement::Function(name, params, body, return_kind) => {
                self.analyze_function(name, params, &body, return_kind)
            }
            Statement::NativeFunction(name, params, return_kind) => {
                self.analyze_native_function(name, params, return_kind)
            }
            Statement::Variable(name, value) => self.analyze_variable_declaration(name, value),
            Statement::ForEach(variable, condition, body) => {
                self.analyze_iterator(variable, condition, &body)
            }
            Statement::While(condition, body) => { self.analyze_while_stmt(condition, body) }
            Statement::If(keyword, condition, body, else_branch) => {
                self.analyze_if_stmt(keyword, condition, &body, else_branch)
            }
            _ => gpp_error!("Statement {:?} not supported.", stmt),
        }
    }

    /// Analyzes a for-each loop and ensures semantic correctness.
    ///
    /// This function verifies that the loop condition is iterable and processes
    /// the loop body within a new scope to ensure proper variable handling.
    ///
    /// # Arguments
    ///
    /// * `variable` - The loop variable.
    /// * `condition` - The iterable expression.
    /// * `body` - The statement representing the loop body.
    ///
    /// # Returns
    ///
    /// An `AnnotatedStatement::ForEach` containing the analyzed loop structure.
    fn analyze_iterator(
        &mut self,
        variable: &Token,
        condition: &Expression,
        body: &Statement
    ) -> AnnotatedStatement {
        self.begin_scope();

        let annotated_iterator: AnnotatedExpression;

        match condition {
            Expression::Variable(variable) => {
                self.assert_archetype_kind(
                    condition,
                    self.get_static_kind("iterator"),
                    "Expect iterator in 'for' loop."
                );

                annotated_iterator = self.analyze_expr(condition);
            }

            Expression::Call(callee, paren, args) => {
                let kind = self.resolve_function_return_type(callee, paren, args);
                self.assert_kind_equals(
                    kind,
                    self.get_static_kind("iterator"),
                    "Expect iterator in for each declaration.".to_string()
                );

                annotated_iterator = self.analyze_expr(condition);
            }

            _ => {
                let iterator_kind: TypeDescriptor = self.resolve_iterator_kind(condition);
                annotated_iterator = self.analyze_expr(condition);
            }
        }

        let mut annotated_body = Vec::new();

        match body {
            Statement::Scope(stmts) => {
                for stmt in stmts {
                    annotated_body.push(Box::new(self.analyze_stmt(stmt)));
                }
            }
            _ => gpp_error!("Statement {:?} is not allowed here.", body),
        }

        self.end_scope();

        AnnotatedStatement::ForEach(
            variable.clone(),
            annotated_iterator,
            Box::new(AnnotatedStatement::Scope(annotated_body))
        )
    }

    /// Analyzes a variable declaration and ensures it adheres to semantic rules.
    ///
    /// This function checks if the variable name is already declared within the
    /// current scope and processes its initialization expression if provided.
    ///
    /// # Arguments
    ///
    /// * `name` - The token representing the variable name.
    /// * `value` - An optional expression representing the variable's initial value.
    ///
    /// # Returns
    ///
    /// An `AnnotatedStatement::Variable` containing the analyzed variable declaration.
    fn analyze_variable_declaration(
        &mut self,
        name: &Token,
        value: &Option<Expression>
    ) -> AnnotatedStatement {
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
                        let annotated_value = self.analyze_expr(expr);

                        let value = SemanticValue::new(
                            Some(self.resolve_expr_type(expr)),
                            Value::Internal,
                            name.line
                        );

                        if value.kind.as_ref().unwrap().name == "void" {
                            gpp_error!(
                                "Cannot initialize variable with 'void' value. At line {}.",
                                name.line
                            );
                        }

                        let mut context = &mut self.context();
                        context.declare_name(&name.lexeme, value);
                        AnnotatedStatement::Variable(name.clone(), Some(annotated_value))
                    }
                    None => {
                        let value = SemanticValue::new(None, Value::Internal, name.line);
                        let mut context = &mut self.context();
                        context.declare_name(&name.lexeme, value);
                        AnnotatedStatement::Variable(name.clone(), None)
                    }
                }
            }
        }
    }

    /// Analyzes a type declaration and ensures it adheres to semantic rules.
    ///
    /// This function validates that the type is declared at the top level,
    /// ensures there are no duplicate type definitions, and processes archetypes
    /// and fields associated with the type.
    ///
    /// # Arguments
    ///
    /// * `name` - The token representing the type name.
    /// * `archetypes` - A list of archetypes associated with the type.
    /// * `fields` - A list of field declarations associated with the type.
    ///
    /// # Returns
    ///
    /// An `AnnotatedStatement::Type` containing the analyzed type declaration.
    fn analyze_type(
        &mut self,
        name: &Token,
        archetypes: &Vec<Token>,
        fields: &Vec<FieldDeclaration>
    ) -> AnnotatedStatement {
        self.require_depth(
            Ordering::Less,
            1,
            format!("Type declarations are only allowed in top level code. At line {}.", name.line)
        );

        if let Some(kind) = self.symbol_table.names.get(&name.lexeme) {
            gpp_error!("Duplicated type definition for '{}'.", name.lexeme);
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

        for (index, field) in fields.iter().enumerate() {
            if let Expression::TypeComposition(mask) = field.kind.clone() {
                let kind = self.resolve_type_composition(&mask);
                let archetypes: Vec<Archetype> = kind.archetypes.clone().into_iter().collect();

                for archetype in archetypes {
                    self.get_static_kind(&archetype.name);
                }

                if type_fields.contains_key(&field.name.lexeme) {
                    self.report_error(
                        CompilationError::new(
                            format!(
                                "Field '{}' already declared at this point.",
                                field.name.lexeme
                            ),
                            Some(field.name.line)
                        )
                    );
                }

                type_fields.insert(
                    field.name.lexeme.clone(),
                    FieldDescriptor::new(field.name.lexeme.clone(), kind.clone(), index as u8)
                );
            }
        }

        let type_descriptor = TypeDescriptor::from_type_decl_with_fields(decl, type_fields.clone());

        self.define_type(type_descriptor.clone());

        let constructor = FunctionPrototype::new(
            name.lexeme.clone(),
            fields.clone(),
            type_fields.len(),
            self.get_user_defined_kind(name.lexeme.clone())
        );

        self.define_function(name.lexeme.clone(), constructor);

        AnnotatedStatement::Type(type_descriptor)
    }

    /// Defines a new type in the symbol table.
    ///
    /// This function adds a new type to the symbol table, creating an entry with the type's name
    /// and an associated static value. The type is represented by a `TypeDescriptor`, and the static
    /// value is initialized as `Internal`.
    ///
    /// # Parameters
    /// - `descriptor`: The `TypeDescriptor` containing information about the type to be defined,
    /// including the type's name and other related details.
    ///
    /// # Examples
    /// ```rust
    /// let descriptor = TypeDescriptor::new("MyType");
    /// analyzer.define_type(descriptor);
    /// ```
    ///
    /// # Panics
    /// This function may panic if the type is already defined in the symbol table.
    ///
    /// # Notes
    /// - The symbol table manages the definition of types to ensure that defined types are not duplicated.
    fn define_type(&mut self, descriptor: TypeDescriptor) {
        self.symbol_table.define(
            descriptor.name.clone(),
            StaticValue::new(descriptor, Value::Internal)
        );
    }

    /// Analyzes a function definition and generates an annotated statement.
    ///
    /// This function processes the function's name, parameters, body, and return type, ensuring
    /// that the function is correctly defined within the top-level scope. It validates the function's
    /// return type, parameters, and checks for any semantic errors. The function body is analyzed
    /// and converted into an annotated scope containing the function's statements.
    ///
    /// # Parameters
    /// - `name`: A reference to the `Token` representing the function's name. It is used to track
    ///   the function's location for error reporting.
    /// - `params`: A reference to a vector of `FieldDeclaration` representing the function's
    ///   parameters. Each parameter has a name and a type.
    /// - `body`: A reference to the `Statement` representing the function's body. It contains the
    ///   actual code of the function.
    /// - `return_kind`: A reference to an `Expression` representing the return type of the function.
    ///   It defines the expected return type, such as a basic type or a composition of types.
    ///
    /// # Returns
    /// This function returns an `AnnotatedStatement` that represents the analyzed function definition.
    /// The returned statement contains the function prototype along with its annotated body.
    fn analyze_function(
        &mut self,
        name: &Token,
        params: &Vec<FieldDeclaration>,
        body: &Statement,
        return_kind: &Expression
    ) -> AnnotatedStatement {
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
            kind = self.get_static_kind("void");

            self.report_error(
                CompilationError::new("Missing function return kind.".to_string(), Some(name.line))
            );
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

        for arg in &function_definition.params {
            let kind = self.resolve_expr_type(&arg.kind);
            self.define_local(
                &arg.name.lexeme,
                SemanticValue::new(Some(kind), Value::Internal, arg.name.line)
            );
        }

        let mut annotated_body = Vec::new();

        match body {
            Statement::Scope(stmts) => {
                for stmt in stmts {
                    annotated_body.push(Box::new(self.analyze_stmt(stmt)));
                }
            }
            _ => gpp_error!("Statement {:?} is not allowed here.", body),
        }

        self.end_scope();

        AnnotatedStatement::Function(
            function_definition,
            Box::new(AnnotatedStatement::Scope(annotated_body))
        )
    }

    /// Ensures that the current depth satisfies a given condition.
    ///
    /// This function compares the current scope depth with a specified value and reports an error
    /// if the depth does not meet the expected condition. The comparison is made based on the provided
    /// `comparator` and `depth`. If the condition is not satisfied, an error message is generated.
    ///
    /// # Parameters
    /// - `comparator`: An `Ordering` value that determines whether the current depth should be less than,
    ///   greater than, or equal to the specified depth.
    /// - `depth`: The expected scope depth that will be compared against the current depth.
    /// - `message`: The error message to be reported if the comparison condition is not met.
    ///
    /// # Returns
    /// This function does not return any value. It will report an error if the condition is not satisfied.
    fn require_depth(&mut self, comparator: Ordering, depth: usize, message: String) {
        let comparison_result = self.depth().cmp(&depth);

        if comparison_result != comparator {
            self.report_error(CompilationError::new(format!("{}", message), None));
        }
    }

    /// Starts a new scope by pushing an empty context onto the context stack.
    ///
    /// This function is used to create a new scope for the current analysis, allowing for local
    /// declarations and symbol management to be isolated within that scope. It adds an empty context
    /// to the `context_stack` to indicate the beginning of a new scope.
    ///
    /// # Parameters
    /// This function does not take any parameters.
    ///
    /// # Returns
    /// This function does not return any value. It only modifies the internal state by adding a new
    /// context to the `context_stack`.
    fn begin_scope(&mut self) {
        self.context_stack.push_empty();
    }

    /// Ends the current scope by popping the top context from the context stack.
    ///
    /// This function is used to close the current scope, removing the local declarations and symbols
    /// associated with it. It pops the top context off the `context_stack`, effectively ending the scope
    /// and returning to the previous one.
    ///
    /// # Parameters
    /// This function does not take any parameters.
    ///
    /// # Returns
    /// This function does not return any value. It only modifies the internal state by removing the
    /// top context from the `context_stack`.
    fn end_scope(&mut self) {
        self.context_stack.pop();
    }

    /// Analyzes a decorator and its associated attributes.
    ///
    /// This function processes a decorator (preceded by a hash token) and ensures it is applied
    /// correctly to a function signature. It checks if the decorator is used in a valid context (only
    /// allowed in function signatures) and annotates the decorator with its attributes. If the decorator
    /// is not used correctly, an error is reported.
    ///
    /// # Parameters
    /// - `hash_token`: A reference to the `Token` representing the `#` symbol used in the decorator.
    ///   It is used to track the decorator's location for error reporting.
    /// - `attributes`: A reference to a vector of `Expression` representing the attributes passed
    ///   to the decorator. These are analyzed and annotated.
    ///
    /// # Returns
    /// This function returns an `AnnotatedStatement` that represents the analyzed decorator. The
    /// decorator is associated with the `hash_token` and its annotated attributes.
    ///
    /// # Errors
    /// If the decorator is used outside a function signature, an error is reported, indicating that
    /// decorators are only allowed in function definitions.
    fn analyze_decorator(
        &mut self,
        hash_token: &Token,
        attributes: &Vec<Expression>
    ) -> AnnotatedStatement {
        let next = self.next();

        match next {
            Statement::Function(name, params, body, return_kind) => {
                let mut annotated_attributes = Vec::new();

                for attribute in attributes {
                    annotated_attributes.push(self.analyze_expr(attribute));
                }

                return AnnotatedStatement::Decorator(hash_token.clone(), annotated_attributes);
            }
            _ =>
                gpp_error!(
                    "Decorators are only accepted in function signatures. \x1b[33mAt line {}.\x1b[0m\n\x1b[36mHint:\x1b[0m Move \x1b[32m'#[...]'\x1b[0m to before \x1b[35m'def {}(...) {{...}}'\x1b[0m",
                    hash_token.line,
                    self.current_symbol
                ),
        }
    }

    /// Analyzes an `if` statement and generates an annotated statement.
    ///
    /// This function processes an `if` statement by analyzing its condition, body, and optional
    /// else branch. It ensures that the condition is of the correct type (boolean), and the bodies
    /// of the `if` and `else` branches are valid statements. The function also manages scope creation
    /// and closure during the analysis of the statement.
    ///
    /// # Parameters
    /// - `keyword`: A reference to the `Token` representing the `if` keyword. It is used to track
    ///   the statement's location for error reporting.
    /// - `condition`: A reference to the `Expression` representing the condition of the `if` statement.
    ///   This expression is validated to ensure it is of type `bool`.
    /// - `body`: A reference to the `Statement` representing the body of the `if` statement.
    /// - `else_branch`: An optional reference to a `Box<Statement>` representing the body of the
    ///   `else` branch. If present, this branch is analyzed as well.
    ///
    /// # Returns
    /// This function returns an `AnnotatedStatement` representing the analyzed `if` statement. The
    /// returned statement contains the annotated condition, the body of the `if` branch, and the
    /// body of the `else` branch (if present).
    ///
    /// # Errors
    /// - If the condition is not of type `bool`, an error is reported.
    /// - If the bodies of the `if` or `else` branches are not valid statements, an error is reported.
    /// - If the `else` branch contains an invalid statement, an error is reported.
    fn analyze_if_stmt(
        &mut self,
        keyword: &Token,
        condition: &Expression,
        body: &Statement,
        else_branch: &Option<Box<Statement>>
    ) -> AnnotatedStatement {
        let annotated_condition = self.analyze_expr(condition);
        self.assert_expression_kind(condition, self.get_static_kind("bool"), keyword);

        self.begin_scope();

        let mut annotated_body = Vec::new();

        match body {
            Statement::Scope(stmts) => {
                for stmt in stmts {
                    annotated_body.push(Box::new(self.analyze_stmt(stmt)));
                }
            }
            _ =>
                self.report_error(
                    CompilationError::new(
                        format!("Statement {:?} is not allowed here.", body),
                        None
                    )
                ),
        }

        self.end_scope();

        let mut annotated_else = Vec::new();

        match else_branch {
            Some(stmt) =>
                match stmt.as_ref() {
                    Statement::Scope(stmts) => {
                        self.begin_scope();

                        for stmt in stmts {
                            annotated_else.push(Box::new(self.analyze_stmt(stmt)));
                        }

                        self.end_scope();

                        AnnotatedStatement::If(
                            keyword.clone(),
                            annotated_condition,
                            Box::new(AnnotatedStatement::Scope(annotated_body)),
                            Some(Box::new(AnnotatedStatement::Scope(annotated_else)))
                        )
                    }
                    Statement::If(keyword, condition, body, else_branch) => {
                        let annotated_else_branch = self.analyze_if_stmt(
                            keyword,
                            condition,
                            body,
                            else_branch
                        );
                        AnnotatedStatement::If(
                            keyword.clone(),
                            annotated_condition,
                            Box::new(AnnotatedStatement::Scope(annotated_body)),
                            Some(Box::new(annotated_else_branch))
                        )
                    }
                    _ => gpp_error!("Statement {:?} is not allowed here.", stmt),
                }

            None =>
                AnnotatedStatement::If(
                    keyword.clone(),
                    annotated_condition,
                    Box::new(AnnotatedStatement::Scope(annotated_body)),
                    None
                ),
        }
    }

    /// Analyzes an expression and generates an annotated expression.
    ///
    /// This function processes various types of expressions, including literals, unary operations,
    /// arithmetic expressions, logical expressions, assignments, and function calls. Depending on the
    /// expression type, it delegates the analysis to the appropriate helper function for more specific
    /// processing. Unsupported expression types are marked as TODO for future implementation.
    ///
    /// # Parameters
    /// - `expr`: A reference to the `Expression` that needs to be analyzed. The expression can be
    ///   of various types, such as a literal, unary operation, or function call.
    ///
    /// # Returns
    /// This function returns an `AnnotatedExpression` that represents the analyzed expression. The
    /// return type depends on the specific type of expression being processed.
    ///
    /// # Supported Expression Types
    /// - `Expression::Void`: Returns `AnnotatedExpression::Void`.
    /// - `Expression::Literal`: Processes a literal expression and returns the result of `analyze_literal`.
    /// - `Expression::Unary`: Analyzes a unary expression and returns the result of `analyze_unary_expr`.
    /// - `Expression::Arithmetic`: Analyzes an arithmetic expression and returns the result of `analyze_arithmetic_expr`.
    /// - `Expression::Logical`: Analyzes a logical expression and returns the result of `analyze_logical_expr`.
    /// - `Expression::Assign`: Analyzes an assignment expression and returns the result of `analyze_assignment_expr`.
    /// - `Expression::Call`: Analyzes a function call expression and returns the result of `analyze_call_expression`.
    /// - `Expression::List`: Analyzes a list expression and returns the result of `analyze_collection`.
    /// - `Expression::Group`: Recursively analyzes a grouped expression using `analyze_expr`.
    ///
    /// # Unsupported Expression Types
    /// - `Expression::Ternary`: Not yet implemented.
    /// - `Expression::Lambda`: Not yet implemented.
    /// - `Expression::Tuple`: Not yet implemented.
    /// - `Expression::TypeComposition`: Not yet implemented.
    /// - `Expression::Attribute`: Not yet implemented.
    /// - `Expression::Set`: Not yet implemented.
    ///
    /// # Errors
    /// This function does not return an error itself, but it delegates the analysis to other functions
    /// that may report errors depending on the expression type.
    fn analyze_expr(&mut self, expr: &Expression) -> AnnotatedExpression {
        match expr.clone() {
            Expression::Void => AnnotatedExpression::Void,
            Expression::Literal(token) => self.analyze_literal(token),
            Expression::PostFix(operator, variable) => {
                self.analyze_postfix_expr(&operator, &variable)
            }
            Expression::Unary(token, expression) => self.analyze_unary_expr(token, &expression),
            Expression::Arithmetic(left, op, right) => {
                self.analyze_arithmetic_expr(&left, &op, &right)
            }
            Expression::Logical(left, op, right) => self.analyze_logical_expr(&left, &op, &right),
            Expression::Ternary(expression, expression1, expression2) => todo!(),
            Expression::Assign(token, expression) => {
                self.analyze_assignment_expr(token, &expression)
            }
            Expression::Lambda => todo!(),
            Expression::Get(expression, token) => self.analyze_get_expr(&expression, token),
            Expression::Variable(token) => self.analyze_variable_get_expr(token),
            Expression::Set(target, name, value) => self.analyze_set_expr(target, name, value),
            Expression::Call(callee, paren, args) => {
                self.analyze_call_expression(&callee, &paren, &args)
            }
            Expression::Tuple(expressions) => todo!(),
            Expression::List(expressions) => self.analyze_collection(expr),
            Expression::TypeComposition(names) => todo!(),
            Expression::Attribute(token, expressions) => todo!(),
            Expression::Group(expression) => self.analyze_expr(&expression),
            Expression::ListGet(expression, index) => self.analyze_list_get_expr(expression, index),
        }
    }

    /// Retrieves the next statement in the sequence of statements.
    ///
    /// This function returns the next statement in the list of statements. If there is no next statement
    /// (i.e., the end of the list is reached), it returns a `Statement::EndCode` to indicate the end of code.
    /// It is used to navigate through a series of statements in sequence.
    ///
    /// # Returns
    /// - If there is a next statement, it returns a cloned reference to the next statement.
    /// - If there is no next statement, it returns `Statement::EndCode` to indicate the end of the code sequence.
    fn next(&self) -> Statement {
        match self.statements.get(self.current_stmt + 1) {
            None => Statement::EndCode,
            Some(stmt) => stmt.clone(),
        }
    }

    /// Checks if the current statement is the last statement.
    ///
    /// This function determines if the current statement is the last statement in the sequence
    /// by checking if the current statement is `Statement::EndCode`. It returns `true` if the
    /// current statement is the last one, indicating the end of the code sequence, and `false` otherwise.
    ///
    /// # Returns
    /// - `true` if the current statement is the last one (`Statement::EndCode`).
    /// - `false` if there are more statements to process.
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

    /// Retrieves the current statement.
    ///
    /// This function returns a reference to the current statement in the sequence. If no statement
    /// is available at the current position, it returns `None`.
    ///
    /// # Returns
    /// - `Some(&Statement)` if there is a current statement.
    /// - `None` if there is no statement at the current position.
    fn current(&self) -> Option<&Statement> {
        self.statements.get(self.current_stmt)
    }

    /// Retrieves the previous statement.
    ///
    /// This function returns a reference to the previous statement in the sequence. If no previous
    /// statement exists (i.e., if the current statement is the first one), it returns `None`.
    ///
    /// # Returns
    /// - `Some(&Statement)` if there is a previous statement.
    /// - `None` if there is no previous statement.
    fn previous(&self) -> Option<&Statement> {
        self.statements.get(self.current_stmt - 1)
    }

    /// Advances to the next statement and returns the previous one.
    ///
    /// This function increments the `current_stmt` index and returns the previous statement in the sequence
    /// (the one before the new current statement). If there is no previous statement, it returns `None`.
    ///
    /// # Returns
    /// - `Some(&Statement)` if there is a previous statement after advancing.
    /// - `None` if there is no previous statement after advancing (i.e., if at the beginning).
    fn advance(&mut self) -> Option<&Statement> {
        self.current_stmt += 1;
        self.previous()
    }

    /// Resets the internal state of the analysis context.
    ///
    /// This function resets the analysis context, including the list of statements, the context stack,
    /// and the current statement index. It is typically used to reinitialize the state before starting
    /// a new analysis or after a major error that requires a fresh start.
    ///
    /// # Parameters
    /// - `statements`: A vector of statements to initialize the internal statements list with.
    fn reset_internal_state(&mut self, statements: Vec<Statement>) {
        self.statements = statements;
        self.context_stack = ContextStack::new();
        self.current_stmt = 0;
    }

    /// Returns the current depth of the context stack.
    ///
    /// The context stack tracks the current scope of analysis. This function returns the number of levels
    /// in the context stack, which corresponds to the current depth of nested scopes.
    ///
    /// # Returns
    /// - The current depth (i.e., the number of levels in the context stack).
    fn depth(&self) -> usize {
        self.context_stack.len()
    }

    /// Retrieves the current context scope.
    ///
    /// This function returns a mutable reference to the topmost scope in the context stack, which is
    /// useful for analyzing or modifying the symbols within the current scope.
    ///
    /// # Returns
    /// - A mutable reference to the current `ContextScope` at the top of the context stack.
    fn context(&mut self) -> &mut ContextScope {
        self.context_stack.peek()
    }

    /// Analyzes a unary expression and returns the corresponding annotated expression.
    ///
    /// This function handles unary operators such as `-` (negation) and `!` (logical negation). It checks
    /// the type of the operand and applies the appropriate checks. If the operator is applied to an invalid
    /// operand type, an error is raised.
    ///
    /// # Parameters
    /// - `token`: The token representing the operator (`-` or `!`).
    /// - `expression`: The expression to which the unary operator is applied.
    ///
    /// # Returns
    /// - An `AnnotatedExpression` representing the analyzed unary expression.
    fn analyze_unary_expr(&mut self, token: Token, expression: &Expression) -> AnnotatedExpression {
        match token.kind {
            TokenKind::Operator(op) =>
                match op {
                    OperatorKind::Minus => {
                        let expr_type = self.resolve_expr_type(&expression);

                        self.assert_archetype_kind(
                            &expression,
                            self.get_static_kind("number"),
                            "'-' operator only be applyed in numbers."
                        );

                        AnnotatedExpression::Unary(
                            token.clone(),
                            Box::new(self.analyze_expr(expression)),
                            expr_type
                        )
                    }

                    OperatorKind::Not => {
                        let expr_type = self.resolve_expr_type(&expression);

                        if expr_type.id != self.get_static_kind_id("bool") {
                            gpp_error!(
                                "Cannot apply 'not' operator in a '{}' instance. At line {}.",
                                expr_type.name,
                                token.line
                            );
                        }

                        AnnotatedExpression::Unary(
                            token.clone(),
                            Box::new(self.analyze_expr(expression)),
                            expr_type
                        )
                    }
                    _ => {
                        gpp_error!("Invalid unary operation at line {}.", token.line);
                    }
                }

            _ => gpp_error!("Invalid unary operation at line {}.", token.line),
        }
    }

    /// Resolves and returns the type descriptor for the given expression.
    ///
    /// This function inspects the expression and resolves its type, returning a `TypeDescriptor` that
    /// corresponds to the type of the expression. It handles various expression types, including literals,
    /// unary operations, and arithmetic operations. If the expression's type cannot be resolved, an error is raised.
    ///
    /// # Parameters
    /// - `expression`: A reference to the expression whose type is being resolved.
    ///
    /// # Returns
    /// - A `TypeDescriptor` representing the type of the given expression.
    ///
    /// # Errors
    /// - If the expression type cannot be determined or is unsupported, an error is raised.
    fn resolve_expr_type(&mut self, expression: &Expression) -> TypeDescriptor {
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
            Expression::Unary(_, expression) => self.resolve_expr_type(&expression),
            Expression::Arithmetic(left, op, right) => {
                if let TokenKind::Operator(operator) = op.kind {
                    match operator {
                        | OperatorKind::Plus
                        | OperatorKind::Minus
                        | OperatorKind::Star
                        | OperatorKind::Slash => {
                            return self.resolve_expr_type(&left);
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
                let left_type = self.resolve_expr_type(&left);

                if left_type != self.get_symbol("bool").unwrap().kind {
                    gpp_error!("Expected boolean type for logical expression.");
                }
                left_type
            }
            Expression::Ternary(cond, true_expr, false_expr) => {
                let cond_type = self.resolve_expr_type(&cond);
                let true_type = self.resolve_expr_type(&true_expr);
                let false_type = self.resolve_expr_type(&false_expr);

                if true_type != false_type {
                    gpp_error!("Types of both branches of the ternary expression must match.");
                }
                true_type
            }
            Expression::Variable(name) => self.resolve_identifier_type(name),
            Expression::Assign(_, expr) => self.resolve_expr_type(expr),
            Expression::Lambda => { gpp_error!("Lambda expressions are currently not supported.") }
            Expression::TypeComposition(mask) => self.resolve_type_composition(mask),
            Expression::Call(callee, paren, args) => {
                self.resolve_function_return_type(callee, paren, args)
            }
            Expression::Get(object, token) => self.resolve_get_expr(object, token),
            Expression::Group(expression) => self.resolve_expr_type(&expression),
            Expression::Void => self.get_void_instance(),
            Expression::ListGet(list, index) => self.resolve_list_get_type(list, index),
            _ => gpp_error!("Expression {expression:?} are not supported."),
        }
    }

    /// Returns a reference to the predefined "void" type instance.
    ///
    /// This function retrieves a predefined instance of the "void" type. It is used when an expression
    /// or function is expected to return no value.
    ///
    /// # Returns
    /// - A clone of the "void" type instance.
    fn get_void_instance(&mut self) -> TypeDescriptor {
        self.void_instance.clone()
    }

    /// Retrieves a symbol from the symbol table by name.
    ///
    /// This function looks up a symbol in the symbol table by its name. It returns an `Option` containing
    /// the symbol if it exists, or `None` if the symbol is not found.
    ///
    /// # Parameters
    /// - `name`: The name of the symbol to look up.
    ///
    /// # Returns
    /// - An `Option` containing the `StaticValue` associated with the symbol if it exists, or `None` if not.
    fn get_symbol(&self, name: &str) -> Option<&StaticValue> {
        self.symbol_table.get(name)
    }

    /// Retrieves the ID of a symbol's kind from the symbol table by name.
    ///
    /// This function looks up a symbol in the symbol table by its name and retrieves the ID of its kind.
    /// If the symbol does not exist, it panics.
    ///
    /// # Parameters
    /// - `name`: The name of the symbol whose kind ID is to be retrieved.
    ///
    /// # Returns
    /// - The ID of the kind associated with the symbol.
    ///
    /// # Panics
    /// - Panics if the symbol does not exist in the symbol table.
    fn get_static_kind_id(&self, name: &str) -> u32 {
        self.symbol_table.get(name).unwrap().kind.id
    }

    /// Resolves the type of an identifier in the current context.
    ///
    /// This function looks up the type of an identifier by traversing the context stack from the current
    /// scope up to the global scope. It checks if the identifier is declared and returns its type. If the
    /// identifier is not found or if its type is unknown, it raises an error.
    ///
    /// # Parameters
    /// - `token`: The token representing the identifier whose type is to be resolved.
    ///
    /// # Returns
    /// - The `TypeDescriptor` representing the type of the identifier.
    ///
    /// # Errors
    /// - Raises an error if the identifier is not found or if its type is unknown.
    fn resolve_identifier_type(&mut self, token: &Token) -> TypeDescriptor {
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

    /// Retrieves a symbol from the context stack by name, checking all levels of scope.
    ///
    /// This function attempts to find a symbol by name starting from the most recent scope and working
    /// backwards through previous scopes. If the symbol is found, it returns it. If the symbol is not found
    /// in any scope, it raises an error.
    ///
    /// # Parameters
    /// - `name`: The token representing the name of the symbol to look for.
    ///
    /// # Returns
    /// - An `Option<SemanticValue>` representing the symbol found in the context stack, or `None` if not found.
    ///
    /// # Errors
    /// - Raises an error if the symbol is not found in the current context or any parent contexts.
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

        gpp_error!("The variable '{}' are not declared here. At line {}.", name.lexeme, name.line);
    }

    /// Analyzes an assignment expression, ensuring the assigned value matches the variable's type.
    ///
    /// This function checks that the variable being assigned a value has been declared, and that the type
    /// of the value being assigned matches the type of the variable. If the types do not match, an error is raised.
    /// If the variable's type is not yet inferred, it infers the type of the variable based on the assigned value.
    ///
    /// # Parameters
    /// - `token`: The token representing the variable being assigned to.
    /// - `expression`: The expression on the right-hand side of the assignment.
    ///
    /// # Returns
    /// - An `AnnotatedExpression` representing the assignment expression, including the assigned value and its type.
    ///
    /// # Errors
    /// - Raises an error if the variable is not declared or if the types of the variable and the assigned value do not match.
    fn analyze_assignment_expr(
        &mut self,
        token: Token,
        expression: &Expression
    ) -> AnnotatedExpression {
        let symbol = self.get_name_in_depth(&token);

        match symbol {
            Some(sv) => {
                let value = self.analyze_expr(&expression);

                let value_type = self.resolve_expr_type(&expression);
                let symbol_type = sv.kind;

                if let Some(kind) = &symbol_type {
                    if kind.name == "void" {
                        gpp_error!("Cannot assign 'void' to variables. At line {}.", token.line);
                    }
                }

                if value_type.name == "void" {
                    gpp_error!("Cannot assign 'void' to variables. At line {}.", token.line);
                }

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

                        AnnotatedExpression::Assign(token.clone(), Box::new(value), kind)
                    }
                    None => {
                        self.context().set_infered_kind(&token.lexeme, value_type.clone());
                        AnnotatedExpression::Assign(token.clone(), Box::new(value), value_type)
                    }
                }
            }
            None => gpp_error!("The name '{}' are not declared here.", token.lexeme),
        }
    }

    /// Asserts that the given expression matches the expected type.
    ///
    /// This function checks if the type of the given expression matches the expected type. If the types do
    /// not match, it raises an error with an appropriate message.
    ///
    /// # Parameters
    /// - `expr`: The expression whose type is being checked.
    /// - `expected_kind`: The expected type for the expression.
    /// - `location`: The token representing the location of the expression in the code.
    ///
    /// # Errors
    /// - Raises an error if the type of the expression does not match the expected type.
    fn assert_expression_kind(
        &mut self,
        expr: &Expression,
        expected_kind: TypeDescriptor,
        location: &Token
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

    /// Retrieves the static type descriptor for a given name from the symbol table.
    ///
    /// This function looks up a type descriptor in the symbol table by name. If the symbol is found, it returns
    /// the corresponding type descriptor. If the symbol does not exist, it raises an error.
    ///
    /// # Parameters
    /// - `name`: The name of the type to retrieve.
    ///
    /// # Returns
    /// - The `TypeDescriptor` corresponding to the name.
    ///
    /// # Panics
    /// - Panics if the symbol does not exist in the symbol table.
    fn get_static_kind(&self, name: &str) -> TypeDescriptor {
        self.symbol_table.get(name).unwrap().kind.clone()
    }

    /// Analyzes a variable reference expression.
    ///
    /// This function resolves the type of a variable reference by looking up the variable in the context
    /// stack. It returns an annotated expression for the variable reference, including the variable's type.
    ///
    /// # Parameters
    /// - `token`: The token representing the variable being referenced.
    ///
    /// # Returns
    /// - An `AnnotatedExpression` representing the variable reference, including its type.
    ///
    /// # Errors
    /// - Raises an error if the variable is not declared or if its type is unknown.
    fn analyze_variable_get_expr(&mut self, token: Token) -> AnnotatedExpression {
        let kind = match self.get_name_in_depth(&token) {
            Some(v) =>
                match v.kind {
                    Some(k) => k,
                    None =>
                        gpp_error!(
                            "The kind of {} is not known here. At line {}.",
                            token.lexeme,
                            token.line
                        ),
                }
            None => {
                gpp_error!(
                    "The kind of {} is not known here. At line {}.",
                    token.lexeme,
                    token.line
                );
            }
        };
        AnnotatedExpression::Variable(token, kind)
    }

    /// Analyzes a literal expression and resolves its type.
    ///
    /// This function creates an annotated expression for a literal, determining its type based on the token
    /// representing the literal.
    ///
    /// # Parameters
    /// - `token`: The token representing the literal value.
    ///
    /// # Returns
    /// - An `AnnotatedExpression` representing the literal, including its type.
    fn analyze_literal(&self, token: Token) -> AnnotatedExpression {
        AnnotatedExpression::Literal(token.clone(), self.resolve_literal_kind(&token))
    }

    /// Analyzes an arithmetic expression (binary operation) involving two operands.
    ///
    /// This function checks the types of the left and right operands, ensuring they are valid for the
    /// given arithmetic operator. It verifies that both operands are of compatible types (e.g., numbers)
    /// and raises an error if the types do not match the expected kind. The operator kind (e.g., plus, minus)
    /// is also validated for its compatibility with the operand types.
    ///
    /// # Parameters
    /// - `left`: The left operand of the arithmetic expression.
    /// - `token`: The token representing the operator.
    /// - `right`: The right operand of the arithmetic expression.
    ///
    /// # Returns
    /// - An `AnnotatedExpression` representing the result of the arithmetic operation, with the operator
    ///   and types validated.
    ///
    /// # Errors
    /// - Raises an error if the operands are incompatible with the operation, or if the operator is invalid
    ///   for the operands' types.
    fn analyze_arithmetic_expr(
        &mut self,
        left: &Expression,
        token: &Token,
        right: &Expression
    ) -> AnnotatedExpression {
        let annotated_left;
        let annotated_right;

        if !matches!(left, Expression::Literal(literal)) {
            annotated_left = self.analyze_expr(&left);
        } else {
            if let Expression::Literal(l) = left {
                annotated_left = self.analyze_literal(l.clone());
            } else {
                gpp_error!("Invalid literal kind. At line {}.", token.line);
            }
        }

        if !matches!(right, Expression::Literal(literal)) {
            annotated_right = self.analyze_expr(&right);
        } else {
            if let Expression::Literal(l) = right {
                annotated_right = self.analyze_literal(l.clone());
            } else {
                gpp_error!("Invalid literal kind. At line {}.", token.line);
            }
        }

        let left_kind = self.resolve_expr_type(&left);
        let right_kind = self.resolve_expr_type(&right);

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
                    let msg = format!(
                        "Cannot apply arithmetic operation '{}' to '{}' and '{}'. At line {}.",
                        token.lexeme,
                        left_kind.name,
                        right_kind.name,
                        token.line
                    );

                    self.assert_archetype_kind(&left, self.get_static_kind("number"), &msg);
                    self.assert_archetype_kind(&right, self.get_static_kind("number"), &msg);

                    AnnotatedExpression::Arithmetic(
                        Box::new(self.analyze_expr(left)),
                        token.clone(),
                        Box::new(self.analyze_expr(right)),
                        left_kind
                    )
                }

                OperatorKind::EqualEqual => {
                    let expected_kind = self.resolve_expr_type(&left);
                    self.assert_expression_kind(&right, expected_kind, &token);

                    AnnotatedExpression::Arithmetic(
                        Box::new(self.analyze_expr(left)),
                        token.clone(),
                        Box::new(self.analyze_expr(right)),
                        left_kind
                    )
                }

                _ =>
                    gpp_error!(
                        "Invalid arithmetic operator '{}'. At line {}.",
                        token.lexeme,
                        token.line
                    ),
            }
        } else {
            gpp_error!("Invalid arithmetic operator '{}'. At line {}.", token.lexeme, token.line);
        }
    }

    /// Checks whether two types are the same kind (i.e., have the same type ID).
    ///
    /// This function compares two `TypeDecl` values and raises an error with a custom message if their
    /// `kind_id` values are not equal. It is useful for ensuring that two types are compatible or
    /// match in a certain context.
    ///
    /// # Parameters
    /// - `a`: The first `TypeDecl` to compare.
    /// - `b`: The second `TypeDecl` to compare.
    /// - `msg`: A custom error message to be included if the types do not match.
    ///
    /// # Errors
    /// - Raises an error with the provided message if the types are not the same kind.
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
        expr: &Expression,
        archetype_source: TypeDescriptor,
        msg: &str
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
    /// - `elements`: A slice of Rced expressions representing the elements of the list.
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
    fn resolve_list_type(&mut self, elements: &[Rc<Expression>]) -> TypeDescriptor {
        if elements.is_empty() {
            gpp_error!("Cannot infer type of empty list. At least one element is required.");
        }

        let first_type = self.resolve_expr_type(&elements[0]);

        if elements.len() == 1 {
            return first_type;
        }

        let mut common_archetypes: HashSet<Archetype> = first_type.archetypes;

        for element in &elements[1..] {
            let element_type = self.resolve_expr_type(&element);
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

    /// Analyzes a collection expression (e.g., a list or set of elements).
    ///
    /// This function processes a collection expression, ensuring its elements are valid and their types
    /// are correctly inferred. If the expression is a list, it iterates over its elements, annotates them
    /// with their respective types, and returns an `AnnotatedExpression` representing the list.
    ///
    /// # Parameters
    /// - `collection`: The collection expression to be analyzed.
    ///
    /// # Returns
    /// - An `AnnotatedExpression` representing the collection, with its elements' types annotated.
    ///
    /// # Errors
    /// - Raises an error if the collection is of an invalid kind (i.e., not a list).
    fn analyze_collection(&mut self, collection: &Expression) -> AnnotatedExpression {
        let kind = self.resolve_iterator_kind(collection);

        if let Expression::List(elements) = collection {
            let mut annotated_elements = Vec::new();

            for element in elements {
                annotated_elements.push(Box::new(self.analyze_expr(element)));
            }

            AnnotatedExpression::List(annotated_elements, kind)
        } else {
            gpp_error!("Invalid collection kind.");
        }
    }

    /// Analyzes a function call expression.
    ///
    /// This function processes a function call expression, ensuring that the callee is a valid function
    /// and that the correct number of arguments is passed. It checks the arity of the function, verifies
    /// that the argument types match the function's parameter types, and returns an `AnnotatedExpression`
    /// representing the function call. If the callee is recursive or not declared, an error is raised.
    ///
    /// # Parameters
    /// - `callee`: The expression representing the function being called.
    /// - `paren`: The token representing the opening parenthesis of the function call.
    /// - `args`: A vector of expressions representing the arguments of the function call.
    ///
    /// # Returns
    /// - An `AnnotatedExpression` representing the function call with annotated arguments.
    ///
    /// # Errors
    /// - Raises an error if the function is recursive, not declared, or if the wrong number of arguments
    ///   is passed.
    fn analyze_call_expression(
        &mut self,
        callee: &Expression,
        paren: &Token,
        args: &Vec<Expression>
    ) -> AnnotatedExpression {
        let mut annotated_args = Vec::new();

        for arg in args {
            annotated_args.push(Box::new(self.analyze_expr(arg)));
        }

        if let Expression::Variable(name) = callee {
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

                    self.assert_function_args(prototype.clone(), args);
                    AnnotatedExpression::Call(
                        prototype.clone(),
                        paren.clone(),
                        annotated_args,
                        prototype.return_kind.clone()
                    )
                }
                None => {
                    match self.get_native_function(&name.lexeme.clone()) {
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

                            self.assert_function_args(prototype.clone(), args);
                            AnnotatedExpression::CallNative(
                                prototype.clone(),
                                paren.clone(),
                                annotated_args,
                                prototype.return_kind.clone()
                            )
                        }

                        None => {
                            gpp_error!(
                                "Function '{}' are not declared in this scope. At line {}.",
                                name.lexeme.clone(),
                                name.line
                            )
                        }
                    }
                }
            }
        } else {
            gpp_error!("Call functions inside modules are currently not allowed.");
        }
    }

    /// Defines a new function in the symbol table.
    ///
    /// This function adds a function prototype to the symbol table, associating it with the specified
    /// function name. This enables later lookups of the function by its name.
    ///
    /// # Parameters
    /// - `name`: The name of the function being defined.
    /// - `value`: The `FunctionPrototype` representing the function's signature.
    ///
    /// # Example
    /// ```rust
    /// define_function("my_function".to_string(), my_function_prototype);
    /// ```
    fn define_function(&mut self, name: String, value: FunctionPrototype) {
        self.symbol_table.define_function(name, value);
    }

    /// Resolves the return type of a function call.
    ///
    /// This function checks the return type of a function when it is called, based on the function's
    /// prototype stored in the symbol table. It ensures that the function is defined and retrieves
    /// its return type.
    ///
    /// # Parameters
    /// - `callee`: The expression representing the function being called.
    /// - `paren`: The token representing the opening parenthesis of the function call.
    /// - `args`: The arguments passed to the function call.
    ///
    /// # Returns
    /// - A `TypeDescriptor` representing the return type of the function.
    ///
    /// # Errors
    /// - Raises an error if the function is not declared in the current scope or if the callee is not a valid function call.
    fn resolve_function_return_type(
        &mut self,
        callee: &Expression,
        paren: &Token,
        args: &Vec<Expression>
    ) -> TypeDescriptor {
        if let Expression::Variable(name) = callee {
            let mut function = self.symbol_table.get_function(&name.lexeme.clone());

            if let None = function {
                function = self.symbol_table.native_functions.get_mut(&name.lexeme);
            }

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

    /// Asserts that the arguments passed to a function call match the expected types.
    ///
    /// This function compares the types of the arguments passed to a function call against the expected
    /// types specified in the function's prototype. If the types don't match, an error is raised.
    ///
    /// # Parameters
    /// - `prototype`: The `FunctionPrototype` representing the expected signature of the function.
    /// - `args`: A vector of expressions representing the arguments passed to the function call.
    ///
    /// # Errors
    /// - Raises an error if any of the argument types do not match the expected types.
    fn assert_function_args(&mut self, prototype: FunctionPrototype, args: &Vec<Expression>) {
        for (index, arg) in args.iter().enumerate() {
            let proto_arg_kind = self.resolve_expr_type(&prototype.params[index].kind);
            let passed_arg_kind = self.resolve_expr_type(arg);

            self.assert_archetype_kind(
                arg,
                proto_arg_kind.clone(),
                format!(
                    "Expect '{}' to '{}' param, but got '{}'.",
                    proto_arg_kind.name,
                    prototype.params[index].name.lexeme,
                    passed_arg_kind.name
                ).as_str()
            );
        }
    }

    /// Retrieves a function prototype by its name.
    ///
    /// This function looks up the function prototype in the symbol table by its name, allowing
    /// access to the function's signature, such as its parameters and return type.
    ///
    /// # Parameters
    /// - `name`: The name of the function being retrieved.
    ///
    /// # Returns
    /// - An `Option<&mut FunctionPrototype>` containing a mutable reference to the function's prototype
    ///   if it exists, or `None` if the function is not defined.
    ///
    /// # Example
    /// ```rust
    /// let function = get_function("my_function");
    /// ```
    fn get_function(&mut self, name: &str) -> Option<&mut FunctionPrototype> {
        self.symbol_table.get_function(name)
    }

    /// Resolves the type of an expression based on a path of tokens.
    ///
    /// This function resolves a type by following a sequence of tokens, ensuring that modules are
    /// not used, as they are currently unsupported. The path should contain a single token representing
    /// the type's name.
    ///
    /// # Parameters
    /// - `path`: A vector of tokens representing the path to the type.
    ///
    /// # Returns
    /// - A `TypeDescriptor` representing the resolved type.
    ///
    /// # Errors
    /// - Raises an error if the path has more than one token, indicating unsupported module usage.
    fn resolve_type(&self, path: Vec<Token>) -> TypeDescriptor {
        if path.len() != 1 {
            gpp_error!("Modules are currently not supported. At line {}.", path[0].line);
        } else {
            self.get_static_kind(&path.first().unwrap().lexeme)
        }
    }

    /// Defines a local variable in the current context.
    ///
    /// This function declares a local variable by adding it to the current context, associating
    /// the variable's name with its semantic value (type, scope, etc.).
    ///
    /// # Parameters
    /// - `name`: The name of the variable being declared.
    /// - `value`: The `SemanticValue` associated with the variable, containing type and other details.
    fn define_local(&mut self, name: &str, value: SemanticValue) {
        self.context().declare_name(name, value);
    }

    /// Resolves the type of an iterator expression (e.g., for lists or function calls).
    ///
    /// This function determines the type of an iterator expression. It handles different types of
    /// iterator expressions, such as lists and function calls, and ensures that the correct type
    /// is inferred based on the expression's context.
    ///
    /// # Parameters
    /// - `iterator`: The iterator expression whose type is to be resolved.
    ///
    /// # Returns
    /// - A `TypeDescriptor` representing the type of the iterator expression.
    ///
    /// # Errors
    /// - Raises an error if the iterator expression is not a list or a function call.
    fn resolve_iterator_kind(&mut self, iterator: &Expression) -> TypeDescriptor {
        let expr_kind = self.resolve_expr_type(iterator);

        match iterator {
            Expression::List(elements) => self.resolve_list_type(&elements),
            Expression::Call(callee, paren, args) => {
                self.analyze_call_expression(callee, paren, args);
                self.resolve_function_return_type(callee, paren, args)
            }
            _ => {
                gpp_error!("Expect list, but got {:?}.", iterator);
            }
        }
    }

    /// Retrieves a `TypeDescriptor` that matches a set of archetypes.
    ///
    /// This function checks the symbol table to find a `TypeDescriptor` whose archetypes match
    /// the provided set of archetypes.
    ///
    /// # Parameters
    /// - `sets`: A slice of `Archetype` values to match against the types in the symbol table.
    ///
    /// # Returns
    /// - An `Option<TypeDescriptor>` representing the matching type, or `None` if no match is found.
    ///
    /// # Example
    /// ```rust
    /// let result = get_by_archetype(&[Archetype::new("object".to_string())]);
    /// ```
    fn get_by_archetype(&mut self, sets: &[Archetype]) -> Option<TypeDescriptor> {
        let target_set: HashSet<_> = sets.iter().cloned().collect();

        match self.symbol_table.names.iter().find(|decl| decl.1.kind.archetypes == target_set) {
            Some((name, value)) => Some(value.kind.clone()),
            None => None,
        }
    }

    /// Analyzes a logical expression (e.g., `&&`, `||`) and ensures both operands are boolean.
    ///
    /// This function checks that both operands of the logical expression are of type `bool` and
    /// then annotates the expression accordingly.
    ///
    /// # Parameters
    /// - `left`: The left operand of the logical expression.
    /// - `op`: The operator (`&&` or `||`).
    /// - `right`: The right operand of the logical expression.
    ///
    /// # Returns
    /// - An `AnnotatedExpression` representing the logical expression, including the operator and operands.
    ///
    /// # Errors
    /// - Raises an error if either operand is not of type `bool`.
    fn analyze_logical_expr(
        &mut self,
        left: &Expression,
        op: &Token,
        right: &Expression
    ) -> AnnotatedExpression {
        self.assert_expression_kind(left, self.get_static_kind("bool"), op);
        self.assert_expression_kind(right, self.get_static_kind("bool"), op);

        let left_kind = self.resolve_expr_type(left);

        AnnotatedExpression::Logical(
            Box::new(self.analyze_expr(left)),
            op.clone(),
            Box::new(self.analyze_expr(right)),
            left_kind
        )
    }

    /// Resolves a type composition from a mask of tokens.
    ///
    /// This function builds a set of archetypes from the given tokens and attempts to find a matching
    /// `TypeDescriptor` that satisfies all the archetypes.
    ///
    /// # Parameters
    /// - `mask`: A vector of `Token`s representing the names of types or modules.
    ///
    /// # Returns
    /// - A `TypeDescriptor` representing the resolved type based on the mask.
    ///
    /// # Errors
    /// - Raises an error if no matching type is found for the given archetypes.
    fn resolve_type_composition(&mut self, mask: &Vec<Token>) -> TypeDescriptor {
        let mut archetypes = HashSet::<Archetype>::new();

        if mask[0].lexeme == "void" {
            return self.get_void_instance();
        }

        archetypes.insert(Archetype::new("object".to_string()));

        for name in mask {
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

    /// Analyzes a return statement and ensures that the return type matches the function signature.
    ///
    /// This function checks if the return statement is within a function context and validates that
    /// the type of the returned expression matches the function's return type.
    ///
    /// # Parameters
    /// - `value`: The expression being returned.
    ///
    /// # Returns
    /// - An `AnnotatedStatement` representing the return statement, with the annotated return value.
    ///
    /// # Errors
    /// - Raises an error if the return statement is outside a function or if the return type does not match the function's signature.
    fn analyze_return(&mut self, value: &Option<Expression>) -> AnnotatedStatement {
        self.require_depth(
            Ordering::Greater,
            0,
            "Return statement are only allowed inside functions.".to_string()
        );

        if self.current_symbol_kind != SymbolKind::Function {
            gpp_error!("Returns is only allowed inside functions.");
        }

        let function = self.current_symbol.clone();
        let function_signature = self.get_function(&function).unwrap().clone();

        match value {
            Some(v) => {
                let annotated_value = self.analyze_expr(v);

                self.assert_archetype_kind(
                    v,
                    function_signature.return_kind.clone(),
                    format!(
                        "Return of '{}' does not match with function signature.",
                        function.clone()
                    ).as_str()
                );

                AnnotatedStatement::Return(Some(annotated_value))
            }
            None => {
                if function_signature.return_kind.name != "void" {
                    gpp_error!(
                        "Cannot return void from '{}' because it's require '{}' instance.",
                        function,
                        function_signature.return_kind.name
                    );
                }

                return AnnotatedStatement::Return(None);
            }
        }
    }

    /// Asserts that two types are equal.
    ///
    /// This function compares two `TypeDescriptor` values and raises an error if they are not equal
    /// in terms of their archetypes.
    ///
    /// # Parameters
    /// - `source`: The source `TypeDescriptor` to check.
    /// - `target`: The target `TypeDescriptor` to compare against.
    /// - `msg`: The error message to display if the types do not match.
    ///
    /// # Errors
    /// - Raises an error if the archetypes of the `source` and `target` types do not match.
    fn assert_kind_equals(&self, source: TypeDescriptor, target: TypeDescriptor, msg: String) {
        for i in target.archetypes {
            if !source.archetypes.contains(&i) {
                gpp_error!("{}", msg);
            }
        }
    }

    /// Resolves the type of an expression with field access (e.g., `obj.field`).
    ///
    /// This function resolves the type of an expression with one or more field accesses, ensuring that
    /// each field in the path exists and is valid for the type.
    ///
    /// # Parameters
    /// - `expression`: The expression representing the object whose fields are being accessed.
    /// - `token`: The token representing the field being accessed.
    ///
    /// # Returns
    /// - A `TypeDescriptor` representing the type of the accessed field.
    ///
    /// # Errors
    /// - Raises an error if any field in the expression path does not exist or if the type is invalid.
    fn resolve_get_expr(&mut self, expression: &Expression, token: &Token) -> TypeDescriptor {
        let mut current_kind: Option<TypeDescriptor> = None;
        let mut current_expression = expression;
        let mut is_literal = false;

        let mut path = vec![token.clone()];

        while let Expression::Get(expr, name) = current_expression {
            path.push(name.clone());
            current_expression = expr;
        }

        if let Expression::Variable(name) = current_expression {
            path.push(name.clone());
        } else {
            current_kind = Some(self.resolve_expr_type(&current_expression).clone());
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

    /// Analyzes an expression involving field or member access (e.g., `obj.field`).
    ///
    /// This function first analyzes the base expression and then constructs an `AnnotatedExpression`
    /// for the field access. It resolves the type of the field access expression as well.
    ///
    /// # Parameters
    /// - `expression`: The expression that represents the base object.
    /// - `token`: The token representing the field being accessed.
    ///
    /// # Returns
    /// - An `AnnotatedExpression::Get` that represents the field access expression, including the
    ///   base expression, the field's token, and the resolved type of the field.
    ///
    /// # Example
    /// ```rust
    /// let expr = analyze_get_expr(&expression, token);
    /// ```
    fn analyze_get_expr(&mut self, expression: &Expression, token: Token) -> AnnotatedExpression {
        AnnotatedExpression::Get(
            Box::new(self.analyze_expr(expression)),
            token.clone(),
            self.resolve_expr_type(expression)
        )
    }

    /// Retrieves the type descriptor of a user-defined symbol.
    ///
    /// This function looks up a symbol's name in the symbol table and retrieves the `TypeDescriptor`
    /// associated with it. It assumes the symbol is user-defined (i.e., not a built-in type).
    ///
    /// # Parameters
    /// - `name`: The name of the symbol whose type descriptor is being retrieved.
    ///
    /// # Returns
    /// - The `TypeDescriptor` of the user-defined symbol.
    ///
    /// # Errors
    /// - Panics if the symbol is not found in the symbol table.
    fn get_user_defined_kind(&self, name: String) -> TypeDescriptor {
        self.symbol_table.names.get(&name).unwrap().kind.clone()
    }

    /// Checks whether a type or symbol exists in the symbol table.
    ///
    /// This function checks if the given name is present in the symbol table, indicating that a type
    /// or symbol has been defined with that name.
    ///
    /// # Parameters
    /// - `name`: The name of the symbol or type to check for.
    ///
    /// # Returns
    /// - `true` if the symbol exists, `false` otherwise.
    fn check_type_exists(&self, name: &String) -> bool {
        self.symbol_table.names.contains_key(name)
    }

    /// Resolves the type of a literal value.
    ///
    /// This function takes a literal token and determines its type (e.g., `int`, `float`, `bool`, `str`).
    /// It retrieves the appropriate `TypeDescriptor` for the literal's type from the symbol table.
    ///
    /// # Parameters
    /// - `literal`: The token representing the literal value.
    ///
    /// # Returns
    /// - The `TypeDescriptor` corresponding to the literal's type.
    ///
    /// # Errors
    /// - Raises an error if the token does not represent a valid literal.
    fn resolve_literal_kind(&self, literal: &Token) -> TypeDescriptor {
        if let TokenKind::Literal(l) = literal.kind {
            match l {
                Literal::Boolean => self.symbol_table.get("bool").unwrap().kind.clone(),
                Literal::Float => self.symbol_table.get("float").unwrap().kind.clone(),
                Literal::Int => self.symbol_table.get("int").unwrap().kind.clone(),
                Literal::String => self.symbol_table.get("str").unwrap().kind.clone(),
            }
        } else {
            gpp_error!("Invalid literal kind. At line {}.", literal.line);
        }
    }

    /// Retrieves a native function's prototype by its name.
    ///
    /// This function looks up a native function by its name in the symbol table and returns its prototype
    /// if it exists. Native functions are predefined in the language.
    ///
    /// # Parameters
    /// - `name`: The name of the native function.
    ///
    /// # Returns
    /// - An `Option<FunctionPrototype>` that represents the native function's prototype, or `None`
    ///   if the function is not found.
    ///
    /// # Example
    /// ```rust
    /// let native_fn = get_native_function("print");
    /// ```
    fn get_native_function(&self, name: &str) -> Option<&FunctionPrototype> {
        self.symbol_table.native_functions.get(name)
    }

    fn analyze_while_stmt(
        &mut self,
        condition: &Expression,
        body: &Statement
    ) -> AnnotatedStatement {
        let annotated_condition = self.analyze_expr(condition);

        let kind = self.resolve_expr_type(condition);
        kind.implements_archetype(&Archetype::new("bool".to_string()));

        let mut annotated_body: Vec<Box<AnnotatedStatement>> = Vec::new();

        match body {
            Statement::Scope(statements) => {
                for stmt in statements {
                    annotated_body.push(Box::new(self.analyze_stmt(stmt)));
                }
            }

            _ => {
                gpp_error!("Only scopes are allowed inside 'while' loop.");
            }
        }

        AnnotatedStatement::While(
            annotated_condition,
            Box::new(AnnotatedStatement::Scope(annotated_body))
        )
    }

    fn analyze_postfix_expr(
        &mut self,
        operator: &Token,
        variable: &Expression
    ) -> AnnotatedExpression {
        if let Expression::Variable(name) = variable {
            let kind = self.resolve_identifier_type(name);

            if !kind.implements_archetype(&Archetype::new("int".to_string())) {
                gpp_error!("Only 'int' instances can be incremented with postfix operators.");
            }

            AnnotatedExpression::PostFix(operator.clone(), Box::new(self.analyze_expr(variable)))
        } else {
            gpp_error!("Only variables can use postfix operators.");
        }
    }

    fn analyze_set_expr(
        &mut self,
        target: Rc<Expression>,
        name: Token,
        value: Rc<Expression>
    ) -> AnnotatedExpression {
        let annotated_target = self.analyze_expr(&target);
        let annotated_value = self.analyze_expr(&value);
        let target_kind = self.resolve_expr_type(&target);
        let value_kind = self.resolve_expr_type(&value);

        // self.assert_kind_equals(
        //     value_kind,
        //     target_kind,
        //     "Cannot assign instance field with different kind.".to_string()
        // );

        AnnotatedExpression::Set(
            Box::new(annotated_target),
            name,
            Box::new(annotated_value),
            target_kind
        )
    }

    fn analyze_list_get_expr(
        &mut self,
        expression: Box<Expression>,
        index: Box<Expression>
    ) -> AnnotatedExpression {
        let annotated_expression = self.analyze_expr(&expression);
        let annotated_index = self.analyze_expr(&index);

        AnnotatedExpression::ListGet(Box::new(annotated_expression), Box::new(annotated_index))
    }

    fn resolve_list_get_type(&mut self, list: &Expression, index: &Expression) -> TypeDescriptor {
        self.resolve_expr_type(list)
    }

    fn analyze_native_function(
        &mut self,
        name: &Token,
        params: &Vec<FieldDeclaration>,
        return_kind: &Expression
    ) -> AnnotatedStatement {
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
            kind = self.get_static_kind("void");

            self.report_error(
                CompilationError::new("Missing function return kind.".to_string(), Some(name.line))
            );
        }

        let function_definition = FunctionPrototype::new(
            name.lexeme.clone(),
            params.clone(),
            params.len(),
            kind.clone()
        );

        self.define_native_function(name.lexeme.clone(), function_definition.clone());

        self.current_symbol = name.lexeme.clone();

        AnnotatedStatement::NativeFunction(function_definition)
    }

    fn define_native_function(&mut self, name: String, value: FunctionPrototype) {
        self.symbol_table.native_functions.insert(name, value);
    }
}
