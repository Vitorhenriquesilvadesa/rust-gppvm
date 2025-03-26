use std::{ cell::RefCell, cmp::Ordering, collections::HashMap, rc::Rc };

use crate::gpp_error;

use super::{
    ast::FieldDeclaration,
    chunk::{ CompileTimeChunk, CompileTimeValue },
    errors::CompilerErrorReporter,
    instructions::Instruction,
    lexer::{ KeywordKind, Literal, OperatorKind, Token, TokenKind },
    semantics::{
        AnnotatedAST,
        AnnotatedExpression,
        AnnotatedStatement,
        FunctionPrototype,
        SemanticCode,
        SymbolTable,
        TypeDescriptor,
        Value,
    },
};

pub struct CompileTimeStack {
    values: Vec<CompileTimeValue>,
}

impl CompileTimeStack {
    pub fn new() -> Self {
        Self {
            values: Vec::new(),
        }
    }

    pub fn push(&mut self, value: CompileTimeValue) {
        self.values.push(value);
    }

    pub fn pop(&mut self) -> CompileTimeValue {
        self.values.pop().unwrap()
    }
}

pub struct IRGenerator {
    semantic_code: SemanticCode,
    reporter: Rc<RefCell<CompilerErrorReporter>>,
    top_level_graph: CodeGraph,
    pub functions: HashMap<String, IRFunction>,
    pub kinds: HashMap<String, IRType>,
    current_chunk: CompileTimeChunk,
}

impl IRGenerator {
    pub fn new() -> Self {
        Self {
            semantic_code: SemanticCode::new(SymbolTable::new(), AnnotatedAST::new(Vec::new())),
            reporter: Rc::new(RefCell::new(CompilerErrorReporter::new())),
            functions: HashMap::new(),
            kinds: HashMap::new(),
            top_level_graph: CodeGraph::new(HashMap::new()),
            current_chunk: CompileTimeChunk::empty(),
        }
    }

    pub fn generate(
        &mut self,
        reporter: Rc<RefCell<CompilerErrorReporter>>,
        semantic_code: &SemanticCode
    ) -> IntermediateCode {
        self.semantic_code = semantic_code.clone();
        self.reporter = reporter;

        for annotated_stmt in self.semantic_code.ast.statements.clone() {
            self.generate_ir_for(&annotated_stmt);
        }

        IntermediateCode::new(
            self.functions.clone(),
            self.kinds.clone(),
            self.top_level_graph.clone()
        )
    }

    fn generate_ir_for(&mut self, annotated_stmt: &AnnotatedStatement) {
        match annotated_stmt {
            AnnotatedStatement::Decorator(name, attributes) => {}
            AnnotatedStatement::EndCode => {}
            AnnotatedStatement::Expression(expression) => {}
            AnnotatedStatement::ForEach(variable, condition, body) => {}
            AnnotatedStatement::Function(prototype, body) => {
                self.generate_function_ir(prototype, body);
            }
            AnnotatedStatement::Global => {}
            AnnotatedStatement::If(keyword, condition, then_branch, else_branch) => {}
            AnnotatedStatement::Return(value) => {}
            AnnotatedStatement::Scope(statements) => {
                self.generate_scope_ir(statements);
            }
            AnnotatedStatement::Type(descriptor) => {}
            AnnotatedStatement::Variable(name, value) => {
                self.generate_variable_decl_ir(name, value);
            }
            AnnotatedStatement::While(condition, body) => {}
        }
    }

    fn is_valid_ir_statement(&self, statement: &AnnotatedStatement) -> bool {
        matches!(
            statement,
            AnnotatedStatement::Expression(_) |
                AnnotatedStatement::If(_, _, _, _) |
                AnnotatedStatement::ForEach(_, _, _) |
                AnnotatedStatement::Return(_) |
                AnnotatedStatement::Scope(_) |
                AnnotatedStatement::While(_, _) |
                AnnotatedStatement::Variable(_, _)
        )
    }

    fn generate_function_ir(&mut self, prototype: &FunctionPrototype, body: &AnnotatedStatement) {
        self.current_chunk = CompileTimeChunk::empty();

        if let AnnotatedStatement::Scope(stmts) = body {
            self.generate_ir_for(body);
        }

        let ir_function = IRFunction::new(
            self.top_level_graph.get_id_for_new_edge(prototype.name.clone()),
            self.current_chunk.clone(),
            prototype.arity as u8
        );

        self.functions.insert(prototype.name.clone(), ir_function);
    }

    fn generate_variable_decl_ir(&mut self, name: &Token, value: &Option<AnnotatedExpression>) {
        match value {
            Some(v) => {
                self.generate_expr_ir(v);
            }
            None => {}
        }
    }

    fn generate_scope_ir(&mut self, statements: &[Box<AnnotatedStatement>]) {
        for stmt in statements {
            self.generate_ir_for(stmt);
        }
    }

    fn generate_expr_ir(&mut self, expr: &AnnotatedExpression) -> Vec<u8> {
        match expr {
            AnnotatedExpression::Arithmetic(left, op, right, kind) => {
                self.generate_arithmetic_expr_ir(left, op, right, kind)
            }

            AnnotatedExpression::Assign(name, value, kind) => {
                self.generate_assign_expr_ir(name, value, kind)
            }

            AnnotatedExpression::Literal(token, kind) => { self.generate_literal_ir(token, kind) }

            _ => { Vec::new() }
        }
    }

    fn generate_arithmetic_expr_ir(
        &mut self,
        left: &AnnotatedExpression,
        op: &Token,
        right: &AnnotatedExpression,
        kind: &TypeDescriptor
    ) -> Vec<u8> {
        let mut left_bytes = self.generate_expr_ir(right);
        let mut right_bytes = self.generate_expr_ir(left);
        let mut operator = self.convert_operator_to_instruction(op) as u8;

        let mut all_bytes: Vec<u8> = Vec::new();

        all_bytes.append(&mut left_bytes);
        all_bytes.append(&mut right_bytes);
        all_bytes.push(operator);

        all_bytes
    }

    fn generate_literal_ir(&mut self, token: &Token, kind: &TypeDescriptor) -> Vec<u8> {
        let constant = self.get_constant(token, kind);
        let mut bytes = Vec::new();

        if constant.is_bool() {
            if let CompileTimeValue::Boolean(b) = constant {
                if b {
                    bytes.push(Instruction::True as u8);
                } else {
                    bytes.push(Instruction::False as u8);
                }
            }
        } else {
            let index = self.current_chunk.add_constant(constant);
            bytes.push(Instruction::Push as u8);

            let (high, low) = self.split_u16(index);
            bytes.push(high);
            bytes.push(low);
        }

        bytes
    }

    fn get_constant(&self, token: &Token, kind: &TypeDescriptor) -> CompileTimeValue {
        if let TokenKind::Literal(l) = token.kind {
            match l {
                Literal::Boolean => {
                    if token.lexeme.cmp(&String::from("true")) == Ordering::Equal {
                        CompileTimeValue::Boolean(true)
                    } else {
                        CompileTimeValue::Boolean(false)
                    }
                }
                Literal::String => { CompileTimeValue::String(token.lexeme.clone()) }
                Literal::Int => CompileTimeValue::Int(token.lexeme.parse::<i32>().unwrap()),
                Literal::Float => CompileTimeValue::Float(token.lexeme.parse::<f32>().unwrap()),
            }
        } else {
            gpp_error!("Invalid literal kind.");
        }
    }

    fn generate_assign_expr_ir(
        &self,
        name: &Token,
        value: &AnnotatedExpression,
        kind: &TypeDescriptor
    ) -> Vec<u8> {
        Vec::<u8>::new()
    }

    fn split_u16(&self, short: u16) -> (u8, u8) {
        let high = (short >> 8) as u8;
        let low = (short & 0xff) as u8;

        (high, low)
    }

    fn convert_operator_to_instruction(&self, op: &Token) -> Instruction {
        if let TokenKind::Operator(operator) = op.kind {
            match operator {
                OperatorKind::And => Instruction::And,
                OperatorKind::Or => Instruction::Or,
                OperatorKind::Star => Instruction::Mul,
                OperatorKind::Slash => Instruction::Div,
                OperatorKind::Plus => Instruction::Add,
                OperatorKind::Minus => Instruction::Sub,
                OperatorKind::Not => Instruction::Not,
                OperatorKind::EqualEqual => Instruction::Cmp,
                OperatorKind::BitwiseAnd => Instruction::BitAnd,
                OperatorKind::BitwiseOr => Instruction::BitOr,
                OperatorKind::DoubleStar => Instruction::Pow,
                OperatorKind::Less => Instruction::LessThan,
                OperatorKind::LessEqual => Instruction::LessEqual,
                OperatorKind::Greater => Instruction::GreaterThan,
                OperatorKind::GreaterEqual => Instruction::GreaterEqual,
                OperatorKind::NotEqual => Instruction::Neq,
                OperatorKind::Equal => Instruction::Eq,
                OperatorKind::Arrow => todo!(),
                _ => {
                    todo!();
                }
            }
        } else {
            gpp_error!("Invalid operator to instruction conversion.");
        }
    }

    fn emit_byte(&mut self, byte: u8) {
        self.current_chunk.write(byte);
    }

    fn emit_instruction(&mut self, instruction: Instruction) {
        self.current_chunk.write(instruction.into());
    }
}

#[derive(Debug, Clone)]
pub struct IRType {
    id: u32,
    fields: HashMap<String, u8>,
    chunk: CompileTimeChunk,
}

#[derive(Debug, Clone)]
pub struct IRFunction {
    pub id: u32,
    pub chunk: CompileTimeChunk,
    pub arity: u8,
}

impl IRFunction {
    pub fn new(id: u32, chunk: CompileTimeChunk, arity: u8) -> Self {
        Self { id, chunk, arity }
    }
}

#[derive(Debug, Clone)]
pub struct CodeGraph {
    connections: HashMap<String, u32>,
    current_id: u32,
}

impl CodeGraph {
    pub fn new(connections: HashMap<String, u32>) -> Self {
        Self { connections, current_id: 0 }
    }

    pub fn get_id_for_new_edge(&mut self, name: String) -> u32 {
        let id = self.current_id;
        self.current_id += 1;

        self.connections.insert(name, id);

        return id;
    }
}

#[derive(Debug, Clone)]
pub struct IntermediateCode {
    pub functions: HashMap<String, IRFunction>,
    pub kinds: HashMap<String, IRType>,
    pub graph: CodeGraph,
}

impl IntermediateCode {
    pub fn new(
        functions: HashMap<String, IRFunction>,
        kinds: HashMap<String, IRType>,
        graph: CodeGraph
    ) -> Self {
        Self { functions, kinds, graph }
    }
}
