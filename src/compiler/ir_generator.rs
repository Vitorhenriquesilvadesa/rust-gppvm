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

#[derive(Debug, Clone)]
struct LocalValue {
    name: String,
    depth: u32,
    is_initialized: bool,
}

impl LocalValue {
    fn new(name: String, depth: u32, is_initialized: bool) -> Self {
        Self { name, depth, is_initialized }
    }
}

#[derive(Debug, Clone)]
pub struct CompileTimeStack {
    values: Vec<LocalValue>,
}

impl CompileTimeStack {
    pub fn new() -> Self {
        Self {
            values: Vec::new(),
        }
    }

    pub fn push(&mut self, value: LocalValue) {
        self.values.push(value);
    }

    pub fn pop(&mut self) -> LocalValue {
        self.values.pop().unwrap()
    }

    pub fn count(&self) -> usize {
        self.values.len()
    }
}

pub struct IRGenerator {
    semantic_code: SemanticCode,
    reporter: Rc<RefCell<CompilerErrorReporter>>,
    top_level_graph: CodeGraph,
    pub functions: HashMap<String, IRFunction>,
    pub kinds: HashMap<String, IRType>,
    current_chunk: CompileTimeChunk,
    local_values: CompileTimeStack,
    current_depth: u32,
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
            current_depth: 0,
            local_values: CompileTimeStack::new(),
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
            AnnotatedStatement::Expression(expression) => {
                let code = self.generate_expr_ir(expression);

                for byte in code {
                    self.emit_byte(byte);
                }
            }
            AnnotatedStatement::ForEach(variable, condition, body) => {}
            AnnotatedStatement::Function(prototype, body) => {
                self.generate_function_ir(prototype, body);
            }
            AnnotatedStatement::Global => {}
            AnnotatedStatement::If(keyword, condition, then_branch, else_branch) => {
                self.generate_if_ir(keyword, condition, then_branch, else_branch);
            }
            AnnotatedStatement::Return(value) => {
                self.generate_return_ir(value);
            }
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

        self.begin_scope();

        for (i, param) in prototype.params.iter().enumerate() {
            self.declare_local(param.name.lexeme.clone(), true);
        }

        if let AnnotatedStatement::Scope(stmts) = body {
            for stmt in stmts {
                self.generate_ir_for(stmt);
            }
        }

        self.end_scope();

        let ir_function = IRFunction::new(
            self.top_level_graph.get_id_for_new_edge(prototype.name.clone()),
            self.current_chunk.clone(),
            prototype.arity as u8
        );

        self.functions.insert(prototype.name.clone(), ir_function);
    }

    fn generate_variable_decl_ir(&mut self, name: &Token, value: &Option<AnnotatedExpression>) {
        self.declare_local(name.lexeme.clone(), true);

        match value {
            Some(v) => {
                let value_code = self.generate_expr_ir(v);

                for byte in value_code {
                    self.emit_byte(byte);
                }

                self.emit_instruction(Instruction::SetLocal);

                // The variable are on top of VM stack after declare with initializer.
                self.emit_byte(self.get_in_depth(name.lexeme.clone()) as u8);
            }
            None => {}
        }
    }

    fn mark_local_initialized(&mut self, name: String) {}

    fn get_value_in_stack(&mut self, depth: u32) -> &LocalValue {
        &self.local_values.values[depth as usize]
    }

    fn get_in_depth(&self, name: String) -> u32 {
        for (index, value) in self.local_values.values.iter().enumerate() {
            if value.name == name {
                return index as u32;
            }
        }

        return 0;
    }

    fn declare_local(&mut self, name: String, is_initialized: bool) {
        self.local_values.push(LocalValue::new(name, self.current_depth, is_initialized));
    }

    fn generate_scope_ir(&mut self, statements: &[Box<AnnotatedStatement>]) {
        self.begin_scope();

        for stmt in statements {
            self.generate_ir_for(stmt);
        }

        self.end_scope();
    }

    fn generate_expr_ir(&mut self, expr: &AnnotatedExpression) -> Vec<u8> {
        match expr {
            AnnotatedExpression::Arithmetic(left, op, right, kind) => {
                self.generate_arithmetic_expr_ir(left, op, right, kind)
            }

            AnnotatedExpression::Call(proto, callee, args, kind) => {
                self.generate_call_expr_ir(proto, callee, args, kind)
            }

            AnnotatedExpression::Assign(name, value, kind) => {
                self.generate_assign_expr_ir(name, value, kind)
            }

            AnnotatedExpression::Variable(name, kind) => {
                self.generate_variable_expr_ir(name, kind)
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
        let mut right_bytes = self.generate_expr_ir(left);
        let mut left_bytes = self.generate_expr_ir(right);
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
        &mut self,
        name: &Token,
        value: &AnnotatedExpression,
        kind: &TypeDescriptor
    ) -> Vec<u8> {
        let mut code = Vec::new();
        let index = self.get_in_depth(name.lexeme.clone());
        self.mark_local_initialized(name.lexeme.clone());

        let mut value_code = self.generate_expr_ir(value);
        code.append(&mut value_code);

        code.push(Instruction::SetLocal as u8);
        code.push(index as u8);

        code
    }

    fn split_u16(&self, short: u16) -> (u8, u8) {
        let high = (short >> 8) as u8;
        let low = (short & 0xff) as u8;

        (high, low)
    }

    fn split_u32(&self, value: u32) -> (u8, u8, u8, u8) {
        let byte1 = (value >> 24) as u8;
        let byte2 = (value >> 16) as u8;
        let byte3 = (value >> 8) as u8;
        let byte4 = value as u8;

        (byte1, byte2, byte3, byte4)
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
                OperatorKind::Less => Instruction::Less,
                OperatorKind::LessEqual => Instruction::LessEqual,
                OperatorKind::Greater => Instruction::Greater,
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

    fn begin_scope(&mut self) {
        self.current_depth += 1;
    }

    fn end_scope(&mut self) {
        for value in self.local_values.values.iter().rev() {
            if value.depth < self.current_depth {
                break;
            }
        }

        self.current_depth -= 1;
    }

    fn generate_variable_expr_ir(&self, name: &Token, kind: &TypeDescriptor) -> Vec<u8> {
        let index = self.get_in_depth(name.lexeme.clone());

        vec![Instruction::GetLocal as u8, index as u8]
    }

    fn generate_return_ir(&mut self, value: &AnnotatedExpression) {
        let code = self.generate_expr_ir(value);

        for byte in code {
            self.emit_byte(byte);
        }

        self.emit_instruction(Instruction::Ret);
    }

    fn generate_call_expr_ir(
        &mut self,
        proto: &FunctionPrototype,
        callee: &Token,
        args: &[Box<AnnotatedExpression>],
        kind: &TypeDescriptor
    ) -> Vec<u8> {
        let mut code = Vec::new();
        let function_table_index = self.top_level_graph.get_function_id(&proto.name);

        for arg in args {
            let mut arg_code = self.generate_expr_ir(arg);
            code.append(&mut arg_code);
        }

        code.push(Instruction::Call as u8);

        let index_bytes = self.split_u32(function_table_index);

        code.push(index_bytes.0);
        code.push(index_bytes.1);
        code.push(index_bytes.2);
        code.push(index_bytes.3);

        code.push(proto.arity as u8);

        code
    }

    fn generate_if_ir(
        &mut self,
        keyword: &Token,
        condition: &AnnotatedExpression,
        then_branch: &AnnotatedStatement,
        else_branch: &Option<Box<AnnotatedStatement>>
    ) {
        let mut condition_code = self.generate_expr_ir(condition);
    }

    fn get_current_chunk_offset(&self) -> usize {
        self.current_chunk.code.len()
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

    fn get_function_id(&self, name: &str) -> u32 {
        self.connections[name]
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
