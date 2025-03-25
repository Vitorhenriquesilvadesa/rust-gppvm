use std::{ cell::RefCell, rc::Rc };

use super::{
    ast::FieldDeclaration,
    errors::CompilerErrorReporter,
    semantics::{ AnnotatedAST, SemanticCode, SymbolTable },
};

pub struct IRGenerator {
    semantic_code: SemanticCode,
    reporter: Rc<RefCell<CompilerErrorReporter>>,
}

impl IRGenerator {
    pub fn new() -> Self {
        Self {
            semantic_code: SemanticCode::new(SymbolTable::new(), AnnotatedAST::new(Vec::new())),
            reporter: Rc::new(RefCell::new(CompilerErrorReporter::new())),
        }
    }

    pub fn generate(
        &mut self,
        reporter: Rc<RefCell<CompilerErrorReporter>>,
        semantic_code: &SemanticCode
    ) -> IntermediateCode {
        self.semantic_code = semantic_code.clone();
        self.reporter = reporter;

        println!("{:#?}", self.semantic_code.ast);

        IntermediateCode::new()
    }
}

pub struct IRType {
    name: String,
    fields: Vec<FieldDeclaration>,
}

pub struct IRFunction {}

pub struct IntermediateCode {}

impl IntermediateCode {
    pub fn new() -> Self {
        Self {}
    }
}
