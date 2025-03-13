use super::{ parser::FieldDeclaration, semantics::{ SemanticCode, SymbolTable } };

pub struct IRGenerator {
    semantic_code: SemanticCode,
}

impl IRGenerator {
    pub fn new() -> Self {
        Self { semantic_code: SemanticCode::new(SymbolTable::new(), Vec::new()) }
    }

    pub fn generate(&mut self, semantic_code: &SemanticCode) -> IntermediateCode {
        self.semantic_code = semantic_code.clone();

        //println!("{:#?}", self.semantic_code);

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
