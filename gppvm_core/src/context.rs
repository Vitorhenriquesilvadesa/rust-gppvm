use std::{ cell::RefCell, path::PathBuf, rc::Rc };

use shared_components::{ CompilerErrorReporter, SemanticCode, Statement, Token };

pub struct CompilerContext {
    pub output: PathBuf,
    pub source: String,
    pub reporter: Rc<RefCell<CompilerErrorReporter>>,
    pub tokens: Option<Vec<Token>>,
    pub statements: Option<Vec<Statement>>,
    pub annotated_ast: Option<SemanticCode>
}

impl Default for CompilerContext {
    fn default() -> Self {
        Self {
            output: PathBuf::default(),
            source: String::default(),
            reporter: Rc::new(RefCell::new(CompilerErrorReporter::default())),
            tokens: None,
            statements: None,
            annotated_ast: None,
        }
    }
}

impl CompilerContext {}
