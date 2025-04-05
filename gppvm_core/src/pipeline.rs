use std::path::PathBuf;

use crate::{ context::CompilerContext, Stage };

pub struct CompilationPipeline {
    context: CompilerContext,
    root: String,
    stages: Vec<Box<dyn Stage>>,
}

impl CompilationPipeline {
    pub fn new() -> Self {
        Self { context: CompilerContext::default(), stages: Vec::new(), root: String::default() }
    }

    pub fn with_output(mut self, path: PathBuf) -> Self {
        self.context.output = path;
        self
    }

    pub fn add_stage<T: Stage + Default + 'static>(&mut self) -> &mut Self {
        self.stages.push(Box::new(T::default()));
        self
    }

    pub fn execute(&mut self) {
        for stage in &mut self.stages {
            println!("Running {} pass...", stage.get_name());
            stage.run(&mut self.context);

            if self.context.reporter.borrow().has_errors() {
                for error in self.context.reporter.borrow().get_errors() {
                    match error.line {
                        None => {
                            println!("ERROR: {}.", error.msg);
                        }

                        Some(line) => {
                            println!("ERROR: {}. At line {}.", error.msg, line);
                        }
                    }
                }

                return;
            }
        }
    }

    pub fn with_source(mut self, source: String) -> Self {
        self.context.source = source;
        self
    }
}
