use crate::context::CompilerContext;

pub enum StageKind {
    Lexer,
    Parser,
    Semantic,
    IRGenerator,
    BytecodeGenerator,
    Custom(&'static str),
}

pub trait Stage {
    fn get_name(&self) -> &'static str;
    fn state(&self) -> StageKind;
    fn run(&mut self, ctx: &mut CompilerContext);
}
