use gppvm::compiler::Compiler;

fn main() {
    let source = String::from("+-*/");

    let mut compiler = Compiler::new();

    compiler.compile(source);
}
