pub struct CompilerArguments {
    pub args: Vec<String>,
}

impl CompilerArguments {
    pub fn new(args: Vec<String>) -> Self {
        Self { args }
    }
}
