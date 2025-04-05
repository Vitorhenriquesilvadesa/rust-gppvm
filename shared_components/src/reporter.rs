#[macro_export]
macro_rules! gpp_error {
    ($($arg:tt)*) => {
        {
            eprintln!("\x1b[31mError\x1b[0m: {}", format_args!($($arg)*));
            std::process::exit(1);
        }
    };
}

#[derive(Debug, Clone)]
pub enum CompilationErrorKind {
    IllegalCharacter,
}

#[derive(Debug)]
pub struct ParseError {
    pub message: CompilerMessage,
    pub line: usize,
}

impl ParseError {
    pub fn new(message: CompilerMessage, line: usize) -> Self {
        Self { message, line }
    }
}

#[derive(Clone, Debug)]
pub enum Severity {
    Info,
    Warn,
    Error,
}

#[derive(Clone, Debug)]
pub enum Color {
    Red,
    Orange,
    Green,
    Yellow,
    White,
    Purple,
}

#[derive(Clone, Debug)]
pub struct TextFragment {
    pub content: String,
    pub color: Color,
}

impl TextFragment {
    pub fn new(content: String, color: Color) -> Self {
        Self { content, color }
    }
}

#[derive(Clone, Debug)]
pub struct CompilerMessage {
    pub fragments: Vec<TextFragment>,
    pub severity: Severity,
    current_color: Color,
}

impl CompilerMessage {
    pub fn new(severity: Severity) -> Self {
        Self { severity, fragments: Vec::new(), current_color: Color::White }
    }

    pub fn color(mut self, color: Color) -> Self {
        self.current_color = color;
        self
    }

    pub fn append(mut self, content: String) -> Self {
        self.fragments.push(TextFragment::new(content, self.current_color.clone()));
        self
    }
}

#[derive(Debug, Clone)]
pub struct CompilationError {
    pub msg: CompilerMessage,
    pub kind: CompilationErrorKind,
    pub line: Option<usize>,
}

impl CompilationError {
    pub fn new(msg: CompilerMessage, line: Option<usize>) -> Self {
        Self { msg, kind: CompilationErrorKind::IllegalCharacter, line }
    }
}

#[derive(Debug, Clone)]
pub struct CompilerErrorStack {
    errors: Vec<CompilationError>,
}

impl Default for CompilerErrorStack {
    fn default() -> Self {
        Self { errors: Default::default() }
    }
}

impl CompilerErrorStack {
    pub fn new() -> Self {
        CompilerErrorStack { errors: Vec::new() }
    }

    pub fn push(&mut self, error: CompilationError) {
        self.errors.push(error);
    }

    pub fn get_errors(&self) -> &Vec<CompilationError> {
        &self.errors
    }
}

#[derive(Debug, Clone)]
pub struct CompilerErrorReporter {
    stack: CompilerErrorStack,
}

impl Default for CompilerErrorReporter {
    fn default() -> Self {
        Self { stack: Default::default() }
    }
}

impl CompilerErrorReporter {
    pub fn new() -> Self {
        Self { stack: CompilerErrorStack::new() }
    }

    pub fn report_error(&mut self, error: CompilationError) {
        self.stack.push(error);
    }

    pub fn get_errors(&self) -> &CompilerErrorStack {
        &self.stack
    }

    pub fn has_errors(&self) -> bool {
        !self.stack.errors.is_empty()
    }
}
