use super::semantics::Value;

#[derive(Debug, Clone, PartialEq)]
pub enum CompileTimeValue {
    Int(i32),
    Float(f32),
    String(String),
    Boolean(bool),
    Object(CompileTimeObject),
}

impl CompileTimeValue {
    pub fn is_int(&self) -> bool {
        matches!(self, CompileTimeValue::Int(v))
    }

    pub fn is_float(&self) -> bool {
        matches!(self, CompileTimeValue::Float(v))
    }

    pub fn is_str(&self) -> bool {
        matches!(self, CompileTimeValue::String(v))
    }

    pub fn is_bool(&self) -> bool {
        matches!(self, CompileTimeValue::Boolean(v))
    }

    pub fn is_object(&self) -> bool {
        matches!(self, CompileTimeValue::Object(v))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CompileTimeObject {}

#[derive(Debug, Clone)]
pub struct CompileTimeChunk {
    pub code: Vec<u8>,
    pub lines: Vec<usize>,
    pub constants: Vec<CompileTimeValue>,
}

impl CompileTimeChunk {
    pub fn empty() -> Self {
        Self { code: Vec::new(), lines: Vec::new(), constants: Vec::new() }
    }

    pub fn write(&mut self, instruction: u8) {
        self.code.push(instruction);
    }

    pub fn add_constant(&mut self, constant: CompileTimeValue) -> u16 {
        if !self.constants.contains(&constant) {
            self.constants.push(constant);
            (self.constants.len() as u16) - 1
        } else {
            for (index, value) in self.constants.iter().enumerate() {
                if value.eq(&constant) {
                    return index as u16;
                }
            }

            return 0u16;
        }
    }
}
