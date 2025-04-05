#![allow(dead_code)]
#![allow(unused_variables)]

#[derive(Debug, Clone, PartialEq)]
pub enum CompileTimeValue {
    Int(i32),
    Float(f32),
    Str(String),
    Bool(bool),
}

impl CompileTimeValue {
    pub fn is_int(&self) -> bool {
        matches!(self, CompileTimeValue::Int(v))
    }

    pub fn is_float(&self) -> bool {
        matches!(self, CompileTimeValue::Float(v))
    }

    pub fn is_str(&self) -> bool {
        matches!(self, CompileTimeValue::Str(v))
    }

    pub fn is_bool(&self) -> bool {
        matches!(self, CompileTimeValue::Bool(v))
    }

    pub fn as_float(&self) -> Option<f32> {
        if let CompileTimeValue::Float(v) = self { Some(*v) } else { None }
    }

    pub fn as_int(&self) -> Option<i32> {
        if let CompileTimeValue::Int(v) = self { Some(*v) } else { None }
    }

    pub fn as_str(&self) -> Option<&str> {
        if let CompileTimeValue::Str(v) = self { Some(v.as_str()) } else { None }
    }

    pub fn as_bool(&self) -> Option<bool> {
        if let CompileTimeValue::Bool(v) = self { Some(*v) } else { None }
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
