#![allow(dead_code)]
#![allow(unused_variables)]
use gppvm_runtime::Value;

pub struct Bytecode {
    functions: Vec<Function>,
}

impl Bytecode {
    pub fn new(functions: Vec<Function>) -> Self {
        Self { functions }
    }
}

#[derive(Debug)]
pub struct Chunk {
    pub constants: Vec<Value>,
    pub code: Vec<u8>,
}

impl Chunk {
    pub fn new(constants: Vec<Value>, code: Vec<u8>) -> Self {
        Self { constants, code }
    }
}

#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub chunk: Chunk,
    pub arity: u8,
}

impl Function {
    pub fn new(name: String, arity: u8, chunk: Chunk) -> Self {
        Self { name, arity, chunk }
    }
}

type FunctionPtr = fn(Vec<Value>);

pub struct NativeFunction {
    pub arity: u8,
    pub fn_ptr: FunctionPtr,
}
