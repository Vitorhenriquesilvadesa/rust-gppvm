use std::{cmp::Ordering, collections::HashMap, rc::Rc};

use crate::{
    gpp_error,
    runtime::{
        objects::{Object, Value},
        virtual_machine::Chunk,
    },
};

use super::ir_generator::IntermediateCode;

pub struct BytecodeGenerator {}

#[derive(Clone, Debug)]
pub struct VirtualFunction {
    pub id: u32,
    pub chunk: Rc<Chunk>,
}

impl VirtualFunction {
    pub fn new(id: u32, chunk: Rc<Chunk>) -> Self {
        Self { id, chunk }
    }
}

#[derive(Debug, Clone)]
pub struct NativeFunctionInfo {
    pub arity: u8,
    pub id: u32,
}

impl NativeFunctionInfo {
    pub fn new(arity: u8, id: u32) -> Self {
        Self { arity, id }
    }
}

#[derive(Clone, Debug)]
pub struct Bytecode {
    functions: HashMap<u32, VirtualFunction>,
    pub native_functions: HashMap<String, NativeFunctionInfo>,
    pub v_tables: HashMap<u32, Vec<VirtualFunction>>,
    pub main: Option<VirtualFunction>,
}

impl Bytecode {
    pub fn new(
        functions: HashMap<u32, VirtualFunction>,
        native_functions: HashMap<String, NativeFunctionInfo>,
        v_tables: HashMap<u32, Vec<VirtualFunction>>,
        main: Option<VirtualFunction>,
    ) -> Self {
        Self {
            functions,
            native_functions,
            v_tables,
            main,
        }
    }

    pub(crate) fn get_function(&self, function_id: u32) -> Rc<Chunk> {
        self.functions[&function_id].chunk.clone()
    }
}

impl BytecodeGenerator {
    pub fn new() -> Self {
        Self {}
    }

    pub fn generate(&self, ir: &IntermediateCode) -> Bytecode {
        let mut functions: HashMap<u32, VirtualFunction> = HashMap::new();
        let mut main: Option<VirtualFunction> = None;
        let mut v_tables: HashMap<u32, Vec<VirtualFunction>> = HashMap::new();

        for function in &ir.functions {
            let mut code = function.1.chunk.code.clone();
            let mut constants = Vec::new();

            for constant in &function.1.chunk.constants {
                let c: Value;

                match constant {
                    super::chunk::CompileTimeValue::Int(v) => {
                        c = Value::Int(v.clone());
                    }
                    super::chunk::CompileTimeValue::Float(v) => {
                        c = Value::Float(v.clone());
                    }
                    super::chunk::CompileTimeValue::String(v) => {
                        c = Value::String(Rc::new(v.clone()));
                    }
                    super::chunk::CompileTimeValue::Boolean(v) => {
                        c = Value::Bool(v.clone());
                    }
                    super::chunk::CompileTimeValue::Object(v) => {
                        gpp_error!("Cannot create complex object constants.");
                    }
                }

                constants.push(c);
            }

            let chunk = Chunk::new(code, constants);
            let virtual_function = VirtualFunction::new(function.1.id, Rc::new(chunk));

            if function.0 == "main" {
                main = Some(virtual_function);
            } else {
                functions.insert(function.1.id, virtual_function);
            }
        }

        for (desc, v_table) in &ir.methods {
            for method in v_table {
                let mut code = method.chunk.code.clone();
                let mut constants = Vec::new();

                for constant in &method.chunk.constants {
                    let c: Value;

                    match constant {
                        super::chunk::CompileTimeValue::Int(v) => {
                            c = Value::Int(v.clone());
                        }
                        super::chunk::CompileTimeValue::Float(v) => {
                            c = Value::Float(v.clone());
                        }
                        super::chunk::CompileTimeValue::String(v) => {
                            c = Value::String(Rc::new(v.clone()));
                        }
                        super::chunk::CompileTimeValue::Boolean(v) => {
                            c = Value::Bool(v.clone());
                        }
                        super::chunk::CompileTimeValue::Object(v) => {
                            gpp_error!("Cannot create complex object constants.");
                        }
                    }

                    constants.push(c);
                }

                let chunk = Chunk::new(code, constants);
                let virtual_function = VirtualFunction::new(method.id, Rc::new(chunk));

                if v_tables.contains_key(&desc.id) {
                    v_tables.get_mut(&desc.id).unwrap().push(virtual_function);
                } else {
                    v_tables.insert(desc.id, vec![virtual_function]);
                }
            }
        }

        Bytecode::new(functions, ir.native_functions.clone(), v_tables, main)
    }
}
