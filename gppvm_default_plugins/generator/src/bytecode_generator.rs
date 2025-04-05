#![allow(dead_code)]
#![allow(unused_variables)]
use std::{ alloc::{ alloc, Layout }, ptr, rc::Rc };

use gppvm_runtime::{ As, ObjDescriptor, ObjString, Value, ValueKind };
use shared_components::gpp_error;
use crate::bytecode::{ Bytecode, Chunk, Function };

use intermediate::{ CompileTimeValue, IRFunction, IntermediateCode };

pub struct BytecodeGenerator {}

impl BytecodeGenerator {
    pub fn new() -> Self {
        Self {}
    }

    pub fn generate(&mut self, ir_code: &IntermediateCode) -> Bytecode {
        let mut functions: Vec<Function> = Vec::new();

        for (name, function) in &ir_code.functions {
            functions.push(self.generate_bytecode_for(name, function, ir_code));
        }

        Bytecode::new(functions)
    }

    fn generate_bytecode_for(
        &self,
        name: &str,
        function: &IRFunction,
        ir_code: &IntermediateCode
    ) -> Function {
        let ct_chunk = &function.chunk;
        let ct_constants = &ct_chunk.constants;

        let code = ct_chunk.code.clone();
        let mut constants: Vec<Value> = Vec::new();

        for ct_constant in ct_constants {
            let kind = match ct_constant {
                CompileTimeValue::Bool(_) => ValueKind::Boolean,
                CompileTimeValue::Float(_) => ValueKind::Float,
                CompileTimeValue::Int(_) => ValueKind::Int,
                CompileTimeValue::Str(_) => ValueKind::String,
            };

            let as_wrapper = match kind {
                ValueKind::Boolean => {
                    if let CompileTimeValue::Bool(b) = ct_constant {
                        As { boolean: b.clone() }
                    } else {
                        As { boolean: false }
                    }
                }

                ValueKind::Float => { As { boolean: ct_constant.as_bool().unwrap() } }

                ValueKind::Int => { As { int: ct_constant.as_int().unwrap() } }

                ValueKind::String => {
                    let layout: Layout = Layout::new::<ObjString>();
                    let obj: *mut ObjDescriptor = (unsafe { alloc(layout) }) as *mut ObjDescriptor;

                    unsafe {
                        ptr::write(
                            obj as *mut ObjString,
                            ObjString::new(
                                Rc::new(ct_constant.as_str().clone().unwrap().to_string())
                            )
                        );
                    }

                    As { object: obj }
                }

                ValueKind::Object => {
                    gpp_error!("Cannot create complex object constant.");
                }
            };

            constants.push(Value::new(kind, as_wrapper));
        }

        let function = Function::new(
            function.name.clone(),
            function.arity,
            Chunk::new(constants, code)
        );

        println!("{:#?}", function);

        function
    }
}
