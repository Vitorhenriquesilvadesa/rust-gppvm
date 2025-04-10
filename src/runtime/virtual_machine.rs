use std::{ cell::RefCell, rc::Rc };
use core::fmt::Debug;

use crate::{
    compiler::{ bytecode_gen::Bytecode, instructions::Instruction },
    runtime::objects::{ AsRaw, ObjectKind },
};

use super::objects::{ Bool8, Float32, Int32, Object, Void };

impl Debug for dyn Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&String::from(format!("{:?}", self)))
    }
}

#[derive(Debug)]
pub struct Chunk {
    pub code: Vec<u8>,
    pub constants: Vec<Rc<dyn Object + 'static>>,
}

impl Chunk {
    pub fn new(code: Vec<u8>, constants: Vec<Rc<dyn Object>>) -> Self {
        Self { code, constants }
    }
}

struct Frame {
    pub chunk: Rc<Chunk>,
    pub sp: usize,
    pub ip: usize,
}

impl Frame {
    fn new(chunk: Rc<Chunk>) -> Self {
        Self { chunk, sp: 0, ip: 0 }
    }

    pub fn set_ip(&mut self, ip: usize) {
        self.ip = ip;
    }

    pub fn set_sp(&mut self, sp: usize) {
        self.sp = sp;
    }
}

pub struct VirtualMachine {
    pub ip: usize,
    pub sp: usize,
    pub stack: Vec<Rc<dyn Object>>,
    pub bytecode: Option<Bytecode>,
    frame_stack: Vec<RefCell<Frame>>,
    return_address_stack: Vec<usize>,
}

impl VirtualMachine {
    pub fn new() -> Self {
        Self {
            ip: 0,
            sp: 0,
            stack: vec![Rc::new(Void::new()); 255],
            frame_stack: Vec::new(),
            return_address_stack: Vec::new(),
            bytecode: None,
        }
    }

    pub fn interpret(&mut self, bytecode: &Bytecode) {
        self.bytecode = Some(bytecode.clone());
        self.attach_main_fn();
        let timer = std::time::Instant::now();
        self.execution_loop();
        println!("Virtual machine took: {:?}", timer.elapsed());
    }

    fn execution_loop(&mut self) {
        loop {
            let byte = self.read_byte();

            match Instruction::try_from(byte).unwrap() {
                Instruction::Push => {
                    let constant_index = self.read_u16();

                    let constant = self.frame_stack
                        .last()
                        .unwrap()
                        .borrow()
                        .chunk.constants[constant_index as usize].clone();

                    self.push(constant);
                }

                Instruction::Pop => {
                    self.pop();
                }

                Instruction::Void => {
                    self.push(Rc::new(Void::new()));
                }

                Instruction::Add => {
                    let a = self.pop();
                    let b = self.pop();

                    match (a.get_kind(), b.get_kind()) {
                        (ObjectKind::Float, ObjectKind::Float) => {
                            let a = a.as_any().downcast_ref::<Float32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Float32>().unwrap().v;
                            self.push(Rc::new(Float32::new(a + b)));
                        }
                        (ObjectKind::Int, ObjectKind::Int) => {
                            let a = a.as_any().downcast_ref::<Int32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Int32>().unwrap().v;
                            self.push(Rc::new(Int32::new(a + b)));
                        }
                        (ObjectKind::Int, ObjectKind::Float) => {
                            let a = a.as_any().downcast_ref::<Int32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Float32>().unwrap().v;
                            self.push(Rc::new(Float32::new((a as f32) + b)));
                        }
                        (ObjectKind::Float, ObjectKind::Int) => {
                            let a = a.as_any().downcast_ref::<Float32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Int32>().unwrap().v;
                            self.push(Rc::new(Float32::new(a + (b as f32))));
                        }
                        _ => {}
                    }
                }

                Instruction::Sub => {
                    let a = self.pop();
                    let b = self.pop();

                    match (a.get_kind(), b.get_kind()) {
                        (ObjectKind::Float, ObjectKind::Float) => {
                            let a = a.as_any().downcast_ref::<Float32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Float32>().unwrap().v;
                            self.push(Rc::new(Float32::new(a - b)));
                        }
                        (ObjectKind::Int, ObjectKind::Int) => {
                            let a = a.as_any().downcast_ref::<Int32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Int32>().unwrap().v;
                            self.push(Rc::new(Int32::new(a - b)));
                        }
                        (ObjectKind::Int, ObjectKind::Float) => {
                            let a = a.as_any().downcast_ref::<Int32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Float32>().unwrap().v;
                            self.push(Rc::new(Float32::new((a as f32) - b)));
                        }
                        (ObjectKind::Float, ObjectKind::Int) => {
                            let a = a.as_any().downcast_ref::<Float32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Int32>().unwrap().v;
                            self.push(Rc::new(Float32::new(a - (b as f32))));
                        }
                        _ => {}
                    }
                }

                Instruction::Mul => {
                    let a = self.pop();
                    let b = self.pop();

                    match (a.get_kind(), b.get_kind()) {
                        (ObjectKind::Float, ObjectKind::Float) => {
                            let a = a.as_any().downcast_ref::<Float32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Float32>().unwrap().v;
                            self.push(Rc::new(Float32::new(a * b)));
                        }
                        (ObjectKind::Int, ObjectKind::Int) => {
                            let a = a.as_any().downcast_ref::<Int32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Int32>().unwrap().v;
                            self.push(Rc::new(Int32::new(a * b)));
                        }
                        (ObjectKind::Int, ObjectKind::Float) => {
                            let a = a.as_any().downcast_ref::<Int32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Float32>().unwrap().v;
                            self.push(Rc::new(Float32::new((a as f32) * b)));
                        }
                        (ObjectKind::Float, ObjectKind::Int) => {
                            let a = a.as_any().downcast_ref::<Float32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Int32>().unwrap().v;
                            self.push(Rc::new(Float32::new(a * (b as f32))));
                        }
                        _ => {}
                    }
                }

                Instruction::Div => {
                    let a = self.pop();
                    let b = self.pop();

                    match (a.get_kind(), b.get_kind()) {
                        (ObjectKind::Float, ObjectKind::Float) => {
                            let a = a.as_any().downcast_ref::<Float32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Float32>().unwrap().v;
                            self.push(Rc::new(Float32::new(a / b)));
                        }
                        (ObjectKind::Int, ObjectKind::Int) => {
                            let a = a.as_any().downcast_ref::<Int32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Int32>().unwrap().v;
                            self.push(Rc::new(Int32::new(a / b)));
                        }
                        (ObjectKind::Int, ObjectKind::Float) => {
                            let a = a.as_any().downcast_ref::<Int32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Float32>().unwrap().v;
                            self.push(Rc::new(Float32::new((a as f32) / b)));
                        }
                        (ObjectKind::Float, ObjectKind::Int) => {
                            let a = a.as_any().downcast_ref::<Float32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Int32>().unwrap().v;
                            self.push(Rc::new(Float32::new(a / (b as f32))));
                        }
                        _ => {}
                    }
                }

                Instruction::Greater => {
                    let a = self.pop();
                    let b = self.pop();

                    match (a.get_kind(), b.get_kind()) {
                        (ObjectKind::Float, ObjectKind::Float) => {
                            let a = a.as_any().downcast_ref::<Float32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Float32>().unwrap().v;
                            self.push(Rc::new(Bool8::new(a > b)));
                        }
                        (ObjectKind::Int, ObjectKind::Int) => {
                            let a = a.as_any().downcast_ref::<Int32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Int32>().unwrap().v;
                            self.push(Rc::new(Bool8::new(a > b)));
                        }
                        (ObjectKind::Int, ObjectKind::Float) => {
                            let a = a.as_any().downcast_ref::<Int32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Float32>().unwrap().v;
                            self.push(Rc::new(Bool8::new((a as f32) > b)));
                        }
                        (ObjectKind::Float, ObjectKind::Int) => {
                            let a = a.as_any().downcast_ref::<Float32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Int32>().unwrap().v;
                            self.push(Rc::new(Bool8::new(a > (b as f32))));
                        }
                        _ => {}
                    }
                }

                Instruction::GreaterEqual => {
                    let a = self.pop();
                    let b = self.pop();

                    match (a.get_kind(), b.get_kind()) {
                        (ObjectKind::Float, ObjectKind::Float) => {
                            let a = a.as_any().downcast_ref::<Float32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Float32>().unwrap().v;
                            self.push(Rc::new(Bool8::new(a >= b)));
                        }
                        (ObjectKind::Int, ObjectKind::Int) => {
                            let a = a.as_any().downcast_ref::<Int32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Int32>().unwrap().v;
                            self.push(Rc::new(Bool8::new(a >= b)));
                        }
                        (ObjectKind::Int, ObjectKind::Float) => {
                            let a = a.as_any().downcast_ref::<Int32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Float32>().unwrap().v;
                            self.push(Rc::new(Bool8::new((a as f32) >= b)));
                        }
                        (ObjectKind::Float, ObjectKind::Int) => {
                            let a = a.as_any().downcast_ref::<Float32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Int32>().unwrap().v;
                            self.push(Rc::new(Bool8::new(a >= (b as f32))));
                        }
                        _ => {}
                    }
                }

                Instruction::Less => {
                    let a = self.pop();
                    let b = self.pop();

                    match (a.get_kind(), b.get_kind()) {
                        (ObjectKind::Float, ObjectKind::Float) => {
                            let a = a.as_any().downcast_ref::<Float32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Float32>().unwrap().v;
                            self.push(Rc::new(Bool8::new(a < b)));
                        }
                        (ObjectKind::Int, ObjectKind::Int) => {
                            let a = a.as_any().downcast_ref::<Int32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Int32>().unwrap().v;
                            self.push(Rc::new(Bool8::new(a < b)));
                        }
                        (ObjectKind::Int, ObjectKind::Float) => {
                            let a = a.as_any().downcast_ref::<Int32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Float32>().unwrap().v;
                            self.push(Rc::new(Bool8::new((a as f32) < b)));
                        }
                        (ObjectKind::Float, ObjectKind::Int) => {
                            let a = a.as_any().downcast_ref::<Float32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Int32>().unwrap().v;
                            self.push(Rc::new(Bool8::new(a < (b as f32))));
                        }
                        _ => {}
                    }
                }

                Instruction::LessEqual => {
                    let a = self.pop();
                    let b = self.pop();

                    match (a.get_kind(), b.get_kind()) {
                        (ObjectKind::Float, ObjectKind::Float) => {
                            let a = a.as_any().downcast_ref::<Float32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Float32>().unwrap().v;
                            self.push(Rc::new(Bool8::new(a <= b)));
                        }
                        (ObjectKind::Int, ObjectKind::Int) => {
                            let a = a.as_any().downcast_ref::<Int32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Int32>().unwrap().v;
                            self.push(Rc::new(Bool8::new(a <= b)));
                        }
                        (ObjectKind::Int, ObjectKind::Float) => {
                            let a = a.as_any().downcast_ref::<Int32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Float32>().unwrap().v;
                            self.push(Rc::new(Bool8::new((a as f32) <= b)));
                        }
                        (ObjectKind::Float, ObjectKind::Int) => {
                            let a = a.as_any().downcast_ref::<Float32>().unwrap().v;
                            let b = b.as_any().downcast_ref::<Int32>().unwrap().v;
                            self.push(Rc::new(Bool8::new(a <= (b as f32))));
                        }
                        _ => {}
                    }
                }

                Instruction::True => {
                    self.push(Rc::new(Bool8::new(true)));
                }

                Instruction::False => {
                    self.push(Rc::new(Bool8::new(false)));
                }

                Instruction::Print => {
                    let value = self.pop().to_string();
                    println!("{}", value);
                }

                Instruction::SetLocal => {
                    let value = self.pop();
                    let index = self.read_byte();
                    self.stack[index as usize] = value;
                }

                Instruction::GetLocal => {
                    let index = self.read_byte();
                    let value = &self.stack[index as usize];
                    self.push(value.clone());
                }

                Instruction::IncrementLocal => {
                    let index = self.read_byte();
                    let value = &self.stack[index as usize];

                    self.stack[index as usize] = Rc::new(
                        Int32::new(value.as_any().downcast_ref::<Int32>().unwrap().v + 1)
                    );
                }

                Instruction::DecrementLocal => {
                    let index = self.read_byte();
                    let value = &self.stack[index as usize];

                    self.stack[index as usize] = Rc::new(
                        Int32::new(value.as_any().downcast_ref::<Int32>().unwrap().v - 1)
                    );
                }

                Instruction::Call => {
                    let index = self.read_u32();
                    let arity = self.read_byte();

                    self.attach_fn(index, arity);
                }

                Instruction::Ret => {
                    let ret_value = self.pop();

                    if let ObjectKind::Void = ret_value.get_kind() {
                        self.detach_fn();
                    } else {
                        self.detach_fn();
                        self.push(ret_value.clone());
                    }
                }

                Instruction::Halt => {
                    break;
                }

                Instruction::Loop => {
                    let offset = self.read_u32();
                    self.ip -= offset as usize;
                }

                Instruction::Jump => {
                    let offset = self.read_u32();
                    self.ip += offset as usize;
                }

                Instruction::JFalse => {
                    let offset = self.read_u32();
                    let value = self.pop();

                    if value.get_kind() == ObjectKind::Boolean {
                        let b = value.as_any().downcast_ref::<Bool8>().unwrap().v;
                        if !b {
                            self.ip += offset as usize;
                        }
                    }
                }

                Instruction::JTrue => {
                    let offset = self.read_u32();
                    let value = self.pop();

                    if value.get_kind() == ObjectKind::Boolean {
                        let b = value.as_any().downcast_ref::<Bool8>().unwrap().v;
                        if b {
                            self.ip += offset as usize;
                        }
                    }
                }

                Instruction::Not => {
                    let value = self.pop();

                    match value.get_kind() {
                        ObjectKind::Float => {
                            let f = value.as_any().downcast_ref::<Float32>().unwrap().v;
                            self.push(Rc::new(Float32::new(-f)));
                        }
                        ObjectKind::Int => {
                            let i = value.as_any().downcast_ref::<Int32>().unwrap().v;
                            self.push(Rc::new(Int32::new(-i)));
                        }
                        ObjectKind::Boolean => {
                            let b = value.as_any().downcast_ref::<Bool8>().unwrap().v;
                            self.push(Rc::new(Bool8::new(!b)));
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
    }

    fn pop(&mut self) -> Rc<dyn Object> {
        self.sp -= 1;
        let value = &self.stack[self.sp as usize];
        value.clone()
    }

    fn read_u16(&mut self) -> u16 {
        let byte1 = self.read_byte();
        let byte2 = self.read_byte();
        ((byte1 as u16) << 8) | (byte2 as u16)
    }

    fn read_u32(&mut self) -> u32 {
        let byte1 = self.read_byte();
        let byte2 = self.read_byte();
        let byte3 = self.read_byte();
        let byte4 = self.read_byte();

        let value =
            ((byte1 as u32) << 24) |
            ((byte2 as u32) << 16) |
            ((byte3 as u32) << 8) |
            (byte4 as u32);
        value
    }

    fn read_byte(&mut self) -> u8 {
        let byte = self.frame_stack.last().unwrap().borrow().chunk.code[self.ip];
        self.ip += 1;

        byte
    }

    fn push(&mut self, value: Rc<dyn Object>) {
        self.stack[self.sp as usize] = value;
        self.sp += 1;
    }

    fn print_stack(&self) {
        print!("Stack [");

        for i in 0..self.sp {
            print!("{}, ", self.stack[i].to_string());
        }

        println!("]");
    }

    fn attach_main_fn(&mut self) {
        let main = Frame::new(self.bytecode.clone().unwrap().main.unwrap().chunk);
        self.frame_stack.push(RefCell::new(main));
        self.ip = 0;
    }

    fn attach_fn(&mut self, function_id: u32, arity: u8) {
        let code = self.bytecode.clone();
        let chunk = code.unwrap().get_function(function_id);
        let frame = Frame::new(chunk);

        self.frame_stack.last().unwrap().borrow_mut().set_ip(self.ip);
        self.frame_stack
            .last()
            .unwrap()
            .borrow_mut()
            .set_sp(self.sp - (arity as usize));
        self.frame_stack.push(RefCell::new(frame));
        self.ip = 0;
    }

    fn detach_fn(&mut self) {
        self.frame_stack.pop();
        self.ip = self.frame_stack.last().unwrap().borrow().ip;
        self.sp = self.frame_stack.last().unwrap().borrow().sp;
    }
}
