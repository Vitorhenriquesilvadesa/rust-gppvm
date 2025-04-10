use std::{ cell::RefCell, collections::HashMap, rc::Rc };
use core::fmt::Debug;

use crate::{
    compiler::{ bytecode_gen::Bytecode, instructions::Instruction },
    runtime::objects::ObjectKind,
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
    dispatch_table: HashMap<Instruction, Box<fn(&mut VirtualMachine)>>,
}

impl VirtualMachine {
    pub fn new() -> Self {
        let mut table: HashMap<Instruction, Box<fn(&mut VirtualMachine)>> = HashMap::new();

        table.insert(Instruction::Add, Box::new(VirtualMachine::handle_add));
        table.insert(Instruction::Sub, Box::new(VirtualMachine::handle_sub));
        table.insert(Instruction::Mul, Box::new(VirtualMachine::handle_mul));
        table.insert(Instruction::Div, Box::new(VirtualMachine::handle_div));
        table.insert(Instruction::JFalse, Box::new(VirtualMachine::handle_jfalse));
        table.insert(Instruction::JTrue, Box::new(VirtualMachine::handle_jtrue));
        table.insert(Instruction::Jump, Box::new(VirtualMachine::handle_jump));
        table.insert(Instruction::Loop, Box::new(VirtualMachine::handle_loop));
        table.insert(Instruction::Push, Box::new(VirtualMachine::handle_push));
        table.insert(Instruction::Pop, Box::new(VirtualMachine::handle_pop));
        table.insert(Instruction::Void, Box::new(VirtualMachine::handle_void));
        table.insert(Instruction::Greater, Box::new(VirtualMachine::handle_greater));
        table.insert(Instruction::GreaterEqual, Box::new(VirtualMachine::handle_greater_equal));
        table.insert(Instruction::Less, Box::new(VirtualMachine::handle_less));
        table.insert(Instruction::LessEqual, Box::new(VirtualMachine::handle_less_equal));
        table.insert(Instruction::True, Box::new(VirtualMachine::handle_true));
        table.insert(Instruction::False, Box::new(VirtualMachine::handle_false));
        table.insert(Instruction::Print, Box::new(VirtualMachine::handle_print));
        table.insert(Instruction::SetLocal, Box::new(VirtualMachine::handle_set_local));
        table.insert(Instruction::GetLocal, Box::new(VirtualMachine::handle_get_local));
        table.insert(Instruction::IncrementLocal, Box::new(VirtualMachine::handle_increment_local));
        table.insert(Instruction::DecrementLocal, Box::new(VirtualMachine::handle_decrement_local));
        table.insert(Instruction::Call, Box::new(VirtualMachine::handle_call));
        table.insert(Instruction::Ret, Box::new(VirtualMachine::handle_return));

        Self {
            ip: 0,
            sp: 0,
            stack: vec![Rc::new(Void::new()); 255],
            frame_stack: Vec::new(),
            dispatch_table: table,
            bytecode: None,
        }
    }

    #[inline]
    pub fn handle_add(&mut self) {
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

    #[inline]
    pub fn handle_sub(&mut self) {
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

    #[inline]
    pub fn handle_div(&mut self) {
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

    #[inline]
    pub fn handle_mul(&mut self) {
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

    #[inline]
    pub fn handle_push(&mut self) {
        let constant_index = self.read_u16();

        let constant = self.frame_stack
            .last()
            .unwrap()
            .borrow()
            .chunk.constants[constant_index as usize].clone();

        self.push(constant);
    }

    #[inline]
    pub fn handle_pop(&mut self) {
        self.pop();
    }

    #[inline]
    pub fn handle_void(&mut self) {
        self.push(Rc::new(Void::new()));
    }

    #[inline]
    pub fn handle_greater(&mut self) {
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

    #[inline]
    pub fn handle_less(&mut self) {
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

    #[inline]
    pub fn handle_greater_equal(&mut self) {
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

    #[inline]
    pub fn handle_less_equal(&mut self) {
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

    #[inline]
    pub fn handle_true(&mut self) {
        self.push(Rc::new(Bool8::new(true)));
    }

    #[inline]
    pub fn handle_false(&mut self) {
        self.push(Rc::new(Bool8::new(false)));
    }

    #[inline]
    pub fn handle_print(&mut self) {
        let value = self.pop().to_string();
        println!("{}", value);
    }

    #[inline]
    pub fn handle_set_local(&mut self) {
        let value = self.pop();
        let index = self.read_byte();
        self.stack[index as usize] = value;
    }

    #[inline]
    pub fn handle_get_local(&mut self) {
        let index = self.read_byte();
        let value = &self.stack[index as usize];
        self.push(value.clone());
    }

    #[inline]
    pub fn handle_increment_local(&mut self) {
        let index = self.read_byte();
        let value = &self.stack[index as usize];

        self.stack[index as usize] = Rc::new(
            Int32::new(value.as_any().downcast_ref::<Int32>().unwrap().v + 1)
        );
    }

    #[inline]
    pub fn handle_decrement_local(&mut self) {
        let index = self.read_byte();
        let value = &self.stack[index as usize];

        self.stack[index as usize] = Rc::new(
            Int32::new(value.as_any().downcast_ref::<Int32>().unwrap().v - 1)
        );
    }

    #[inline]
    pub fn handle_call(&mut self) {
        let index = self.read_u32();
        let arity = self.read_byte();

        self.attach_fn(index, arity);
    }

    #[inline]
    pub fn handle_return(&mut self) {
        let ret_value = self.pop();

        if let ObjectKind::Void = ret_value.get_kind() {
            self.detach_fn();
        } else {
            self.detach_fn();
            self.push(ret_value.clone());
        }
    }

    #[inline]
    pub fn handle_loop(&mut self) {
        let offset = self.read_u32();
        self.ip -= offset as usize;
    }

    #[inline]
    pub fn handle_jump(&mut self) {
        let offset = self.read_u32();
        self.ip += offset as usize;
    }

    #[inline]
    pub fn handle_jfalse(&mut self) {
        let offset = self.read_u32();
        let value = self.pop();

        if value.get_kind() == ObjectKind::Boolean {
            let b = value.as_any().downcast_ref::<Bool8>().unwrap().v;
            if !b {
                self.ip += offset as usize;
            }
        }
    }

    #[inline]
    pub fn handle_jtrue(&mut self) {
        let offset = self.read_u32();
        let value = self.pop();

        if value.get_kind() == ObjectKind::Boolean {
            let b = value.as_any().downcast_ref::<Bool8>().unwrap().v;
            if b {
                self.ip += offset as usize;
            }
        }
    }

    #[inline]
    pub fn handle_not(&mut self) {
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

    pub fn interpret(&mut self, bytecode: &Bytecode) {
        self.bytecode = Some(bytecode.clone());
        self.attach_main_fn();
        let timer = std::time::Instant::now();
        self.execution_loop();
        println!("Virtual machine took: {:?}", timer.elapsed());
    }

    fn execution_loop(&mut self) {
        loop {
            let instruction = Instruction::try_from(self.read_byte()).unwrap();

            match instruction {
                Instruction::Halt => {
                    break;
                }

                _ => {
                    self.dispatch_table[&instruction].as_ref()(self);
                }
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

    #[allow(dead_code)]
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
