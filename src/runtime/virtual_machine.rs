use std::{ cell::RefCell, rc::Rc };
use core::fmt::Debug;
use crate::compiler::{ bytecode_gen::Bytecode, instructions::Instruction };
use super::objects::{ Instance, List, Value };

#[derive(Debug)]
pub struct Chunk {
    pub code: Vec<u8>,
    pub constants: Vec<Value>,
}

impl Chunk {
    pub fn new(code: Vec<u8>, constants: Vec<Value>) -> Self {
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
    pub stack: Vec<Value>,
    pub bytecode: Option<Bytecode>,
    frame_stack: Vec<RefCell<Frame>>,
}

impl VirtualMachine {
    pub fn new() -> Self {
        Self {
            ip: 0,
            sp: 0,
            stack: vec![Value::Void; 255],
            frame_stack: Vec::new(),
            bytecode: None,
        }
    }

    #[inline(always)]
    pub fn handle_add(&mut self) {
        let a = self.pop();
        let b = self.pop();

        match (a, b) {
            (Value::Float(a), Value::Float(b)) => {
                self.push(Value::Float(a + b));
            }
            (Value::Int(a), Value::Int(b)) => {
                self.push(Value::Int(a + b));
            }
            (Value::Int(a), Value::Float(b)) => {
                self.push(Value::Float((a as f32) + b));
            }
            (Value::Float(a), Value::Int(b)) => {
                self.push(Value::Float(a + (b as f32)));
            }
            _ => {}
        }
    }

    #[inline(always)]
    pub fn handle_sub(&mut self) {
        let a = self.pop();
        let b = self.pop();

        match (a, b) {
            (Value::Float(a), Value::Float(b)) => {
                self.push(Value::Float(a - b));
            }
            (Value::Int(a), Value::Int(b)) => {
                self.push(Value::Int(a - b));
            }
            (Value::Int(a), Value::Float(b)) => {
                self.push(Value::Float((a as f32) - b));
            }
            (Value::Float(a), Value::Int(b)) => {
                self.push(Value::Float(a - (b as f32)));
            }
            _ => {}
        }
    }

    #[inline(always)]
    pub fn handle_div(&mut self) {
        let a = self.pop();
        let b = self.pop();

        match (a, b) {
            (Value::Float(a), Value::Float(b)) => {
                self.push(Value::Float(a / b));
            }
            (Value::Int(a), Value::Int(b)) => {
                self.push(Value::Int(a / b));
            }
            (Value::Int(a), Value::Float(b)) => {
                self.push(Value::Float((a as f32) / b));
            }
            (Value::Float(a), Value::Int(b)) => {
                self.push(Value::Float(a / (b as f32)));
            }
            _ => {}
        }
    }

    #[inline(always)]
    pub fn handle_mul(&mut self) {
        let a = self.pop();
        let b = self.pop();

        match (a, b) {
            (Value::Float(a), Value::Float(b)) => {
                self.push(Value::Float(a * b));
            }
            (Value::Int(a), Value::Int(b)) => {
                self.push(Value::Int(a * b));
            }
            (Value::Int(a), Value::Float(b)) => {
                self.push(Value::Float((a as f32) * b));
            }
            (Value::Float(a), Value::Int(b)) => {
                self.push(Value::Float(a * (b as f32)));
            }
            _ => {}
        }
    }

    #[inline(always)]
    pub fn handle_push(&mut self) {
        let constant_index = self.read_u16();

        let constant = self.frame_stack
            .last()
            .unwrap()
            .borrow()
            .chunk.constants[constant_index as usize].clone();

        self.push(constant);
    }

    #[inline(always)]
    pub fn handle_pop(&mut self) {
        self.pop();
    }

    #[inline(always)]
    pub fn handle_void(&mut self) {
        self.push(Value::Void);
    }

    #[inline(always)]
    pub fn handle_greater(&mut self) {
        let a = self.pop();
        let b = self.pop();

        match (a, b) {
            (Value::Float(a), Value::Float(b)) => {
                self.push(Value::Bool(a > b));
            }
            (Value::Int(a), Value::Int(b)) => {
                self.push(Value::Bool(a > b));
            }
            (Value::Int(a), Value::Float(b)) => {
                self.push(Value::Bool((a as f32) > b));
            }
            (Value::Float(a), Value::Int(b)) => {
                self.push(Value::Bool(a > (b as f32)));
            }
            _ => {}
        }
    }

    #[inline(always)]
    pub fn handle_less(&mut self) {
        let a = self.pop();
        let b = self.pop();

        match (a, b) {
            (Value::Float(a), Value::Float(b)) => {
                self.push(Value::Bool(a < b));
            }
            (Value::Int(a), Value::Int(b)) => {
                self.push(Value::Bool(a < b));
            }
            (Value::Int(a), Value::Float(b)) => {
                self.push(Value::Bool((a as f32) < b));
            }
            (Value::Float(a), Value::Int(b)) => {
                self.push(Value::Bool(a < (b as f32)));
            }
            _ => {}
        }
    }

    #[inline(always)]
    pub fn handle_greater_equal(&mut self) {
        let a = self.pop();
        let b = self.pop();

        match (a, b) {
            (Value::Float(a), Value::Float(b)) => {
                self.push(Value::Bool(a >= b));
            }
            (Value::Int(a), Value::Int(b)) => {
                self.push(Value::Bool(a >= b));
            }
            (Value::Int(a), Value::Float(b)) => {
                self.push(Value::Bool((a as f32) >= b));
            }
            (Value::Float(a), Value::Int(b)) => {
                self.push(Value::Bool(a >= (b as f32)));
            }
            _ => {}
        }
    }

    #[inline(always)]
    pub fn handle_less_equal(&mut self) {
        let a = self.pop();
        let b = self.pop();

        match (a, b) {
            (Value::Float(a), Value::Float(b)) => {
                self.push(Value::Bool(a <= b));
            }
            (Value::Int(a), Value::Int(b)) => {
                self.push(Value::Bool(a <= b));
            }
            (Value::Int(a), Value::Float(b)) => {
                self.push(Value::Bool((a as f32) <= b));
            }
            (Value::Float(a), Value::Int(b)) => {
                self.push(Value::Bool(a <= (b as f32)));
            }
            _ => {}
        }
    }

    #[inline(always)]
    pub fn handle_true(&mut self) {
        self.push(Value::Bool(true));
    }

    #[inline(always)]
    pub fn handle_false(&mut self) {
        self.push(Value::Bool(false));
    }

    #[inline(always)]
    pub fn handle_get_field(&mut self) {
        let object = self.pop();
        let index = self.read_byte();

        if let Value::Object(obj_ptr) = object {
            self.push(
                obj_ptr
                    .borrow()
                    .as_any()
                    .downcast_ref::<Instance>()
                    .unwrap()
                    .fields[index as usize].clone()
            );
        }
    }

    pub fn handle_set_field(&mut self) {
        let value = self.pop();
        let object = self.pop();
        let index = self.read_byte();

        if let Value::Object(obj_ptr) = &object {
            obj_ptr.borrow_mut().as_any_mut().downcast_mut::<Instance>().unwrap().fields[
                index as usize
            ] = value;
        }
    }

    #[inline(always)]
    pub fn handle_new(&mut self) {
        let arity = self.read_byte();

        let mut fields: Vec<Value> = Vec::new();

        self.sp -= arity as usize;

        for i in 0..arity as usize {
            fields.push(self.stack[self.sp + i].clone());
        }

        self.push(Value::Object(Rc::new(RefCell::new(Instance::new(fields)))));
    }

    #[inline(always)]
    pub fn handle_print(&mut self) {
        let value = self.pop();

        match value {
            Value::Bool(b) => println!("{}", b),
            Value::Int(i) => println!("{}", i),
            Value::Float(f) => println!("{}", f),
            Value::String(s) => println!("{}", s),
            Value::Object(obj) => {
                println!("{}", obj.borrow().to_string());
            }
            _ => todo!(),
        }
    }

    #[inline(always)]
    pub fn handle_set_local(&mut self) {
        let value = self.pop();
        let index = self.read_byte();
        self.stack[index as usize] = value;
    }

    #[inline(always)]
    pub fn handle_get_local(&mut self) {
        let index = self.read_byte();
        let value = &self.stack[index as usize];
        self.push(value.clone());
    }

    #[inline(always)]
    pub fn handle_get_local0(&mut self) {
        let value = &self.stack[0];
        self.push(value.clone());
    }

    #[inline(always)]
    pub fn handle_get_local1(&mut self) {
        let value = &self.stack[1];
        self.push(value.clone());
    }

    #[inline(always)]
    pub fn handle_get_local2(&mut self) {
        let value = &self.stack[2];
        self.push(value.clone());
    }

    #[inline(always)]
    pub fn handle_get_local3(&mut self) {
        let value = &self.stack[3];
        self.push(value.clone());
    }

    #[inline(always)]
    pub fn handle_get_local4(&mut self) {
        let value = &self.stack[4];
        self.push(value.clone());
    }

    #[inline(always)]
    pub fn handle_increment_local(&mut self) {
        let index = self.read_byte();
        let value = &self.stack[index as usize];

        if let Value::Int(i) = value {
            self.stack[index as usize] = Value::Int(i + 1);
        }
    }

    #[inline(always)]
    pub fn handle_decrement_local(&mut self) {
        let index = self.read_byte();
        let value = &self.stack[index as usize];

        if let Value::Int(i) = value {
            self.stack[index as usize] = Value::Int(i - 1);
        }
    }

    #[inline(always)]
    pub fn handle_call(&mut self) {
        let index = self.read_u32();
        let arity = self.read_byte();

        self.attach_fn(index, arity);
    }

    #[inline(always)]
    pub fn handle_return(&mut self) {
        let ret_value = self.pop();

        if let Value::Void = ret_value {
            self.detach_fn();
        } else {
            self.detach_fn();
            self.push(ret_value);
        }
    }

    #[inline(always)]
    pub fn handle_loop(&mut self) {
        let offset = self.read_u32();
        self.ip -= offset as usize;
    }

    #[inline(always)]
    pub fn handle_jump(&mut self) {
        let offset = self.read_u32();
        self.ip += offset as usize;
    }

    #[inline(always)]
    pub fn handle_jfalse(&mut self) {
        let offset = self.read_u32();
        let value = self.pop();

        if let Value::Bool(b) = value {
            if !b {
                self.ip += offset as usize;
            }
        }
    }

    #[inline(always)]
    pub fn handle_jtrue(&mut self) {
        let offset = self.read_u32();
        let value = self.pop();

        if let Value::Bool(b) = value {
            if b {
                self.ip += offset as usize;
            }
        }
    }

    #[inline(always)]
    pub fn handle_not(&mut self) {
        let value = self.pop();

        match value {
            Value::Float(f) => {
                self.push(Value::Float(-f));
            }
            Value::Int(i) => {
                self.push(Value::Int(-i));
            }
            Value::Bool(b) => {
                self.push(Value::Bool(!b));
            }
            _ => {}
        }
    }

    #[inline(always)]
    pub fn handle_array(&mut self) {
        let arity = self.read_byte();

        let mut elements: Vec<Value> = Vec::new();

        self.sp -= arity as usize;

        for i in 0..arity as usize {
            elements.push(self.stack[self.sp + i].clone());
        }

        self.push(Value::Object(Rc::new(RefCell::new(List::new(elements)))));
    }

    pub fn interpret(&mut self, bytecode: &Bytecode) {
        self.bytecode = Some(bytecode.clone());
        self.attach_main_fn();
        let timer = std::time::Instant::now();
        self.execution_loop();
        println!("Virtual machine took: {:?}", timer.elapsed());
    }

    #[inline(always)]
    fn execution_loop(&mut self) {
        loop {
            let byte = self.read_byte();
            let instruction = unsafe { std::mem::transmute::<u8, Instruction>(byte) };

            match instruction {
                Instruction::Add => self.handle_add(),
                Instruction::Sub => self.handle_sub(),
                Instruction::Mul => self.handle_mul(),
                Instruction::Div => self.handle_div(),
                Instruction::Greater => self.handle_greater(),
                Instruction::Less => self.handle_less(),
                Instruction::GreaterEqual => self.handle_greater_equal(),
                Instruction::LessEqual => self.handle_less_equal(),
                Instruction::Push => self.handle_push(),
                Instruction::Pop => self.handle_pop(),
                Instruction::Jump => self.handle_jump(),
                Instruction::JTrue => self.handle_jtrue(),
                Instruction::JFalse => self.handle_jfalse(),
                Instruction::Ret => self.handle_return(),
                Instruction::Print => self.handle_print(),
                Instruction::Call => self.handle_call(),
                Instruction::True => self.handle_true(),
                Instruction::False => self.handle_false(),
                Instruction::GetLocal => self.handle_get_local(),
                Instruction::GetLocal0 => self.handle_get_local0(),
                Instruction::GetLocal1 => self.handle_get_local1(),
                Instruction::GetLocal2 => self.handle_get_local2(),
                Instruction::GetLocal3 => self.handle_get_local3(),
                Instruction::GetLocal4 => self.handle_get_local4(),
                Instruction::SetLocal => self.handle_set_local(),
                Instruction::Void => self.handle_void(),
                Instruction::DecrementLocal => self.handle_decrement_local(),
                Instruction::IncrementLocal => self.handle_increment_local(),
                Instruction::Loop => self.handle_loop(),
                Instruction::New => self.handle_new(),
                Instruction::GetField => self.handle_get_field(),
                Instruction::SetField => self.handle_set_field(),
                Instruction::Array => self.handle_array(),
                Instruction::Halt => {
                    break;
                }
                _ => panic!("Unimplemented instruction: {:?}", instruction),
            }
        }
    }

    fn pop(&mut self) -> Value {
        self.sp -= 1;
        std::mem::replace(&mut self.stack[self.sp as usize], Value::Void)
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

    fn push(&mut self, value: Value) {
        self.stack[self.sp as usize] = value;
        self.sp += 1;
    }

    #[allow(dead_code)]
    fn print_stack(&self) {
        print!("Stack [");

        for i in 0..self.sp {
            if let Value::Object(obj_ptr) = &self.stack[i] {
                print!("{}, ", obj_ptr.borrow().to_string());
            } else {
                print!("{:?}, ", self.stack[i]);
            }
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
