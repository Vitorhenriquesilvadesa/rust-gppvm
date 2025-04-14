use std::{ io::stdin, rc::Rc };

use rand::Rng;

use super::{ ffi::{ NativeBridge, NativeLibrary }, objects::{ List, Value } };

pub struct StdLibrary;

impl StdLibrary {
    pub fn get_lib() -> Self {
        Self {}
    }

    fn print(args: Vec<Value>) -> Value {
        println!("{}", args[0]);
        Value::Void
    }

    fn int(args: Vec<Value>) -> Value {
        if let Value::String(s) = &args[0] {
            Value::Int(s.trim().parse().expect("str to int parse error."))
        } else {
            unreachable!()
        }
    }

    fn float(args: Vec<Value>) -> Value {
        if let Value::String(s) = &args[0] {
            Value::Float(s.trim().parse().expect("str to float parse error."))
        } else {
            unreachable!()
        }
    }

    fn random_range(args: Vec<Value>) -> Value {
        match (&args[0], &args[1]) {
            (Value::Int(a), Value::Int(b)) => { Value::Int(rand::thread_rng().gen_range(*a..*b)) }
            _ => unreachable!(),
        }
    }

    fn input(args: Vec<Value>) -> Value {
        let mut line = String::new();
        stdin().read_line(&mut line).unwrap();
        Value::String(Rc::new(line.trim().to_string()))
    }

    fn len(args: Vec<Value>) -> Value {
        if let Value::Object(obj_ptr) = &args[0] {
            let len = obj_ptr.borrow().as_any().downcast_ref::<List>().unwrap().elements.len();
            return Value::Int(len as i32);
        }

        unreachable!();
    }

    fn append(args: Vec<Value>) -> Value {
        if let Value::Object(obj_ptr) = &args[0] {
            let value = &args[1];
            obj_ptr
                .borrow_mut()
                .as_any_mut()
                .downcast_mut::<List>()
                .unwrap()
                .elements.push(value.clone());

            return Value::Void;
        }

        unreachable!()
    }
}

impl NativeLibrary for StdLibrary {
    fn register_functions(&self, bridge: &mut dyn NativeBridge) {
        bridge.bind("print", Self::print);
        bridge.bind("input", Self::input);
        bridge.bind("int", Self::int);
        bridge.bind("float", Self::float);
        bridge.bind("random_range", Self::random_range);
        bridge.bind("len", Self::len);
        bridge.bind("append", Self::append);
    }
}
