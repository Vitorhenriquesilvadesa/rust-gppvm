use std::{cell::RefCell, env, io::stdin, rc::Rc};

use rand::Rng;

use crate::register_native_funcs;

use super::{
    ffi::{NativeBridge, NativeLibrary},
    objects::{List, Value},
};

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
        match &args[0] {
            Value::String(s) => Value::Int(s.trim().parse().expect("str to int parse error.")),
            Value::Int(i) => Value::Int(*i),
            _ => {
                unreachable!()
            }
        }
    }

    fn float(args: Vec<Value>) -> Value {
        if let Value::String(s) = &args[0] {
            Value::Float(s.trim().parse().expect("str to float parse error."))
        } else {
            unreachable!()
        }
    }

    fn bool(args: Vec<Value>) -> Value {
        if let Value::Bool(b) = &args[0] {
            Value::Bool(*b)
        } else {
            unreachable!()
        }
    }

    fn random_range(args: Vec<Value>) -> Value {
        match (&args[0], &args[1]) {
            (Value::Int(a), Value::Int(b)) => Value::Int(rand::thread_rng().gen_range(*a..*b)),
            _ => unreachable!(),
        }
    }

    fn input(args: Vec<Value>) -> Value {
        let mut line = String::new();
        stdin().read_line(&mut line).unwrap();
        Value::String(Rc::new(line.trim().to_string()))
    }

    fn exit(args: Vec<Value>) -> Value {
        if let Value::Int(i) = &args[0] {
            std::process::exit(*i);
        }

        unreachable!()
    }

    fn len(args: Vec<Value>) -> Value {
        if let Value::Object(obj_ptr) = &args[0] {
            let len = obj_ptr
                .borrow()
                .as_any()
                .downcast_ref::<List>()
                .unwrap()
                .elements
                .len();
            return Value::Int(len as i32);
        }

        unreachable!();
    }

    fn args(args: Vec<Value>) -> Value {
        let args: Vec<String> = env::args().into_iter().collect();
        let mut elements: Vec<Value> = Vec::new();

        for i in 5..args.len() {
            elements.push(Value::String(Rc::new(args[i].clone())));
        }

        let list = List::new(elements);

        Value::Object(Rc::new(RefCell::new(list)))
    }

    fn append(args: Vec<Value>) -> Value {
        if let Value::Object(obj_ptr) = &args[0] {
            let value = &args[1];
            obj_ptr
                .borrow_mut()
                .as_any_mut()
                .downcast_mut::<List>()
                .unwrap()
                .elements
                .push(value.clone());

            return Value::Void;
        }

        unreachable!()
    }
}

impl NativeLibrary for StdLibrary {
    fn register_functions(&self, bridge: &mut dyn NativeBridge) {
        register_native_funcs!(
            bridge,
            [
                print,
                input,
                int,
                float,
                random_range,
                len,
                append,
                args,
                exit,
            ]
        );
    }
}
