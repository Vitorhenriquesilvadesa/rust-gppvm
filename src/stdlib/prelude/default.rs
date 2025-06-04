use std::{
    cell::RefCell,
    env,
    rc::Rc,
    thread::sleep,
    time::{Duration, SystemTime, UNIX_EPOCH},
};

use crate::{
    register_native_funcs,
    runtime::{
        ffi::NativeLibrary,
        objects::{List, Value},
    },
};

pub struct GPPDefaultFunctionsNativeLibrary;

impl GPPDefaultFunctionsNativeLibrary {
    fn int(args: Vec<Value>) -> Value {
        match &args[0] {
            Value::String(s) => Value::Int(s.trim().parse().expect(&format!(
                "str to int parse error. Input was '{}'",
                s.to_string()
            ))),
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

    fn exception(args: Vec<Value>) -> Value {
        if let Value::String(s) = &args[0] {
            eprintln!("{}", s);
            std::process::exit(-1);
        }

        unreachable!();
    }

    fn exit(args: Vec<Value>) -> Value {
        if let Value::Int(i) = &args[0] {
            std::process::exit(*i);
        }

        unreachable!()
    }

    fn args(_args: Vec<Value>) -> Value {
        let args: Vec<String> = env::args().into_iter().collect();
        let mut elements: Vec<Value> = Vec::new();

        for i in 5..args.len() {
            elements.push(Value::String(Rc::new(args[i].clone())));
        }

        let list = List::new(elements);

        Value::Object(Rc::new(RefCell::new(list)))
    }

    fn sleep(args: Vec<Value>) -> Value {
        if let Value::Int(i) = args[0] {
            sleep(Duration::from_millis(i as u64));
        }

        Value::Void
    }

    fn now_ms(_args: Vec<Value>) -> Value {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("System time before UNIX EPOCH");

        Value::Int(now.as_millis() as i32)
    }
}

impl NativeLibrary for GPPDefaultFunctionsNativeLibrary {
    fn register_functions(&self, bridge: &mut dyn crate::runtime::ffi::NativeBridge) {
        register_native_funcs!(
            bridge,
            [exception, int, float, bool, args, exit, now_ms, sleep,]
        );
    }
}
