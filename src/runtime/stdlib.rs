#![allow(dead_code)]
#![allow(deprecated)]
#![allow(unused_variables)]
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

    fn int_to_float(args: Vec<Value>) -> Value {
        if let Value::Int(i) = &args[0] {
            return Value::Float(*i as f32);
        }

        unreachable!("Found value '{}'.", &args[0]);
    }

    fn float_to_int(args: Vec<Value>) -> Value {
        if let Value::Float(f) = &args[0] {
            return Value::Int(*f as i32);
        }

        unreachable!("Found value '{}'.", &args[0]);
    }

    fn str_len(args: Vec<Value>) -> Value {
        if let Value::String(characters) = &args[0] {
            return Value::Int(characters.len() as i32);
        }

        unreachable!();
    }

    fn str_eq(args: Vec<Value>) -> Value {
        match (&args[0], &args[1]) {
            (Value::String(a), Value::String(b)) => Value::Bool(a == b),
            _ => unreachable!(
                "str_eq expects two strings, got: {:?} and {:?}",
                args[0], args[1]
            ),
        }
    }

    fn str_starts_with(args: Vec<Value>) -> Value {
        match (&args[0], &args[1]) {
            (Value::String(a), Value::String(b)) => Value::Bool(a.starts_with(&**b)),
            _ => unreachable!("str_starts_with expects two strings"),
        }
    }

    fn str_ends_with(args: Vec<Value>) -> Value {
        match (&args[0], &args[1]) {
            (Value::String(a), Value::String(b)) => Value::Bool(a.ends_with(&**b)),
            _ => unreachable!("str_ends_with expects two strings"),
        }
    }

    fn str_contains(args: Vec<Value>) -> Value {
        match (&args[0], &args[1]) {
            (Value::String(a), Value::String(b)) => Value::Bool(a.contains(&**b)),
            _ => unreachable!("str_contains expects two strings"),
        }
    }

    fn str_concat(args: Vec<Value>) -> Value {
        match (&args[0], &args[1]) {
            (Value::String(a), Value::String(b)) => {
                let mut result = String::with_capacity(a.len() + b.len());
                result.push_str(a);
                result.push_str(b);
                Value::String(Rc::new(result))
            }
            _ => unreachable!("str_concat espera dois argumentos do tipo str."),
        }
    }

    fn str_find(args: Vec<Value>) -> Value {
        if let (Value::String(haystack), Value::String(needle)) = (&args[0], &args[1]) {
            let haystack_str = haystack.as_str();
            let needle_str = needle.as_str();

            match haystack_str.find(needle_str) {
                Some(index) => Value::Int(index as i32),
                None => Value::Int(-1),
            }
        } else {
            unreachable!(
                "str_find expects two string arguments, found: '{:?}' and '{:?}'",
                args[0], args[1]
            );
        }
    }

    fn str_to_upper(args: Vec<Value>) -> Value {
        if let Value::String(a) = &args[0] {
            Value::String(Rc::new(a.to_uppercase()))
        } else {
            unreachable!("str_to_upper expects a string");
        }
    }

    fn str_to_lower(args: Vec<Value>) -> Value {
        if let Value::String(a) = &args[0] {
            Value::String(Rc::new(a.to_lowercase()))
        } else {
            unreachable!("str_to_lower expects a string");
        }
    }

    fn str_replace(args: Vec<Value>) -> Value {
        match (&args[0], &args[1], &args[2]) {
            (Value::String(a), Value::String(from), Value::String(to)) => {
                Value::String(Rc::new(a.replace(&**from, &**to)))
            }
            _ => unreachable!("str_replace expects three strings"),
        }
    }

    fn str_split(args: Vec<Value>) -> Value {
        match (&args[0], &args[1]) {
            (Value::String(a), Value::String(delim)) => {
                let parts = a.split(&**delim);
                let elements: Vec<Value> = parts
                    .map(|s| Value::String(Rc::new(s.to_string())))
                    .collect();
                Value::Object(Rc::new(RefCell::new(List::new(elements))))
            }
            _ => unreachable!("str_split expects two strings"),
        }
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

    fn int_abs(args: Vec<Value>) -> Value {
        if let Value::Int(x) = args[0] {
            Value::Int(x.abs())
        } else {
            unreachable!()
        }
    }

    fn int_is_even(args: Vec<Value>) -> Value {
        if let Value::Int(x) = args[0] {
            Value::Bool(x % 2 == 0)
        } else {
            unreachable!()
        }
    }

    fn int_is_odd(args: Vec<Value>) -> Value {
        if let Value::Int(x) = args[0] {
            Value::Bool(x % 2 != 0)
        } else {
            unreachable!()
        }
    }

    fn int_sign(args: Vec<Value>) -> Value {
        if let Value::Int(x) = args[0] {
            Value::Int(x.signum())
        } else {
            unreachable!()
        }
    }

    fn int_max(args: Vec<Value>) -> Value {
        if let (Value::Int(a), Value::Int(b)) = (&args[0], &args[1]) {
            Value::Int(std::cmp::max(*a, *b))
        } else {
            unreachable!()
        }
    }

    fn int_min(args: Vec<Value>) -> Value {
        if let (Value::Int(a), Value::Int(b)) = (&args[0], &args[1]) {
            Value::Int(std::cmp::min(*a, *b))
        } else {
            unreachable!()
        }
    }

    fn int_clamp(args: Vec<Value>) -> Value {
        if let (Value::Int(x), Value::Int(min), Value::Int(max)) = (&args[0], &args[1], &args[2]) {
            Value::Int(*x.clamp(min, max))
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
                str_len,
                int_to_float,
                float_to_int,
                str_eq,
                str_starts_with,
                str_ends_with,
                str_contains,
                str_to_upper,
                str_to_lower,
                str_replace,
                str_concat,
                str_split,
                str_find,
                int_abs,
                int_is_even,
                int_is_odd,
                int_sign,
                int_max,
                int_min,
                int_clamp,
                exception
            ]
        );
    }
}
