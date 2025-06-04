use std::{cell::RefCell, rc::Rc};

use crate::{
    register_native_funcs,
    runtime::{
        ffi::NativeLibrary,
        objects::{List, Value},
    },
};

pub struct GPPStringNativeLibrary;

impl GPPStringNativeLibrary {
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

    pub fn str_slice(args: Vec<Value>) -> Value {
        if args.len() != 3 {
            return Value::Void;
        }

        if let (Value::String(s), Value::Int(start), Value::Int(end)) =
            (&args[0], &args[1], &args[2])
        {
            let s_ref = &**s;

            let len = s_ref.len() as i32;
            let start = start.max(&0).min(&len);
            let end = end.max(&0).min(&len);

            if start > end {
                return Value::String(Rc::new(String::new()));
            }

            let slice = s_ref
                .char_indices()
                .skip_while(|(i, _)| *i < *start as usize)
                .take_while(|(i, _)| *i < *end as usize)
                .map(|(_, c)| c)
                .collect::<String>();

            return Value::String(Rc::new(slice));
        }

        Value::Void
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
}

impl NativeLibrary for GPPStringNativeLibrary {
    fn register_functions(&self, bridge: &mut dyn crate::runtime::ffi::NativeBridge) {
        register_native_funcs!(
            bridge,
            [
                str_len,
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
                str_slice
            ]
        );
    }
}
