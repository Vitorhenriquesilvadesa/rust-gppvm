#![allow(dead_code)]
#![allow(deprecated)]
#![allow(unused_variables)]
use std::fs::{write, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::{
    cell::RefCell,
    env,
    io::{self},
    rc::Rc,
    thread::sleep,
    time::{Duration, SystemTime, UNIX_EPOCH},
};

use rand::Rng;

use crate::{gpp_error, read_file_without_bom, register_native_funcs};

use super::{
    ffi::{NativeBridge, NativeLibrary},
    objects::{List, Value},
};

pub struct StdLibrary;

impl StdLibrary {
    pub fn get_lib() -> Self {
        Self {}
    }

    pub fn print(args: Vec<Value>) -> Value {
        if let Some(val) = args.first() {
            print!("{}", val);
            io::stdout().flush().unwrap();
        }
        Value::Void
    }

    pub fn println(args: Vec<Value>) -> Value {
        if let Some(val) = args.first() {
            println!("{}", val);
        }
        Value::Void
    }

    pub fn debug(args: Vec<Value>) -> Value {
        if let Some(val) = args.first() {
            eprintln!("[DEBUG] {}", val);
        }
        Value::Void
    }

    pub fn input(_: Vec<Value>) -> Value {
        let mut buffer = String::new();
        io::stdin().read_line(&mut buffer).unwrap();
        Value::String(Rc::new(buffer.trim_end().to_string()))
    }

    pub fn read_line(_: Vec<Value>) -> Value {
        Self::input(vec![])
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

    pub fn read_int(_: Vec<Value>) -> Value {
        let mut buffer = String::new();
        io::stdin().read_line(&mut buffer).unwrap();
        match buffer.trim().parse::<i32>() {
            Ok(n) => Value::Int(n),
            Err(_) => gpp_error!("Cannot perform read_int."),
        }
    }

    pub fn read_float(_: Vec<Value>) -> Value {
        let mut buffer = String::new();
        io::stdin().read_line(&mut buffer).unwrap();
        match buffer.trim().parse::<f32>() {
            Ok(n) => Value::Float(n),
            Err(_) => gpp_error!("Cannot perform read_float."),
        }
    }

    fn get_current_dir() -> String {
        let current_dir = env::current_dir().unwrap();
        return current_dir.to_str().unwrap().into();
    }

    fn get_full_path(path: String) -> PathBuf {
        let current_path = format!(
            "{}{}{}",
            env::current_dir()
                .map_err(|e| e.to_string())
                .unwrap()
                .to_str()
                .unwrap_or(""),
            std::path::MAIN_SEPARATOR,
            env::args().into_iter().collect::<Vec<String>>()[2].as_str()
        );

        let full_path = PathBuf::from(&current_path);

        let root = full_path
            .parent()
            .ok_or("Cannot get parent directory.")
            .unwrap()
            .to_path_buf();

        let absolute_path = root.join(&path);

        return absolute_path;
    }

    pub fn read_file(args: Vec<Value>) -> Value {
        if let Some(Value::String(path)) = args.first() {
            let path = StdLibrary::get_full_path(path.to_string());

            match read_file_without_bom(&path.to_str().unwrap()) {
                Ok(content) => Value::String(Rc::new(content)),
                Err(e) => {
                    gpp_error!("Cannot read file '{}': {}", path.to_str().unwrap(), e);
                }
            }
        } else {
            Value::String(Rc::new("".to_string()))
        }
    }

    pub fn write_file(args: Vec<Value>) -> Value {
        if args.len() == 2 {
            if let (Value::String(path), Value::String(content)) = (&args[0], &args[1]) {
                let _ = write(StdLibrary::get_full_path(path.to_string()), &**content);
            }
        }
        Value::Void
    }

    pub fn append_file(args: Vec<Value>) -> Value {
        if args.len() == 2 {
            if let (Value::String(path), Value::String(content)) = (&args[0], &args[1]) {
                if let Ok(mut file) = OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(StdLibrary::get_full_path(path.to_string()))
                {
                    let _ = writeln!(file, "{}", &**content);
                }
            }
        }
        Value::Void
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

    fn int_to_string(args: Vec<Value>) -> Value {
        if let Value::Int(i) = &args[0] {
            return Value::String(Rc::new(i.to_string()));
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

    fn list_append(args: Vec<Value>) -> Value {
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

    fn list_pop(args: Vec<Value>) -> Value {
        if let Value::Object(obj_ptr) = &args[0] {
            let value = &args[1];

            if let Value::Int(i) = value {
                obj_ptr
                    .borrow_mut()
                    .as_any_mut()
                    .downcast_mut::<List>()
                    .unwrap()
                    .elements
                    .remove(*i as usize);
            }

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

    fn int_sqrt(args: Vec<Value>) -> Value {
        if let Value::Int(a) = args[0] {
            Value::Float((a as f32).sqrt())
        } else {
            unreachable!()
        }
    }

    fn float_sqrt(args: Vec<Value>) -> Value {
        if let Value::Float(a) = args[0] {
            Value::Float(a.sqrt())
        } else {
            unreachable!()
        }
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
                println,
                debug,
                input,
                read_line,
                read_int,
                read_float,
                read_file,
                write_file,
                append_file,
                int,
                float,
                bool,
                int_to_float,
                float_to_int,
                random_range,
                len,
                list_append,
                list_pop,
                args,
                exit,
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
                int_abs,
                int_is_even,
                int_to_string,
                int_is_odd,
                int_sign,
                int_max,
                int_min,
                int_clamp,
                int_sqrt,
                exception,
                now_ms,
                float_sqrt,
                sleep
            ]
        );
    }
}
