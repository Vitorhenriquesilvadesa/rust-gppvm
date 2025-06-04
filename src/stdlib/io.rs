use std::{
    env,
    fs::{write, OpenOptions},
    io::{self, Write},
    path::PathBuf,
    rc::Rc,
};

use crate::{
    gpp_error, read_file_without_bom, register_native_funcs,
    runtime::{ffi::NativeLibrary, objects::Value},
};

pub struct GPPStdIOLibrary;

impl GPPStdIOLibrary {
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
            let path = Self::get_full_path(path.to_string());

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
                let _ = write(Self::get_full_path(path.to_string()), &**content);
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
                    .open(Self::get_full_path(path.to_string()))
                {
                    let _ = writeln!(file, "{}", &**content);
                }
            }
        }
        Value::Void
    }
}

impl NativeLibrary for GPPStdIOLibrary {
    fn register_functions(&self, bridge: &mut dyn crate::runtime::ffi::NativeBridge) {
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
            ]
        );
    }
}
