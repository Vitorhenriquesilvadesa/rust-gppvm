#![allow(dead_code)]
#![allow(unused_macros)]
use std::{ cell::RefCell, fmt::{ Debug, Display }, rc::Rc };

#[derive(Debug, Eq, PartialEq)]
pub enum ObjectKind {
    Int,
    Float,
    String,
    Boolean,
    Obj,
    Void,
}

#[derive(Clone)]
pub enum Value {
    Int(i32),
    Float(f32),
    Bool(bool),
    String(Rc<String>),
    Void,
    Object(Rc<RefCell<dyn Object>>),
}

impl Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Bool(v) => f.write_str(&format!("{}", v)),
            Value::Int(v) => f.write_str(&format!("{}", v)),
            Value::Float(v) => f.write_str(&format!("{}", v)),
            Value::String(v) => f.write_str(&format!("{}", v)),
            Value::Void => f.write_str("void"),
            Value::Object(obj_ptr) => f.write_str(&format!("{}", obj_ptr.borrow().to_string())),
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Bool(v) => f.write_str(&format!("{}", v)),
            Value::Int(v) => f.write_str(&format!("{}", v)),
            Value::Float(v) => f.write_str(&format!("{}", v)),
            Value::String(v) => f.write_str(&format!("{}", v)),
            Value::Void => f.write_str("void"),
            Value::Object(obj_ptr) => f.write_str(&format!("{}", obj_ptr.borrow().to_string())),
        }
    }
}

pub trait Object {
    fn as_any(&self) -> &dyn std::any::Any;
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any;
    fn get_kind(&self) -> ObjectKind;
    fn type_name(&self) -> &'static str;
    fn to_string(&self) -> String;
}

impl Debug for dyn Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&String::from(format!("{:?}", self)))
    }
}

pub struct Instance {
    pub fields: Vec<Value>,
}

impl Instance {
    pub fn new(fields: Vec<Value>) -> Self {
        Self { fields }
    }
}

impl Object for Instance {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }

    fn get_kind(&self) -> ObjectKind {
        ObjectKind::Obj
    }

    fn type_name(&self) -> &'static str {
        "object"
    }

    fn to_string(&self) -> String {
        format!("{:?}", self.fields)
    }
}

pub struct List {
    pub elements: Vec<Value>,
}

impl List {
    pub fn new(elements: Vec<Value>) -> Self {
        Self { elements }
    }
}

impl Object for List {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }

    fn get_kind(&self) -> ObjectKind {
        ObjectKind::Obj
    }

    fn type_name(&self) -> &'static str {
        "list"
    }

    fn to_string(&self) -> String {
        format!("{:?}", self.elements)
    }
}

macro_rules! impl_object {
    ($type:ident, $kind:expr, $name:expr, $inner_type:ty) => {
        impl AsRaw<$inner_type> for $type {
            fn get_raw(&self) -> $inner_type {
                self.v.clone()
            }
        }

        impl Object for $type {
            fn as_any(&self) -> &dyn std::any::Any {
                self
            }

            fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
                self
            }

            fn get_kind(&self) -> ObjectKind {
                $kind
            }

            fn type_name(&self) -> &'static str {
                $name
            }

            fn to_string(&self) -> String {
                format!("{:?}", self.v)
            }
        }
    };
}
