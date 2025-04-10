use std::{ fmt::Debug, rc::Rc };

#[derive(Debug)]
pub enum ObjectKind {
    Int,
    Float,
    String,
    Boolean,
    Obj,
    Void,
}

pub trait Object {
    fn as_any(&self) -> &dyn std::any::Any;
    fn get_kind(&self) -> ObjectKind;
    fn type_name(&self) -> &'static str;
    fn to_string(&self) -> String;
}

pub trait AsRaw<T> {
    fn get_raw(&self) -> T;
}

pub struct Int32 {
    pub v: i32,
}

impl Debug for Int32 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("{}", self.v))
    }
}

impl AsRaw<i32> for Int32 {
    fn get_raw(&self) -> i32 {
        self.v
    }
}

impl Object for Int32 {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn get_kind(&self) -> ObjectKind {
        ObjectKind::Int
    }

    fn type_name(&self) -> &'static str {
        "int"
    }

    fn to_string(&self) -> String {
        format!("{}", self.v)
    }
}

impl Int32 {
    pub fn new(v: i32) -> Self {
        Self { v }
    }
}

#[derive(Debug)]
pub struct Float32 {
    pub v: f32,
}

impl AsRaw<f32> for Float32 {
    fn get_raw(&self) -> f32 {
        self.v
    }
}

impl Object for Float32 {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn get_kind(&self) -> ObjectKind {
        ObjectKind::Float
    }

    fn type_name(&self) -> &'static str {
        "float"
    }

    fn to_string(&self) -> String {
        format!("{}", self.v)
    }
}

impl Float32 {
    pub fn new(v: f32) -> Self {
        Self { v }
    }
}

#[derive(Debug)]
pub struct Bool8 {
    pub v: bool,
}

impl AsRaw<bool> for Bool8 {
    fn get_raw(&self) -> bool {
        self.v
    }
}

impl Object for Bool8 {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn get_kind(&self) -> ObjectKind {
        ObjectKind::Boolean
    }

    fn type_name(&self) -> &'static str {
        "bool"
    }

    fn to_string(&self) -> String {
        format!("{}", self.v)
    }
}

impl Bool8 {
    pub fn new(v: bool) -> Self {
        Self { v }
    }
}

#[derive(Debug)]
pub struct GPPString {
    pub v: Rc<String>,
}

impl AsRaw<Rc<String>> for GPPString {
    fn get_raw(&self) -> Rc<String> {
        self.v.clone()
    }
}

impl Object for GPPString {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn get_kind(&self) -> ObjectKind {
        ObjectKind::String
    }

    fn type_name(&self) -> &'static str {
        "str"
    }

    fn to_string(&self) -> String {
        format!("{}", self.v)
    }
}

impl GPPString {
    pub fn new(v: Rc<String>) -> Self {
        Self { v }
    }
}

#[derive(Debug)]
pub struct Void {
    pub v: i32,
}

impl AsRaw<i32> for Void {
    fn get_raw(&self) -> i32 {
        0
    }
}

impl Object for Void {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn get_kind(&self) -> ObjectKind {
        ObjectKind::Void
    }

    fn type_name(&self) -> &'static str {
        "void"
    }

    fn to_string(&self) -> String {
        format!("void")
    }
}

impl Void {
    pub fn new() -> Self {
        Self { v: 0 }
    }
}
