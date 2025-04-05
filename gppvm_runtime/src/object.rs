#![allow(dead_code)]

use crate::native_objects::ObjString;

use super::native_objects::ObjDescriptor;

#[derive(Debug, Clone)]
pub enum ValueKind {
    Int,
    Float,
    Boolean,
    Object,
    String,
}

pub union As {
    pub int: i32,
    pub float: f32,
    pub boolean: bool,
    pub object: *mut ObjDescriptor,
}

impl std::fmt::Debug for As {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        unsafe {
            let string = self.object as *mut ObjString;
            write!(
                f,
                "As: int={} | float={} | bool={}, obj={:#?}",
                self.int,
                self.float,
                self.boolean,
                string.as_ref().unwrap()
            )
        }
    }
}

#[derive(Debug)]
pub struct Value {
    pub kind: ValueKind,
    pub as_wrapper: As,
}

impl Value {
    pub fn new(kind: ValueKind, as_wrapper: As) -> Self {
        Self { kind, as_wrapper }
    }
}
