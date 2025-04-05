#![allow(dead_code)]
use std::rc::Rc;

#[derive(Copy, Clone, Debug)]
pub enum ObjectKind {
    String,
    List,
    Tuple,
    Kind,
    Instance,
}

#[derive(Copy, Clone, Debug)]
#[repr(C)]
pub struct ObjDescriptor {
    kind: ObjectKind,
}

impl ObjDescriptor {
    pub fn new_string() -> Self {
        Self { kind: ObjectKind::String }
    }

    pub fn new_list() -> Self {
        Self { kind: ObjectKind::List }
    }

    pub fn new_tuple() -> Self {
        Self { kind: ObjectKind::Tuple }
    }

    pub fn new_instance() -> Self {
        Self { kind: ObjectKind::Instance }
    }
}

#[derive(Clone, Debug)]
#[repr(C)]
pub struct ObjString {
    pub descriptor: ObjDescriptor,
    pub chars: Rc<String>,
}

impl ObjString {
    pub fn new(chars: Rc<String>) -> Self {
        Self { descriptor: ObjDescriptor::new_string(), chars }
    }
}
