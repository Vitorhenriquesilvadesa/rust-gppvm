#![allow(dead_code)]

use std::rc::Rc;

use super::{ bytecode::Function, object::As };

const FRAMES_MAX: u32 = 256;

struct Frame {
    function: Function,
    ip: usize,
    slots: Vec<As>,
}

pub struct VirtualMachine {
    ip: usize,
    sp: usize,
    stack: Vec<Rc<As>>,
    frames: Vec<Frame>,
}
