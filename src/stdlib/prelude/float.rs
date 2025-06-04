use crate::{
    register_native_funcs,
    runtime::{ffi::NativeLibrary, objects::Value},
};

pub struct GPPFloatLibrary;

impl GPPFloatLibrary {
    fn float_sqrt(args: Vec<Value>) -> Value {
        if let Value::Float(a) = args[0] {
            Value::Float(a.sqrt())
        } else {
            unreachable!()
        }
    }

    fn float_to_int(args: Vec<Value>) -> Value {
        if let Value::Float(f) = &args[0] {
            return Value::Int(*f as i32);
        }

        unreachable!("Found value '{}'.", &args[0]);
    }
}

impl NativeLibrary for GPPFloatLibrary {
    fn register_functions(&self, bridge: &mut dyn crate::runtime::ffi::NativeBridge) {
        register_native_funcs!(bridge, [float_to_int, float_sqrt,]);
    }
}
