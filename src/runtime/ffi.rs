use super::objects::Value;

pub type NativeFnPtr = fn(Vec<Value>) -> Value;

#[derive(Clone)]
pub struct NativeFunction {
    pub handler: NativeFnPtr,
    pub arity: u8,
}

impl NativeFunction {
    pub fn new(handler: NativeFnPtr, arity: u8) -> Self {
        Self { handler, arity }
    }
}

pub trait NativeBridge {
    fn bind(&mut self, name: &str, func: NativeFnPtr);
}

pub trait NativeLibrary {
    fn register_functions(&self, bridge: &mut dyn NativeBridge);
}

#[macro_export]
macro_rules! register_native_funcs {
    ($bridge:expr, [$($name:ident),* $(,)?]) => {
        $(
            $bridge.bind(stringify!($name), Self::$name);
        )*
    };
}
