use crate::{runtime::ffi::NativeLibrary, stdlib::net::http::GPPHttpLibrary};

pub mod http;

pub struct GPPNetLibrary;

impl NativeLibrary for GPPNetLibrary {
    fn register_functions(&self, bridge: &mut dyn crate::runtime::ffi::NativeBridge) {
        let mut native_libs: Vec<Box<dyn NativeLibrary>> = Vec::new();

        native_libs.push(Box::new(GPPHttpLibrary {}));

        for lib in native_libs {
            lib.register_functions(bridge);
        }
    }
}
