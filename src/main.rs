use gppvm::compiler::Compiler;
use std::fs;
use std::io::{self, Read};

fn read_file_without_bom(path: &str) -> io::Result<String> {
    let mut file = fs::File::open(path)?;
    let mut buffer = Vec::new();
    file.read_to_end(&mut buffer)?;

    let content = if buffer.starts_with(&[0xEF, 0xBB, 0xBF]) {
        String::from_utf8_lossy(&buffer[3..]).to_string()
    } else {
        String::from_utf8_lossy(&buffer).to_string()
    };

    Ok(content)
}

fn main() {
    let source = match read_file_without_bom("res/test.gpp") {
        Ok(s) => {
            println!("{}", s);
            s
        }
        Err(msg) => {
            println!("{}", msg);
            return;
        }
    };

    let mut compiler = Compiler::new();

    compiler.compile(source);
}
