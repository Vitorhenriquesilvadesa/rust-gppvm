use super::{ instructions::Instruction, ir_generator::{ IRFunction, IntermediateCode } };

pub struct Decompiler {}

impl Decompiler {
    pub fn decompile(code: &IntermediateCode) {
        for (name, function) in &code.functions {
            println!("====== {} ======", name);
            Decompiler::decompile_function(function);
            println!("==================\n\n");
        }
    }

    fn decompile_function(function: &IRFunction) {
        let mut index = 0;

        while index < function.chunk.code.len() {
            Decompiler::decompile_instruction(&mut index, &function.chunk.code);
        }
    }

    fn combine_u8(high: u8, low: u8) -> u16 {
        ((high as u16) << 8) | (low as u16)
    }

    fn decompile_instruction(index: &mut usize, code: &[u8]) {
        match Instruction::try_from(code[*index]) {
            Ok(i) => {
                match i {
                    Instruction::Push => {
                        println!(
                            "{:?}    {}",
                            i,
                            Decompiler::combine_u8(code[*index + 1], code[*index + 2])
                        );
                        *index += 2;
                    }
                    _ => {
                        println!("{:?}", i);
                    }
                }
            }
            Err(msg) => {}
        }

        *index += 1;
    }
}
