use super::{
    chunk::CompileTimeChunk,
    instructions::Instruction,
    ir_generator::{ IRFunction, IntermediateCode },
};

pub struct Decompiler {}

impl Decompiler {
    pub fn decompile(code: &IntermediateCode) {
        for (name, function) in &code.functions {
            println!("====== {} ======", name);
            Decompiler::decompile_function(function, code);
            println!("==================\n\n");
        }
    }

    fn decompile_function(function: &IRFunction, code: &IntermediateCode) {
        let mut index = 0;

        while index < function.chunk.code.len() {
            Decompiler::decompile_instruction(&mut index, &function.chunk, code);
        }
    }

    fn combine_u8_to_u16(high: u8, low: u8) -> u16 {
        ((high as u16) << 8) | (low as u16)
    }

    fn combine_u8_to_u32(byte1: u8, byte2: u8, byte3: u8, byte4: u8) -> u32 {
        ((byte1 as u32) << 24) | ((byte2 as u32) << 16) | ((byte3 as u32) << 8) | (byte4 as u32)
    }

    fn decompile_instruction(index: &mut usize, chunk: &CompileTimeChunk, ir: &IntermediateCode) {
        let code = &chunk.code;

        match Instruction::try_from(code[*index]) {
            Ok(instruction) => {
                let instruction_name = format!("{:?}", instruction).to_lowercase();
                let padded_instruction = format!("{:<20}", instruction_name);
                let instr_index = format!("0x{:02X}", instruction as u8);

                match instruction {
                    Instruction::Push => {
                        let pos = Decompiler::combine_u8_to_u16(code[*index + 1], code[*index + 2]);
                        println!(
                            "{}  {} {}   ; {:?}",
                            instr_index,
                            padded_instruction,
                            pos,
                            chunk.constants[pos as usize]
                        );
                        *index += 2;
                    }
                    Instruction::GetLocal | Instruction::SetLocal => {
                        println!("{}  {} {}", instr_index, padded_instruction, code[*index + 1]);
                        *index += 1;
                    }

                    Instruction::Call => {
                        let function_index = Decompiler::combine_u8_to_u32(
                            code[*index + 1],
                            code[*index + 2],
                            code[*index + 3],
                            code[*index + 4]
                        );

                        let arity = code[*index + 5];

                        println!(
                            "{}  {} {}   ; {}",
                            instr_index,
                            padded_instruction,
                            function_index,
                            arity
                        );
                        *index += 5;
                    }
                    _ => {
                        println!("{}  {}", instr_index, padded_instruction);
                    }
                }
            }
            Err(_) => {}
        }

        *index += 1;
    }
}
