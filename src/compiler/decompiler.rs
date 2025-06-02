use super::{
    chunk::CompileTimeChunk,
    instructions::Instruction,
    ir_generator::{IRFunction, IntermediateCode},
    semantic_types::TypeDescriptor,
};

pub struct Decompiler {}

impl Decompiler {
    pub fn decompile(code: &IntermediateCode) {
        for (name, info) in &code.native_functions {
            Decompiler::decompile_native_function(name, info.id);
        }

        for (descriptor, info) in &code.methods {
            Decompiler::decompile_methods(descriptor, info, &code);
        }

        for (name, function) in &code.functions {
            let width = 60;
            println!(
                "{}",
                format!(
                    "{:=^1$}",
                    format!(
                        " {} (id = {}; arity = {}) ",
                        name, function.id, function.arity
                    ),
                    width
                )
            );
            Decompiler::decompile_function(function, code);
            println!("{}", "=".repeat(width));
            println!("\n");
        }
    }

    fn decompile_function(function: &IRFunction, code: &IntermediateCode) {
        let mut index = 0;

        while index < function.chunk.code.len() {
            print!("|");
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
                let padded_instruction = format!("{:<15}", instruction_name);
                let instr_index = format!("{:03}", index);

                match instruction {
                    Instruction::Push => {
                        let pos = Decompiler::combine_u8_to_u16(code[*index + 1], code[*index + 2]);
                        println!(
                            "{}  {} {}   ; {:?}",
                            instr_index, padded_instruction, pos, chunk.constants[pos as usize]
                        );
                        *index += 2;
                    }
                    Instruction::GetLocal
                    | Instruction::SetLocal
                    | Instruction::IncrementLocal
                    | Instruction::DecrementLocal => {
                        println!(
                            "{}  {} {}",
                            instr_index,
                            padded_instruction,
                            code[*index + 1]
                        );
                        *index += 1;
                    }

                    Instruction::Call => {
                        let function_index = Decompiler::combine_u8_to_u32(
                            code[*index + 1],
                            code[*index + 2],
                            code[*index + 3],
                            code[*index + 4],
                        );

                        let arity = code[*index + 5];

                        println!(
                            "{}  {} {}   ; {} ({} args)",
                            instr_index,
                            padded_instruction,
                            function_index,
                            ir.graph.inverse_connections[&function_index],
                            arity
                        );
                        *index += 5;
                    }

                    Instruction::InvokeVirtual => {
                        let vtable_index = Decompiler::combine_u8_to_u32(
                            code[*index + 1],
                            code[*index + 2],
                            code[*index + 3],
                            code[*index + 4],
                        );

                        let function_index = Decompiler::combine_u8_to_u32(
                            code[*index + 5],
                            code[*index + 6],
                            code[*index + 7],
                            code[*index + 8],
                        );

                        let arity = code[*index + 9];

                        println!(
                            "{}  {} {}   ; ({} args)",
                            instr_index, padded_instruction, function_index, arity
                        );

                        *index += 9;
                    }

                    Instruction::InvokeNative => {
                        let function_index = Decompiler::combine_u8_to_u32(
                            code[*index + 1],
                            code[*index + 2],
                            code[*index + 3],
                            code[*index + 4],
                        );

                        let arity = code[*index + 5];

                        println!(
                            "{}  {} {}   ; ({} args)",
                            instr_index, padded_instruction, function_index, arity
                        );
                        *index += 5;
                    }

                    Instruction::New => {
                        let arity = code[*index + 1];

                        println!("{}  {} {}", instr_index, padded_instruction, arity);
                        *index += 1;
                    }

                    Instruction::GetField | Instruction::SetField | Instruction::Array => {
                        let field_index = code[*index + 1];

                        println!("{}  {} {}", instr_index, padded_instruction, field_index);
                        *index += 1;
                    }

                    Instruction::Greater => {
                        println!("{} greater", instr_index);
                    }

                    Instruction::JFalse
                    | Instruction::Jump
                    | Instruction::Loop
                    | Instruction::JTrue => {
                        let offset = Decompiler::combine_u8_to_u32(
                            code[*index + 1],
                            code[*index + 2],
                            code[*index + 3],
                            code[*index + 4],
                        );

                        println!("{}  {}     ; {}", instr_index, padded_instruction, offset);
                        *index += 4;
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

    fn decompile_native_function(name: &str, id: u32) {
        let width = 60;
        println!(
            "{}",
            format!("{:=^1$}", format!(" {} (native_id = {}) ", name, id), width)
        );
        println!("{}", "=".repeat(width));
        println!("\n");
    }

    fn decompile_methods(
        descriptor: &TypeDescriptor,
        info: &Vec<IRFunction>,
        ir: &IntermediateCode,
    ) {
        let mut index = 0usize;
        for method in info {
            let width = 60;

            println!(
                "{}",
                format!(
                    "{:=^1$}",
                    format!(
                        " {} (type = {}, arity = {}) ",
                        method.name, descriptor.name, method.arity
                    ),
                    width
                )
            );

            index = 0;

            while index < method.chunk.code.len() {
                Decompiler::decompile_instruction(&mut index, &method.chunk, &ir);
            }

            println!("{}", "=".repeat(width));
            println!("\n");
        }
    }
}
