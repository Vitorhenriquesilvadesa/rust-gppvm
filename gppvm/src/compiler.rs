#![allow(unused_variables)]
use lexer::Lexer;
use parser::Parser;
use semantics::SemanticAnalyzer;
use shared_components::util::read_file_without_bom;

use gppvm_core::{ argument::CompilerArguments, pipeline::CompilationPipeline };
use std::{ env, path::PathBuf, time::Instant };

pub fn run(config: CompilerArguments) -> Result<(), String> {
    if config.args.len() != 3 {
        return Err("Usage gppvm -c file.gpp -o file.grc".to_string());
    }

    let path = format!(
        "{}\\{}",
        env
            ::current_dir()
            .map_err(|e| e.to_string())?
            .to_str()
            .unwrap_or(""),
        config.args[0].as_str()
    );

    let output_path = format!(
        "{}\\{}",
        env
            ::current_dir()
            .map_err(|e| e.to_string())?
            .to_str()
            .unwrap_or(""),
        config.args[2].as_str()
    );

    println!("{}", path);

    let source = match read_file_without_bom(&path) {
        Ok(s) => s,
        Err(msg) => {
            return Err(msg.to_string());
        }
    };

    let mut pipeline = CompilationPipeline::new()
        .with_output(PathBuf::from(output_path))
        .with_source(source);

    pipeline.add_stage::<Lexer>();
    pipeline.add_stage::<Parser>();
    pipeline.add_stage::<SemanticAnalyzer>();

    let start = Instant::now();
    pipeline.execute();

    println!("Compiler took: {:?}", start.elapsed());

    Ok(())
}
