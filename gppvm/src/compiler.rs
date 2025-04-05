#![allow(unused_variables)]
use lexer::Lexer;
use parser::Parser;
use semantics::SemanticAnalyzer;
use shared_components::{ util::read_file_without_bom, Color, CompilerErrorStack, Severity };

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
    let result = pipeline.execute();

    match result {
        Ok(_) => {}
        Err(errors) => {
            print_errors(errors);
        }
    }

    println!("Compiler took: {:?}", start.elapsed());

    Ok(())
}

pub fn print_errors(stack: CompilerErrorStack) {
    for error in stack.get_errors() {
        let severity_label = match error.msg.severity {
            Severity::Info => "\x1b[34mInfo\x1b[0m",
            Severity::Warn => "\x1b[33mWarning\x1b[0m",
            Severity::Error => "\x1b[31mError\x1b[0m",
        };

        eprint!("[\x1b[1m{}\x1b[0m]", severity_label);

        if let Some(line) = error.line {
            eprint!("\x1b[1m[line {}]\x1b[0m: ", line);
        }

        for fragment in &error.msg.fragments {
            let ansi_color = match fragment.color {
                Color::Red => "\x1b[31m",
                Color::Orange => "\x1b[38;5;208m",
                Color::Yellow => "\x1b[33m",
                Color::Green => "\x1b[32m",
                Color::White => "\x1b[37m",
                Color::Purple => "\x1b[35m",
            };
            eprint!("{}{}{}", ansi_color, fragment.content, "\x1b[0m");
        }

        eprintln!();
    }
}
