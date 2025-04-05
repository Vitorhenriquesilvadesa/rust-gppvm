#![allow(dead_code)]

#[cfg(test)]
mod tests {
    use std::{ env, path::PathBuf };

    use gppvm_core::CompilationPipeline;
    use lexer::Lexer;
    use shared_components::{
        read_file_without_bom,
        Color,
        CompilationError,
        CompilerErrorStack,
        Severity,
    };

    #[test]
    fn lexer_invalid_character() {
        let mut pipeline = get_pipeline_with_source_and_output_path(
            "../test_scripts/invalid_character.gpp",
            "test_scripts/test.grc"
        );

        pipeline.add_stage::<Lexer>();

        let result = pipeline.execute();
        expect_error_message(result, "Invalid character");
    }

    #[test]
    fn lexer_unterminated_string() {
        let mut pipeline = get_pipeline_with_source_and_output_path(
            "../test_scripts/unerminated_string.gpp",
            "test_scripts/test.grc"
        );

        pipeline.add_stage::<Lexer>();

        let result = pipeline.execute();
        expect_error_message(result, "Unterminated string");
    }

    fn expect_error_message(result: Result<(), CompilerErrorStack>, msg: &str) {
        match result {
            Ok(_) => {}
            Err(stack) => {
                for error in stack.get_errors() {
                    println!("{}", format_message(error));
                    assert!(format_message(error).contains(msg));
                }
            }
        }
    }

    fn panic_if_has_errors(result: Result<(), CompilerErrorStack>) {
        match result {
            Ok(_) => {}
            Err(stack) => {
                for error in stack.get_errors() {
                    println!("{}", format_message(error));
                    panic!();
                }
            }
        }
    }

    fn get_pipeline_with_source_and_output_path(src: &str, out: &str) -> CompilationPipeline {
        let output_path = format!(
            "{}\\{}",
            env
                ::current_dir()
                .map_err(|e| e.to_string())
                .unwrap()
                .to_str()
                .unwrap_or(""),
            out
        );
        let output_path = PathBuf::from(output_path);

        let path = format!(
            "{}\\{}",
            env
                ::current_dir()
                .map_err(|e| e.to_string())
                .unwrap()
                .to_str()
                .unwrap_or(""),
            src
        );

        let source = read_file_without_bom(&path).unwrap();

        let pipeline = CompilationPipeline::new()
            .with_output(PathBuf::from(output_path))
            .with_source(source);

        pipeline
    }

    fn format_message(error: &CompilationError) -> String {
        let severity_label = match error.msg.severity {
            Severity::Info => "\x1b[34mInfo\x1b[0m",
            Severity::Warn => "\x1b[33mWarning\x1b[0m",
            Severity::Error => "\x1b[31mError\x1b[0m",
        };

        let mut output = String::new();
        output.push_str(&format!("[\x1b[1m{}\x1b[0m]", severity_label));

        if let Some(line) = error.line {
            output.push_str(&format!("\x1b[1m[line {}]\x1b[0m: ", line));
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
            output.push_str(&format!("{}{}{}", ansi_color, fragment.content, "\x1b[0m"));
        }

        output.push('\n');
        output
    }
}
