#[cfg(test)]
mod test {
    use assert_cmd::Command;
    use predicates::{prelude::PredicateBooleanExt, str::contains};

    #[test]
    fn should_print_binary_operation_results() {
        let mut cmd = Command::cargo_bin("gppvm").unwrap();
        cmd.args(["-c", "res/test/should_print_binary_operation_results.gpp"])
            .assert()
            .success()
            .stdout(contains("50").and(contains("0")));
    }

    #[test]
    fn should_fail_with_variable_not_declared_error() {
        let output = Command::cargo_bin("gppvm")
            .unwrap()
            .args([
                "-c",
                "res/test/should_panic_with_variable_is_out_of_context.gpp",
            ])
            .output()
            .expect("failed to run gppvm");

        assert!(!output.status.success(), "esperava falha, mas foi sucesso");

        let stderr = String::from_utf8_lossy(&output.stderr);
        println!("stderr:\n{}", stderr);

        assert!(
            stderr.contains("The variable 'x' are not declared here"),
            "mensagem de erro inesperada"
        );
    }

    #[test]
    fn should_print_division_and_precedence() {
        let mut cmd = Command::cargo_bin("gppvm").unwrap();
        cmd.args(["-c", "res/test/should_print_division_and_precedence.gpp"])
            .assert()
            .success()
            .stdout(contains("2").and(contains("11")));
    }

    #[test]
    fn should_fail_with_variable_redeclaration() {
        let output = Command::cargo_bin("gppvm")
            .unwrap()
            .args(["-c", "res/test/should_fail_with_variable_redeclaration.gpp"])
            .output()
            .expect("failed to run gppvm");

        assert!(
            !output.status.success(),
            "expected failure, but it was a success"
        );

        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("The name 'x' was previous declared in current scope."),
            "Unexpected error message"
        );
    }
}
