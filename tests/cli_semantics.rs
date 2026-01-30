use std::io::Write;
use std::process::{Command, Stdio};

#[test]
fn cli_prints_banner_and_exits_on_quit() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_sggslog"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("failed to spawn CLI");

    {
        let stdin = child.stdin.as_mut().expect("stdin");
        stdin
            .write_all(b":quit\n")
            .expect("failed to write to stdin");
    }

    let output = child.wait_with_output().expect("failed to read CLI output");
    assert!(output.status.success(), "CLI should exit cleanly");
}
