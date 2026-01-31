use std::fs;
use std::io::Write;
use std::process::{Command, Stdio};
use std::time::{SystemTime, UNIX_EPOCH};

fn run_cli(input: &str) -> String {
    let mut child = Command::new(env!("CARGO_BIN_EXE_sggslog"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn CLI");

    {
        let stdin = child.stdin.as_mut().expect("stdin");
        stdin
            .write_all(input.as_bytes())
            .expect("failed to write to stdin");
    }

    let output = child.wait_with_output().expect("failed to read CLI output");
    assert!(output.status.success(), "CLI should exit cleanly");
    let mut all = String::new();
    all.push_str(&String::from_utf8_lossy(&output.stdout));
    all.push_str(&String::from_utf8_lossy(&output.stderr));
    all
}

fn write_temp_file(prefix: &str, contents: &str) -> std::path::PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time")
        .as_nanos();
    let path = std::env::temp_dir().join(format!("{}_{}.sggs", prefix, unique));
    fs::write(&path, contents).expect("write temp file");
    path
}

fn contains_any(haystack: &str, needles: &[&str]) -> bool {
    let hay = haystack.to_ascii_lowercase();
    needles
        .iter()
        .any(|n| hay.contains(&n.to_ascii_lowercase()))
}

#[test]
fn cli_prints_banner_and_exits_on_quit() {
    let output = run_cli(":quit\n");
    assert!(
        output.contains("SGGSLog"),
        "banner should mention SGGSLog"
    );
}

#[test]
fn cli_load_query_stream_and_exhaustion() {
    let path = write_temp_file("sggslog_cli_load", "p alpha\np beta\n");
    let input = format!(
        ":load \"{}\"\n?- p X\n:next\n:next\n:quit\n",
        path.to_string_lossy()
    );
    let output = run_cli(&input);
    assert!(
        contains_any(&output, &["loaded", "load"]),
        "load directive should report success"
    );
    assert!(
        output.contains("alpha") && output.contains("beta") && output.contains("X"),
        "query answers should include alpha and beta bindings"
    );
    assert!(
        contains_any(&output, &["exhausted", "no more", "no answers"]),
        "stream exhaustion should be reported"
    );

    let _ = fs::remove_file(&path);
}

#[test]
fn cli_projection_toggle_changes_visibility() {
    let path = write_temp_file("sggslog_cli_proj", "\u{2203}X (p X)\n");
    let input_default = format!(
        ":load \"{}\"\n?- p X\n:quit\n",
        path.to_string_lossy()
    );
    let output_default = run_cli(&input_default);
    assert!(
        contains_any(
            &output_default,
            &["no answers", "none", "no solution", "false", "exhausted"]
        ),
        "default projection should hide internal witnesses"
    );

    let input_internal = format!(
        ":load \"{}\"\n:set projection allow_internal\n?- p X\n:quit\n",
        path.to_string_lossy()
    );
    let output_internal = run_cli(&input_internal);
    assert!(
        output_internal.contains("X")
            && !contains_any(
                &output_internal,
                &["no answers", "none", "no solution", "false", "exhausted"]
            ),
        "allow_internal should produce a visible binding"
    );

    let _ = fs::remove_file(&path);
}

#[test]
fn cli_respects_resource_limit() {
    let input = ":set timeout_ms 0\n?- p X\n:quit\n";
    let output = run_cli(input);
    assert!(
        contains_any(&output, &["resource", "limit", "timeout"]),
        "resource limit should be reported"
    );
}
