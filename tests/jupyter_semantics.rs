use sggslog::jupyter::Kernel;
use std::collections::HashSet;
use std::fs;
use std::time::{SystemTime, UNIX_EPOCH};

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
fn kernel_load_query_stream_and_exhaustion() {
    let path = write_temp_file("sggslog_kernel_load", "p alpha\np beta\n");
    let mut kernel = Kernel::new();

    let load = kernel
        .execute(&format!(":load \"{}\"", path.to_string_lossy()))
        .expect("load should succeed");
    assert!(
        contains_any(&load, &["loaded", "load"]),
        "load should report success"
    );

    let r1 = kernel.execute("?- p X").expect("query failed");
    let r2 = kernel.execute(":next").expect("next failed");
    let mut seen = HashSet::new();
    for r in [&r1, &r2] {
        if r.contains("alpha") {
            seen.insert("alpha");
        }
        if r.contains("beta") {
            seen.insert("beta");
        }
    }
    assert!(
        seen.contains("alpha") && seen.contains("beta"),
        "streaming should return alpha and beta bindings"
    );

    let r3 = kernel.execute(":next").expect("next failed");
    assert!(
        contains_any(&r3, &["exhausted", "no more", "no answers"]),
        "stream exhaustion should be reported"
    );

    let _ = fs::remove_file(&path);
}

#[test]
fn kernel_projection_toggle_changes_visibility() {
    let path = write_temp_file("sggslog_kernel_proj", "\u{2203}X (p X)\n");
    let mut kernel = Kernel::new();
    let _ = kernel
        .execute(&format!(":load \"{}\"", path.to_string_lossy()))
        .expect("load should succeed");

    let r1 = kernel.execute("?- p X").expect("query failed");
    assert!(
        contains_any(
            &r1,
            &["no answers", "none", "no solution", "false", "exhausted"]
        ),
        "default projection should hide internal witnesses"
    );

    let _ = kernel
        .execute(":set projection allow_internal")
        .expect("set projection");
    let r2 = kernel.execute("?- p X").expect("query failed");
    assert!(
        !contains_any(
            &r2,
            &["no answers", "none", "no solution", "false", "exhausted"]
        ),
        "allow_internal should produce a visible binding"
    );

    let _ = fs::remove_file(&path);
}

#[test]
fn kernel_respects_resource_limit() {
    let mut kernel = Kernel::new();
    let _ = kernel.execute(":set timeout_ms 0").expect("set timeout_ms");
    let r = kernel.execute("?- p X").expect("query failed");
    assert!(
        contains_any(&r, &["resource", "limit", "timeout"]),
        "resource limit should be reported"
    );
}

#[test]
fn kernel_next_without_active_query_errors() {
    let mut kernel = Kernel::new();
    let err = kernel.execute(":next").expect_err("expected error");
    assert!(!err.message.is_empty());
}

#[test]
fn kernel_recursive_query_streams_incrementally() {
    let mut kernel = Kernel::new();
    let r1 = kernel.execute("(p a)").unwrap();
    assert!(!r1.is_empty(), "expected non-empty response, got {}", r1);
    let r2 = kernel.execute("(p X) -> (p (f X))").unwrap();
    assert!(!r2.is_empty(), "expected non-empty response, got {}", r2);

    let first = kernel.execute("?- (p X)").expect("query failed");
    assert!(
        !contains_any(&first, &["exhausted", "no more", "no answers", "false", "none"]),
        "expected streaming answer, got {}",
        first
    );
    assert!(first.contains("a"), "expected answer containing a, got {}", first);

    for _ in 0..2 {
        let next = kernel.execute(":next").expect("next failed");
        assert!(
            !contains_any(&next, &["exhausted", "no more", "no answers", "false", "none"]),
            "expected additional answers, got {}",
            next
        );
    }
}
