//! REPL implementation.

use crate::session::Session;

/// REPL error.
#[derive(Debug)]
pub struct ReplError {
    pub message: String,
}

impl std::fmt::Display for ReplError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for ReplError {}

/// Interactive REPL for SGGSLog.
pub struct Repl {
    session: Session,
}

impl Repl {
    /// Create a new REPL.
    pub fn new() -> Self {
        todo!("Repl::new implementation")
    }

    /// Load a file into the REPL.
    pub fn load_file(&mut self, _path: &str) -> Result<(), ReplError> {
        todo!("Repl::load_file implementation")
    }

    /// Process a line of input.
    pub fn process_line(&mut self, _line: &str) -> Result<String, ReplError> {
        todo!("Repl::process_line implementation")
    }

    /// Run the REPL interactively.
    pub fn run(&mut self) -> Result<(), ReplError> {
        todo!("Repl::run implementation")
    }
}

impl Default for Repl {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn contains_any(haystack: &str, needles: &[&str]) -> bool {
        let hay = haystack.to_ascii_lowercase();
        needles
            .iter()
            .any(|n| hay.contains(&n.to_ascii_lowercase()))
    }

    #[test]
    fn test_repl_new_constructs() {
        let _ = Repl::new();
    }

    #[test]
    fn test_repl_default_constructs() {
        let _ = Repl::default();
    }

    #[test]
    fn test_repl_process_line_clause_and_query() {
        let mut repl = Repl::new();
        let r1 = repl.process_line("p").unwrap();
        assert!(!r1.is_empty(), "expected non-empty response, got {}", r1);
        let r2 = repl.process_line("?- p").unwrap();
        assert!(
            !r2.is_empty(),
            "expected non-empty query response, got {}",
            r2
        );
        let r3 = repl.process_line(":next").unwrap();
        assert!(
            !r3.is_empty(),
            "expected non-empty next-answer response, got {}",
            r3
        );
    }

    #[test]
    fn test_repl_process_line_directive() {
        let mut repl = Repl::new();
        let r = repl.process_line(":set timeout_ms 10").unwrap();
        assert!(
            r.contains("timeout_ms") && r.contains("10"),
            "expected directive acknowledgement, got {}",
            r
        );
    }

    #[test]
    fn test_repl_process_line_parse_error() {
        let mut repl = Repl::new();
        let err = repl.process_line("p ∧").expect_err("expected parse error");
        assert!(!err.message.is_empty());
    }

    #[test]
    fn test_repl_query_no_and_answers() {
        let mut repl = Repl::new();
        let r1 = repl.process_line("(p a)").unwrap();
        assert!(!r1.is_empty(), "expected non-empty response, got {}", r1);
        let r2 = repl.process_line("?- (p b)").unwrap();
        assert!(
            !r2.is_empty(),
            "expected non-empty no-answer response, got {}",
            r2
        );
        let r3 = repl.process_line("?- (p X)").unwrap();
        assert!(
            r3.contains("a"),
            "expected an answer containing a, got {}",
            r3
        );
        let r4 = repl.process_line(":next").unwrap();
        assert!(
            !r4.is_empty(),
            "expected non-empty next-answer response, got {}",
            r4
        );
    }

    #[test]
    fn test_repl_next_without_query_errors() {
        let mut repl = Repl::new();
        let err = repl.process_line(":next").expect_err("expected error on :next");
        assert!(!err.message.is_empty());
    }

    #[test]
    fn test_repl_recursive_query_streams_incrementally() {
        let mut repl = Repl::new();
        let r1 = repl.process_line("(p a)").unwrap();
        assert!(!r1.is_empty(), "expected non-empty response, got {}", r1);
        let r2 = repl.process_line("(p X) -> (p (f X))").unwrap();
        assert!(!r2.is_empty(), "expected non-empty response, got {}", r2);

        let first = repl.process_line("?- (p X)").unwrap();
        assert!(
            !contains_any(&first, &["exhausted", "no more", "no answers", "false", "none"]),
            "expected streaming answer, got {}",
            first
        );
        assert!(
            first.contains("a"),
            "expected answer containing a, got {}",
            first
        );

        for _ in 0..2 {
            let next = repl.process_line(":next").unwrap();
            assert!(
                !contains_any(&next, &["exhausted", "no more", "no answers", "false", "none"]),
                "expected additional answers, got {}",
                next
            );
        }
    }
}
