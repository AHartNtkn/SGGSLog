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
        assert_eq!(repl.process_line("p").unwrap(), "ok");
        assert_eq!(repl.process_line("?- p").unwrap(), "yes");
    }

    #[test]
    fn test_repl_process_line_directive() {
        let mut repl = Repl::new();
        assert_eq!(
            repl.process_line(":set max_steps 10").unwrap(),
            "set max_steps=10"
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
        assert_eq!(repl.process_line("(p a)").unwrap(), "ok");
        assert_eq!(repl.process_line("?- (p b)").unwrap(), "no");
        assert_eq!(repl.process_line("?- (p X)").unwrap(), "answers: {X=a}");
    }
}
