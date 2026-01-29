//! REPL implementation.

use crate::theory::Theory;
use crate::sggs::DerivationConfig;

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
    theory: Theory,
    config: DerivationConfig,
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
