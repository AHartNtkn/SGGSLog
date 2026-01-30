//! Jupyter kernel implementation.

use crate::session::Session;

/// Jupyter kernel for SGGSLog.
pub struct Kernel {
    session: Session,
}

impl Kernel {
    /// Create a new kernel.
    pub fn new() -> Self {
        todo!("Kernel::new implementation")
    }

    /// Execute a cell.
    pub fn execute(&mut self, _code: &str) -> Result<String, KernelError> {
        todo!("Kernel::execute implementation")
    }
}

impl Default for Kernel {
    fn default() -> Self {
        Self::new()
    }
}

/// Kernel error.
#[derive(Debug)]
pub struct KernelError {
    pub message: String,
}

impl std::fmt::Display for KernelError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for KernelError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_kernel_new_constructs() {
        let _ = Kernel::new();
    }

    #[test]
    fn test_kernel_default_constructs() {
        let _ = Kernel::default();
    }

    #[test]
    fn test_kernel_execute_clause_and_query() {
        let mut k = Kernel::new();
        assert_eq!(k.execute("p").unwrap(), "ok");
        assert_eq!(k.execute("?- p").unwrap(), "yes");
    }

    #[test]
    fn test_kernel_execute_multiple_lines() {
        let mut k = Kernel::new();
        let code = "p\nq\n?- p";
        assert_eq!(k.execute(code).unwrap(), "yes");
    }

    #[test]
    fn test_kernel_execute_parse_error() {
        let mut k = Kernel::new();
        let err = k.execute("p ∧").expect_err("expected parse error");
        assert!(!err.message.is_empty());
    }

    #[test]
    fn test_kernel_execute_answers_and_no() {
        let mut k = Kernel::new();
        assert_eq!(k.execute("(p a)").unwrap(), "ok");
        assert_eq!(k.execute("?- (p b)").unwrap(), "no");
        assert_eq!(k.execute("?- (p X)").unwrap(), "answers: {X=a}");
    }
}
