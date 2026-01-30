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
}
