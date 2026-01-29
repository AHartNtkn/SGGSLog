//! Jupyter kernel implementation.

use crate::theory::Theory;
use crate::sggs::DerivationConfig;

/// Jupyter kernel for SGGSLog.
pub struct Kernel {
    theory: Theory,
    config: DerivationConfig,
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
