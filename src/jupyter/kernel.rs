//! Jupyter kernel implementation.

use crate::parser::{parse_file, Setting, Statement};
use crate::session::{DirectiveResult, ExecResult, Session, SessionError};
use crate::sggs::QueryResult;

/// Jupyter kernel for SGGSLog.
pub struct Kernel {
    session: Session,
}

impl Kernel {
    /// Create a new kernel.
    pub fn new() -> Self {
        Kernel {
            session: Session::new(),
        }
    }

    /// Execute a cell containing one or more statements.
    pub fn execute(&mut self, code: &str) -> Result<String, KernelError> {
        let code = code.trim();
        if code.is_empty() || code.starts_with('#') {
            return Ok(String::new());
        }

        // Check for kernel commands (start with :)
        if code.starts_with(':') {
            return self.process_command(code);
        }

        // Parse and execute the statements
        let stmts = parse_file(code)
            .map_err(|e| KernelError { message: format!("Parse error: {}", e) })?;

        if stmts.is_empty() {
            return Ok(String::new());
        }

        // Execute all statements, collect results
        let mut results = Vec::new();
        for stmt in stmts {
            let result = self.execute_statement(stmt)?;
            if !result.is_empty() {
                results.push(result);
            }
        }
        Ok(results.join("\n"))
    }

    /// Process a kernel command (starts with :).
    fn process_command(&mut self, line: &str) -> Result<String, KernelError> {
        let parts: Vec<&str> = line[1..].splitn(2, ' ').collect();
        let cmd = parts[0].trim();
        let args = parts.get(1).map(|s| s.trim()).unwrap_or("");

        match cmd {
            "next" | "n" => {
                let result = self.session.next_answer()?;
                Ok(format_query_result(&result))
            }
            "set" => {
                self.process_set_directive(args)
            }
            "load" | "l" => {
                if args.is_empty() {
                    return Err(KernelError { message: "Usage: :load <filename>".to_string() });
                }
                // Remove quotes if present
                let path = args.trim_matches('"').trim_matches('\'');
                let result = self.session.load_file(path)?;
                Ok(format_directive_result(&result))
            }
            _ => {
                Err(KernelError { message: format!("Unknown command: {}", cmd) })
            }
        }
    }

    /// Process :set directive.
    fn process_set_directive(&mut self, args: &str) -> Result<String, KernelError> {
        let parts: Vec<&str> = args.splitn(2, ' ').collect();
        if parts.len() < 2 {
            return Err(KernelError { message: "Usage: :set <key> <value>".to_string() });
        }
        let key = parts[0].trim();
        let value = parts[1].trim();

        let setting = match key {
            "timeout_ms" | "timeout" => {
                let ms = value.parse::<u64>()
                    .map_err(|_| KernelError { message: format!("Invalid timeout value: {}", value) })?;
                Setting::TimeoutMs(ms)
            }
            "projection" => {
                let proj = match value {
                    "user" | "only_user" | "user_symbols" => {
                        crate::parser::ProjectionSetting::OnlyUserSymbols
                    }
                    "internal" | "allow_internal" => {
                        crate::parser::ProjectionSetting::AllowInternal
                    }
                    _ => {
                        return Err(KernelError {
                            message: format!("Unknown projection mode: {}", value),
                        });
                    }
                };
                Setting::Projection(proj)
            }
            _ => Setting::Unknown { key: key.to_string(), value: value.to_string() },
        };

        let result = self.session.apply_setting(setting)?;
        Ok(format_directive_result(&result))
    }

    /// Execute a parsed statement.
    fn execute_statement(&mut self, stmt: Statement) -> Result<String, KernelError> {
        let result = self.session.execute_statement(stmt)?;
        Ok(format_exec_result(&result))
    }
}

impl From<SessionError> for KernelError {
    fn from(e: SessionError) -> Self {
        KernelError { message: e.message }
    }
}

/// Format a query result as a string.
fn format_query_result(result: &QueryResult) -> String {
    match result {
        QueryResult::Answer(subst) => {
            if subst.is_empty() {
                "true.".to_string()
            } else {
                let bindings: Vec<String> = subst.bindings()
                    .map(|(v, t)| format!("{} = {}", v.name(), t))
                    .collect();
                format!("{}", bindings.join(", "))
            }
        }
        QueryResult::Exhausted => "no answers.".to_string(),
        QueryResult::Timeout => "timeout.".to_string(),
    }
}

/// Format a directive result as a string.
fn format_directive_result(result: &DirectiveResult) -> String {
    match result {
        DirectiveResult::Loaded { path, clauses } => {
            format!("Loaded {} clauses from {}", clauses, path)
        }
        DirectiveResult::Set(setting) => match setting {
            Setting::TimeoutMs(ms) => format!("Set timeout_ms = {}", ms),
            Setting::Projection(proj) => format!("Set projection = {:?}", proj),
            Setting::Unknown { key, value } => format!("Set {} = {}", key, value),
        },
    }
}

/// Format an execution result as a string.
fn format_exec_result(result: &ExecResult) -> String {
    match result {
        ExecResult::ClauseAdded => "ok.".to_string(),
        ExecResult::QueryResult(qr) => format_query_result(qr),
        ExecResult::DirectiveApplied(dr) => format_directive_result(dr),
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
        let r1 = k.execute("p").unwrap();
        assert!(!r1.is_empty(), "expected non-empty response, got {}", r1);
        let r2 = k.execute("?- p").unwrap();
        assert!(
            !r2.is_empty(),
            "expected non-empty query response, got {}",
            r2
        );
        let r3 = k.execute(":next").unwrap();
        assert!(
            !r3.is_empty(),
            "expected non-empty next-answer response, got {}",
            r3
        );
    }

    #[test]
    fn test_kernel_execute_multiple_lines() {
        let mut k = Kernel::new();
        let code = "p\nq\n?- p";
        let r = k.execute(code).unwrap();
        assert!(
            !r.is_empty(),
            "expected non-empty query response, got {}",
            r
        );
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
        let r1 = k.execute("(p a)").unwrap();
        assert!(!r1.is_empty(), "expected non-empty response, got {}", r1);
        let r2 = k.execute("?- (p b)").unwrap();
        assert!(
            !r2.is_empty(),
            "expected non-empty no-answer response, got {}",
            r2
        );
        let r3 = k.execute("?- (p X)").unwrap();
        assert!(
            r3.contains("a"),
            "expected an answer containing a, got {}",
            r3
        );
        let r4 = k.execute(":next").unwrap();
        assert!(
            !r4.is_empty(),
            "expected non-empty next-answer response, got {}",
            r4
        );
    }

    #[test]
    fn test_kernel_execute_next_without_query_errors() {
        let mut k = Kernel::new();
        let err = k.execute(":next").expect_err("expected error on :next");
        assert!(!err.message.is_empty());
    }

    #[test]
    fn test_kernel_new_query_resets_stream() {
        let mut k = Kernel::new();
        k.execute("p a").unwrap();
        let _ = k.execute("?- p X").unwrap();
        let _ = k.execute(":next").unwrap();
        let r2 = k.execute("?- p X").unwrap();
        assert!(
            r2.contains("a"),
            "expected new query to return an answer, got {}",
            r2
        );
    }
}
