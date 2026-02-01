//! REPL implementation.

use crate::parser::{parse_file, Setting, Statement};
use crate::session::{DirectiveResult, ExecResult, Session, SessionError};
use crate::sggs::QueryResult;
use std::io::{self, BufRead, Write};

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

impl From<SessionError> for ReplError {
    fn from(e: SessionError) -> Self {
        ReplError { message: e.message }
    }
}

/// Interactive REPL for SGGSLog.
pub struct Repl {
    session: Session,
}

impl Repl {
    /// Create a new REPL.
    pub fn new() -> Self {
        Repl {
            session: Session::new(),
        }
    }

    /// Load a file into the REPL.
    pub fn load_file(&mut self, path: &str) -> Result<(), ReplError> {
        self.session
            .load_file(path)
            .map_err(|e| ReplError { message: e.message })?;
        Ok(())
    }

    /// Process a line of input.
    pub fn process_line(&mut self, line: &str) -> Result<String, ReplError> {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            return Ok(String::new());
        }

        // Check for REPL commands (start with :)
        if line.starts_with(':') {
            return self.process_command(line);
        }

        // Parse and execute the statement
        let stmts = parse_file(line).map_err(|e| ReplError {
            message: format!("Parse error: {}", e),
        })?;

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

    /// Process a REPL command (starts with :).
    fn process_command(&mut self, line: &str) -> Result<String, ReplError> {
        let parts: Vec<&str> = line[1..].splitn(2, ' ').collect();
        let cmd = parts[0].trim();
        let args = parts.get(1).map(|s| s.trim()).unwrap_or("");

        match cmd {
            "quit" | "q" | "exit" => Ok("Goodbye!".to_string()),
            "next" | "n" => {
                let result = self.session.next_answer()?;
                Ok(format_query_result(&result))
            }
            "set" => self.process_set_directive(args),
            "load" | "l" => {
                if args.is_empty() {
                    return Err(ReplError {
                        message: "Usage: :load <filename>".to_string(),
                    });
                }
                let result = self.session.load_file(args)?;
                Ok(format_directive_result(&result))
            }
            _ => Err(ReplError {
                message: format!("Unknown command: {}", cmd),
            }),
        }
    }

    /// Process :set directive.
    fn process_set_directive(&mut self, args: &str) -> Result<String, ReplError> {
        let parts: Vec<&str> = args.splitn(2, ' ').collect();
        if parts.len() < 2 {
            return Err(ReplError {
                message: "Usage: :set <key> <value>".to_string(),
            });
        }
        let key = parts[0].trim();
        let value = parts[1].trim();

        let setting = match key {
            "timeout_ms" | "timeout" => {
                let ms = value.parse::<u64>().map_err(|_| ReplError {
                    message: format!("Invalid timeout value: {}", value),
                })?;
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
                        return Err(ReplError {
                            message: format!("Unknown projection mode: {}", value),
                        });
                    }
                };
                Setting::Projection(proj)
            }
            _ => Setting::Unknown {
                key: key.to_string(),
                value: value.to_string(),
            },
        };

        let result = self.session.apply_setting(setting)?;
        Ok(format_directive_result(&result))
    }

    /// Execute a parsed statement.
    fn execute_statement(&mut self, stmt: Statement) -> Result<String, ReplError> {
        let result = self.session.execute_statement(stmt)?;
        Ok(format_exec_result(&result))
    }

    /// Run the REPL interactively.
    pub fn run(&mut self) -> Result<(), ReplError> {
        let stdin = io::stdin();
        let mut stdout = io::stdout();

        println!("SGGSLog REPL");
        println!("Type :help for help, :quit to exit.");

        loop {
            print!("?- ");
            stdout.flush().map_err(|e| ReplError {
                message: e.to_string(),
            })?;

            let mut line = String::new();
            match stdin.lock().read_line(&mut line) {
                Ok(0) => break, // EOF
                Ok(_) => {}
                Err(e) => {
                    return Err(ReplError {
                        message: e.to_string(),
                    })
                }
            }

            let line = line.trim();
            if line == ":quit" || line == ":q" || line == ":exit" {
                println!("Goodbye!");
                break;
            }

            match self.process_line(line) {
                Ok(response) => {
                    if !response.is_empty() {
                        println!("{}", response);
                    }
                }
                Err(e) => {
                    eprintln!("Error: {}", e);
                }
            }
        }

        Ok(())
    }
}

/// Format a query result as a string.
fn format_query_result(result: &QueryResult) -> String {
    match result {
        QueryResult::Answer(subst) => {
            if subst.is_empty() {
                "true.".to_string()
            } else {
                let bindings: Vec<String> = subst
                    .bindings()
                    .map(|(v, t)| format!("{} = {}", v.name(), t))
                    .collect();
                bindings.join(", ").to_string()
            }
        }
        QueryResult::Exhausted => "no (more) answers.".to_string(),
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
        let err = repl
            .process_line(":next")
            .expect_err("expected error on :next");
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
