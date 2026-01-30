//! Lexer for SGGSLog syntax.

/// Token types for SGGSLog syntax.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    // Identifiers
    Identifier(String), // lowercase: constants, predicates, functors
    Variable(String),   // uppercase: variables

    // Delimiters
    LParen, // (
    RParen, // )

    // Logic operators (Unicode)
    Not,     // ¬
    And,     // ∧
    Or,      // ∨
    Implies, // →
    Forall,  // ∀
    Exists,  // ∃

    // Query
    Query, // ?-

    // Directive
    Colon, // :

    // String literal
    StringLit(String),

    // End of input
    Eof,
}

/// Lexer state.
pub struct Lexer<'a> {
    input: &'a str,
    position: usize,
    line: usize,
    column: usize,
}

impl<'a> Lexer<'a> {
    /// Create a new lexer for the given input.
    pub fn new(input: &'a str) -> Self {
        Lexer {
            input,
            position: 0,
            line: 1,
            column: 1,
        }
    }

    /// Get the next token.
    pub fn next_token(&mut self) -> Result<Token, LexError> {
        self.skip_whitespace_and_comments();

        if self.position >= self.input.len() {
            return Ok(Token::Eof);
        }

        let remaining = &self.input[self.position..];
        let ch = remaining.chars().next().unwrap();

        // Single-character tokens
        match ch {
            '(' => {
                self.advance(1);
                return Ok(Token::LParen);
            }
            ')' => {
                self.advance(1);
                return Ok(Token::RParen);
            }
            ':' => {
                self.advance(1);
                return Ok(Token::Colon);
            }
            // Unicode operators
            '¬' => {
                self.advance(ch.len_utf8());
                return Ok(Token::Not);
            }
            '∧' => {
                self.advance(ch.len_utf8());
                return Ok(Token::And);
            }
            '∨' => {
                self.advance(ch.len_utf8());
                return Ok(Token::Or);
            }
            '→' => {
                self.advance(ch.len_utf8());
                return Ok(Token::Implies);
            }
            '∀' => {
                self.advance(ch.len_utf8());
                return Ok(Token::Forall);
            }
            '∃' => {
                self.advance(ch.len_utf8());
                return Ok(Token::Exists);
            }
            // ASCII operators
            '~' => {
                self.advance(1);
                return Ok(Token::Not);
            }
            '&' => {
                self.advance(1);
                return Ok(Token::And);
            }
            '|' => {
                self.advance(1);
                return Ok(Token::Or);
            }
            '-' if remaining.starts_with("->") => {
                self.advance(2);
                return Ok(Token::Implies);
            }
            '?' if remaining.starts_with("?-") => {
                self.advance(2);
                return Ok(Token::Query);
            }
            '"' => {
                return self.lex_string();
            }
            _ => {}
        }

        // Identifiers, variables, and Skolem names
        if ch.is_ascii_lowercase() || ch == '$' {
            return Ok(self.lex_identifier());
        }

        if ch.is_ascii_uppercase() {
            return Ok(self.lex_variable());
        }

        Err(LexError {
            message: format!("unexpected character: '{}'", ch),
            line: self.line,
            column: self.column,
        })
    }

    /// Peek at the next token without consuming it.
    pub fn peek_token(&mut self) -> Result<Token, LexError> {
        let saved_position = self.position;
        let saved_line = self.line;
        let saved_column = self.column;

        let token = self.next_token()?;

        self.position = saved_position;
        self.line = saved_line;
        self.column = saved_column;

        Ok(token)
    }

    fn advance(&mut self, bytes: usize) {
        let consumed = &self.input[self.position..self.position + bytes];
        for ch in consumed.chars() {
            if ch == '\n' {
                self.line += 1;
                self.column = 1;
            } else {
                self.column += 1;
            }
        }
        self.position += bytes;
    }

    fn skip_whitespace_and_comments(&mut self) {
        while self.position < self.input.len() {
            let remaining = &self.input[self.position..];
            let ch = remaining.chars().next().unwrap();

            if ch.is_whitespace() {
                self.advance(ch.len_utf8());
            } else if remaining.starts_with("//") {
                // Skip to end of line
                while self.position < self.input.len() {
                    let c = self.input[self.position..].chars().next().unwrap();
                    self.advance(c.len_utf8());
                    if c == '\n' {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }

    fn lex_identifier(&mut self) -> Token {
        let start = self.position;

        while self.position < self.input.len() {
            let ch = self.input[self.position..].chars().next().unwrap();
            if ch.is_ascii_alphanumeric() || ch == '_' || ch == '$' {
                self.advance(ch.len_utf8());
            } else {
                break;
            }
        }

        let name = self.input[start..self.position].to_string();
        Token::Identifier(name)
    }

    fn lex_variable(&mut self) -> Token {
        let start = self.position;

        while self.position < self.input.len() {
            let ch = self.input[self.position..].chars().next().unwrap();
            if ch.is_ascii_alphanumeric() || ch == '_' {
                self.advance(ch.len_utf8());
            } else {
                break;
            }
        }

        let name = self.input[start..self.position].to_string();
        Token::Variable(name)
    }

    fn lex_string(&mut self) -> Result<Token, LexError> {
        // Skip opening quote
        self.advance(1);
        let start = self.position;

        while self.position < self.input.len() {
            let ch = self.input[self.position..].chars().next().unwrap();
            if ch == '"' {
                let content = self.input[start..self.position].to_string();
                self.advance(1); // Skip closing quote
                return Ok(Token::StringLit(content));
            } else if ch == '\n' {
                return Err(LexError {
                    message: "unterminated string literal".to_string(),
                    line: self.line,
                    column: self.column,
                });
            } else {
                self.advance(ch.len_utf8());
            }
        }

        Err(LexError {
            message: "unterminated string literal".to_string(),
            line: self.line,
            column: self.column,
        })
    }
}

/// Lexer error.
#[derive(Debug, Clone)]
pub struct LexError {
    pub message: String,
    pub line: usize,
    pub column: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lex_ascii_and_unicode_ops() {
        let mut lex = Lexer::new("~p ∧ q | r -> s");
        let tokens = [
            Token::Not,
            Token::Identifier("p".to_string()),
            Token::And,
            Token::Identifier("q".to_string()),
            Token::Or,
            Token::Identifier("r".to_string()),
            Token::Implies,
            Token::Identifier("s".to_string()),
        ];
        for expected in tokens {
            let tok = lex.next_token().expect("token");
            assert_eq!(tok, expected);
        }
    }

    #[test]
    fn test_lex_ascii_and_operator() {
        let mut lex = Lexer::new("p & q");
        assert_eq!(
            lex.next_token().unwrap(),
            Token::Identifier("p".to_string())
        );
        assert_eq!(lex.next_token().unwrap(), Token::And);
        assert_eq!(
            lex.next_token().unwrap(),
            Token::Identifier("q".to_string())
        );
    }

    #[test]
    fn test_lex_query_token() {
        let mut lex = Lexer::new("?- (p a)");
        assert_eq!(lex.next_token().unwrap(), Token::Query);
        assert_eq!(lex.next_token().unwrap(), Token::LParen);
    }

    #[test]
    fn test_lex_comments_are_skipped() {
        let mut lex = Lexer::new("// comment\np");
        assert_eq!(
            lex.next_token().unwrap(),
            Token::Identifier("p".to_string())
        );
    }

    #[test]
    fn test_lex_sorted_identifier_parts() {
        let mut lex = Lexer::new("X:s1");
        assert_eq!(lex.next_token().unwrap(), Token::Variable("X".to_string()));
        assert_eq!(lex.next_token().unwrap(), Token::Colon);
        assert_eq!(
            lex.next_token().unwrap(),
            Token::Identifier("s1".to_string())
        );
    }

    #[test]
    fn test_lex_skolem_identifier() {
        // Skolem names may start with '$' and should be lexed as identifiers.
        let mut lex = Lexer::new("$sk0");
        assert_eq!(
            lex.next_token().unwrap(),
            Token::Identifier("$sk0".to_string())
        );
    }
}
