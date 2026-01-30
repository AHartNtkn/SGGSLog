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
        todo!("Lexer::new implementation")
    }

    /// Get the next token.
    pub fn next_token(&mut self) -> Result<Token, LexError> {
        todo!("Lexer::next_token implementation")
    }

    /// Peek at the next token without consuming it.
    pub fn peek_token(&mut self) -> Result<Token, LexError> {
        todo!("Lexer::peek_token implementation")
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
