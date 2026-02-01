//! Parser for SGGSLog syntax.

use super::ast::{Directive, ProjectionSetting, Setting, Statement};
use super::lexer::{LexError, Lexer, Token};
use crate::syntax::{Atom, Clause, Formula, Literal, Query, Term, Var};

/// Parse error with location information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
    pub line: usize,
    pub column: usize,
    pub span: Option<(usize, usize)>,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}: {}", self.line, self.column, self.message)
    }
}

impl std::error::Error for ParseError {}

impl From<LexError> for ParseError {
    fn from(e: LexError) -> Self {
        ParseError {
            message: e.message,
            line: e.line,
            column: e.column,
            span: None,
        }
    }
}

/// Parser state.
struct Parser<'a> {
    lexer: Lexer<'a>,
    current: Token,
    line: usize,
    column: usize,
    /// Whether a newline was skipped before the current token
    newline_before: bool,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Result<Self, ParseError> {
        let mut lexer = Lexer::new(input);
        let current = lexer.next_token()?;
        let newline_before = lexer.newline_before;
        Ok(Parser {
            lexer,
            current,
            line: 1,
            column: 1,
            newline_before,
        })
    }

    fn advance(&mut self) -> Result<Token, ParseError> {
        let old = std::mem::replace(&mut self.current, self.lexer.next_token()?);
        self.newline_before = self.lexer.newline_before;
        Ok(old)
    }

    fn expect(&mut self, expected: Token) -> Result<(), ParseError> {
        if self.current == expected {
            self.advance()?;
            Ok(())
        } else {
            Err(self.error(format!("expected {:?}, found {:?}", expected, self.current)))
        }
    }

    fn error(&self, message: String) -> ParseError {
        ParseError {
            message,
            line: self.line,
            column: self.column,
            span: None,
        }
    }
}

/// Parse a source file into statements.
pub fn parse_file(source: &str) -> Result<Vec<Statement>, ParseError> {
    let mut parser = Parser::new(source)?;
    let mut statements = Vec::new();

    while parser.current != Token::Eof {
        let stmt = parse_statement(&mut parser)?;
        statements.push(stmt);
    }

    Ok(statements)
}

/// Parse a single query.
pub fn parse_query(source: &str) -> Result<Query, ParseError> {
    let mut parser = Parser::new(source)?;

    // Expect ?-
    if parser.current != Token::Query {
        return Err(parser.error("expected '?-'".to_string()));
    }
    parser.advance()?;

    // Parse the conjunction of literals
    let literals = parse_query_conjunction(&mut parser)?;
    Ok(Query::new(literals))
}

fn parse_statement(parser: &mut Parser) -> Result<Statement, ParseError> {
    match &parser.current {
        Token::Colon => parse_directive(parser),
        Token::Query => parse_query_statement(parser),
        Token::Identifier(s) if s == "clause" => parse_clause_statement(parser),
        _ => parse_formula_statement(parser),
    }
}

fn parse_directive(parser: &mut Parser) -> Result<Statement, ParseError> {
    parser.expect(Token::Colon)?;

    match &parser.current {
        Token::Identifier(name) => {
            let name = name.clone();
            parser.advance()?;

            match name.as_str() {
                "load" => {
                    // Expect a string literal
                    match &parser.current {
                        Token::StringLit(path) => {
                            let path = path.clone();
                            parser.advance()?;
                            Ok(Statement::Directive(Directive::Load(path)))
                        }
                        _ => Err(parser.error("expected string literal after :load".to_string())),
                    }
                }
                "set" => {
                    // Parse setting key
                    let key = match &parser.current {
                        Token::Identifier(k) => {
                            let k = k.clone();
                            parser.advance()?;
                            k
                        }
                        _ => {
                            return Err(parser.error("expected setting name after :set".to_string()))
                        }
                    };

                    // Parse setting value
                    let value = match &parser.current {
                        Token::Identifier(v) => {
                            let v = v.clone();
                            parser.advance()?;
                            v
                        }
                        _ => {
                            return Err(parser
                                .error("expected setting value after setting name".to_string()))
                        }
                    };

                    let setting = match key.as_str() {
                        "timeout_ms" => {
                            let ms = value
                                .parse::<u64>()
                                .map_err(|_| parser.error("invalid timeout value".to_string()))?;
                            Setting::TimeoutMs(ms)
                        }
                        "projection" => match value.as_str() {
                            "only_user_symbols" => {
                                Setting::Projection(ProjectionSetting::OnlyUserSymbols)
                            }
                            "allow_internal" => {
                                Setting::Projection(ProjectionSetting::AllowInternal)
                            }
                            _ => Setting::Unknown { key, value },
                        },
                        _ => Setting::Unknown { key, value },
                    };

                    Ok(Statement::Directive(Directive::Set(setting)))
                }
                "next" => Ok(Statement::Directive(Directive::Next)),
                "quit" => Ok(Statement::Directive(Directive::Quit)),
                _ => Err(parser.error(format!("unknown directive: {}", name))),
            }
        }
        _ => Err(parser.error("expected directive name after ':'".to_string())),
    }
}

fn parse_query_statement(parser: &mut Parser) -> Result<Statement, ParseError> {
    parser.expect(Token::Query)?;
    let literals = parse_query_conjunction(parser)?;
    Ok(Statement::Query(Query::new(literals)))
}

fn parse_query_conjunction(parser: &mut Parser) -> Result<Vec<Literal>, ParseError> {
    let mut literals = Vec::new();

    // Parse first literal
    let first = parse_query_literal(parser)?;
    literals.push(first);

    // Parse additional literals connected by ∧ or &
    while matches!(parser.current, Token::And) {
        parser.advance()?;
        let lit = parse_query_literal(parser)?;
        literals.push(lit);
    }

    Ok(literals)
}

fn parse_query_literal(parser: &mut Parser) -> Result<Literal, ParseError> {
    // Check for negation
    let positive = if matches!(parser.current, Token::Not) {
        parser.advance()?;
        false
    } else {
        true
    };

    let atom = parse_atom(parser)?;
    if positive {
        Ok(Literal::positive(atom))
    } else {
        Ok(Literal::negative(atom))
    }
}

fn parse_clause_statement(parser: &mut Parser) -> Result<Statement, ParseError> {
    // Skip "clause" keyword
    parser.advance()?;

    let literals = parse_clause_literals(parser)?;
    Ok(Statement::Clause(Clause::new(literals)))
}

fn parse_clause_literals(parser: &mut Parser) -> Result<Vec<Literal>, ParseError> {
    let mut literals = Vec::new();

    // Parse first literal
    let first = parse_clause_literal(parser)?;
    literals.push(first);

    // Parse additional literals connected by ∨ or |
    while matches!(parser.current, Token::Or) {
        parser.advance()?;
        let lit = parse_clause_literal(parser)?;
        literals.push(lit);
    }

    Ok(literals)
}

fn parse_clause_literal(parser: &mut Parser) -> Result<Literal, ParseError> {
    // Check for negation
    let positive = if matches!(parser.current, Token::Not) {
        parser.advance()?;
        false
    } else {
        true
    };

    let atom = parse_atom(parser)?;
    if positive {
        Ok(Literal::positive(atom))
    } else {
        Ok(Literal::negative(atom))
    }
}

fn parse_formula_statement(parser: &mut Parser) -> Result<Statement, ParseError> {
    let formula = parse_formula(parser)?;
    Ok(Statement::Formula(formula))
}

fn parse_formula(parser: &mut Parser) -> Result<Formula, ParseError> {
    parse_implication(parser)
}

// Implication is right-associative: p -> q -> r = p -> (q -> r)
fn parse_implication(parser: &mut Parser) -> Result<Formula, ParseError> {
    let left = parse_disjunction(parser)?;

    if matches!(parser.current, Token::Implies) {
        parser.advance()?;
        let right = parse_implication(parser)?; // Right-associative
        Ok(Formula::implies(left, right))
    } else {
        Ok(left)
    }
}

// Disjunction: left-associative for simplicity, or treat as flat
fn parse_disjunction(parser: &mut Parser) -> Result<Formula, ParseError> {
    let mut left = parse_conjunction(parser)?;

    while matches!(parser.current, Token::Or) {
        parser.advance()?;
        let right = parse_conjunction(parser)?;
        left = Formula::or(left, right);
    }

    Ok(left)
}

// Conjunction binds tighter than disjunction
fn parse_conjunction(parser: &mut Parser) -> Result<Formula, ParseError> {
    let mut left = parse_unary(parser)?;

    while matches!(parser.current, Token::And) {
        parser.advance()?;
        let right = parse_unary(parser)?;
        left = Formula::and(left, right);
    }

    Ok(left)
}

fn parse_unary(parser: &mut Parser) -> Result<Formula, ParseError> {
    match &parser.current {
        Token::Not => {
            parser.advance()?;
            let inner = parse_unary(parser)?;
            Ok(Formula::negation(inner))
        }
        Token::Forall => {
            parser.advance()?;
            let var = parse_quantifier_var(parser)?;
            let body = parse_unary(parser)?;
            Ok(Formula::forall(var, body))
        }
        Token::Exists => {
            parser.advance()?;
            let var = parse_quantifier_var(parser)?;
            let body = parse_unary(parser)?;
            Ok(Formula::exists(var, body))
        }
        _ => parse_primary(parser),
    }
}

fn parse_quantifier_var(parser: &mut Parser) -> Result<Var, ParseError> {
    match &parser.current {
        Token::Variable(name) => {
            let name = name.clone();
            parser.advance()?;

            // Check for sort annotation
            if matches!(parser.current, Token::Colon) {
                parser.advance()?;
                match &parser.current {
                    Token::Identifier(sort) => {
                        let sort = sort.clone();
                        parser.advance()?;
                        Ok(Var::new_with_sort(name, sort))
                    }
                    _ => Err(parser.error("expected sort name after ':'".to_string())),
                }
            } else {
                Ok(Var::new(name))
            }
        }
        _ => Err(parser.error("expected variable after quantifier".to_string())),
    }
}

fn parse_primary(parser: &mut Parser) -> Result<Formula, ParseError> {
    if matches!(parser.current, Token::LParen) {
        parser.advance()?;

        // Always parse as a formula inside parentheses
        // This handles both (pred args...) and (formula ∧ formula)
        let inner = parse_formula(parser)?;
        parser.expect(Token::RParen)?;
        Ok(inner)
    } else {
        // Atom without parens: pred or pred arg1 arg2 ...
        let atom = parse_atom(parser)?;
        Ok(Formula::atom(atom))
    }
}

fn parse_atom(parser: &mut Parser) -> Result<Atom, ParseError> {
    match &parser.current {
        Token::Identifier(pred) => {
            let pred = pred.clone();
            parser.advance()?;

            // Collect arguments (terms that follow immediately)
            let args = parse_atom_args(parser)?;
            Ok(Atom::new(pred, args))
        }
        Token::LParen => {
            parser.advance()?;
            let atom = parse_atom_after_lparen(parser)?;
            parser.expect(Token::RParen)?;
            Ok(atom)
        }
        _ => Err(parser.error("expected predicate name or '('".to_string())),
    }
}

fn parse_atom_after_lparen(parser: &mut Parser) -> Result<Atom, ParseError> {
    match &parser.current {
        Token::Identifier(pred) => {
            let pred = pred.clone();
            parser.advance()?;

            // Collect arguments
            let args = parse_atom_args(parser)?;
            Ok(Atom::new(pred, args))
        }
        _ => Err(parser.error("expected predicate name after '('".to_string())),
    }
}

fn parse_atom_args(parser: &mut Parser) -> Result<Vec<Term>, ParseError> {
    let mut args = Vec::new();

    // Collect terms until we hit something that isn't a term start
    // or we hit a newline (which separates statements)
    while can_start_term_arg(parser) {
        let term = parse_term(parser)?;
        args.push(term);
    }

    Ok(args)
}

fn can_start_term_arg(parser: &Parser) -> bool {
    // If there's a newline before this token and it's an identifier,
    // it's likely a new statement, not an argument
    if parser.newline_before && matches!(parser.current, Token::Identifier(_)) {
        return false;
    }
    matches!(
        parser.current,
        Token::Identifier(_) | Token::Variable(_) | Token::LParen
    )
}

fn parse_term(parser: &mut Parser) -> Result<Term, ParseError> {
    match &parser.current {
        Token::Variable(name) => {
            let name = name.clone();
            parser.advance()?;

            // Check for sort annotation
            if matches!(parser.current, Token::Colon) {
                parser.advance()?;
                match &parser.current {
                    Token::Identifier(sort) => {
                        let sort = sort.clone();
                        parser.advance()?;
                        Ok(Term::Var(Var::new_with_sort(name, sort)))
                    }
                    _ => Err(parser.error("expected sort name after ':'".to_string())),
                }
            } else {
                Ok(Term::var(name))
            }
        }
        Token::Identifier(name) => {
            let name = name.clone();
            parser.advance()?;

            // Check for sort annotation on constant
            if matches!(parser.current, Token::Colon) {
                parser.advance()?;
                match &parser.current {
                    Token::Identifier(sort) => {
                        let sort = sort.clone();
                        parser.advance()?;
                        Ok(Term::constant_with_sort(name, sort))
                    }
                    _ => Err(parser.error("expected sort name after ':'".to_string())),
                }
            } else {
                Ok(Term::constant(name))
            }
        }
        Token::LParen => {
            parser.advance()?;

            // Function application: (f args...)
            match &parser.current {
                Token::Identifier(fn_name) => {
                    let fn_name = fn_name.clone();
                    parser.advance()?;

                    // Check for sort annotation on function
                    let sort = if matches!(parser.current, Token::Colon) {
                        parser.advance()?;
                        match &parser.current {
                            Token::Identifier(s) => {
                                let s = s.clone();
                                parser.advance()?;
                                Some(s)
                            }
                            _ => {
                                return Err(parser.error("expected sort name after ':'".to_string()))
                            }
                        }
                    } else {
                        None
                    };

                    // Collect arguments
                    let mut args = Vec::new();
                    while parser.current != Token::RParen {
                        let arg = parse_term(parser)?;
                        args.push(arg);
                    }
                    parser.expect(Token::RParen)?;

                    if let Some(s) = sort {
                        Ok(Term::app_with_sort(fn_name, s, args))
                    } else {
                        Ok(Term::app(fn_name, args))
                    }
                }
                _ => Err(parser.error("expected function name after '('".to_string())),
            }
        }
        _ => Err(parser.error("expected term".to_string())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_atom() {
        let stmts = parse_file("p").unwrap();
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Statement::Formula(Formula::Atom(atom)) => {
                assert_eq!(atom.predicate, "p");
                assert!(atom.args.is_empty());
            }
            _ => panic!("expected atom"),
        }
    }

    #[test]
    fn test_parse_atom_with_args() {
        let stmts = parse_file("p a b").unwrap();
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Statement::Formula(Formula::Atom(atom)) => {
                assert_eq!(atom.predicate, "p");
                assert_eq!(atom.args.len(), 2);
            }
            _ => panic!("expected atom"),
        }
    }

    #[test]
    fn test_parse_negation() {
        let stmts = parse_file("~p").unwrap();
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Statement::Formula(Formula::Not(inner)) => match inner.as_ref() {
                Formula::Atom(atom) => assert_eq!(atom.predicate, "p"),
                _ => panic!("expected atom inside Not"),
            },
            _ => panic!("expected Not"),
        }
    }

    #[test]
    fn test_parse_conjunction() {
        let stmts = parse_file("p & q").unwrap();
        assert_eq!(stmts.len(), 1);
        assert!(matches!(&stmts[0], Statement::Formula(Formula::And(_, _))));
    }

    #[test]
    fn test_parse_disjunction() {
        let stmts = parse_file("p | q").unwrap();
        assert_eq!(stmts.len(), 1);
        assert!(matches!(&stmts[0], Statement::Formula(Formula::Or(_, _))));
    }

    #[test]
    fn test_parse_implication() {
        let stmts = parse_file("p -> q").unwrap();
        assert_eq!(stmts.len(), 1);
        assert!(matches!(
            &stmts[0],
            Statement::Formula(Formula::Implies(_, _))
        ));
    }

    #[test]
    fn test_parse_forall() {
        let stmts = parse_file("∀X (p X)").unwrap();
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Statement::Formula(Formula::Forall(var, _)) => {
                assert_eq!(var.name(), "X");
            }
            _ => panic!("expected Forall"),
        }
    }

    #[test]
    fn test_parse_exists() {
        let stmts = parse_file("∃X (p X)").unwrap();
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Statement::Formula(Formula::Exists(var, _)) => {
                assert_eq!(var.name(), "X");
            }
            _ => panic!("expected Exists"),
        }
    }

    #[test]
    fn test_parse_sorted_var() {
        let stmts = parse_file("∀X:s1 (p X)").unwrap();
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Statement::Formula(Formula::Forall(var, _)) => {
                assert_eq!(var.name(), "X");
                assert_eq!(var.sort(), Some("s1"));
            }
            _ => panic!("expected Forall"),
        }
    }
}
