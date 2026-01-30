//! SGGSLog: A minimal logic programming language using SGGS inference
//!
//! This crate implements Semantically Guided Goal-Sensitive Reasoning (SGGS)
//! for first-order logic theorem proving.

pub mod syntax;
pub mod unify;
pub mod constraint;
pub mod sggs;
pub mod parser;
pub mod theory;
pub mod repl;
pub mod jupyter;
pub mod session;

#[cfg(test)]
mod tests;
