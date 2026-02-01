//! SGGSLog: A minimal logic programming language using SGGS inference
//!
//! This crate implements Semantically Guided Goal-Sensitive Reasoning (SGGS)
//! for first-order logic theorem proving.

#![allow(clippy::module_inception)]
#![allow(clippy::too_many_arguments)]

pub mod constraint;
pub mod jupyter;
pub mod normalize;
pub mod parser;
pub mod repl;
pub mod session;
pub mod sggs;
pub mod syntax;
pub mod theory;
pub mod unify;

#[cfg(test)]
mod tests;
