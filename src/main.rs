//! SGGSLog CLI - A logic programming language using SGGS inference.

use sggslog::repl::Repl;

fn main() {
    println!("SGGSLog - Semantically Guided Goal-Sensitive Logic Programming");
    println!("Type :help for help, :quit to exit.\n");

    let mut repl = Repl::new();
    if let Err(e) = repl.run() {
        eprintln!("Error: {}", e);
        std::process::exit(1);
    }
}
