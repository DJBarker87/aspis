#![allow(dead_code)]

// Compile the production files in a Solana-free harness so Charon can start
// from the prepared-claim function without translating the program entrypoint.
// The `#[path]` modules are the repository files themselves, not copied code.
#[path = "../../../../programs/aspis-verifier/src/v5_private_openings.rs"]
pub mod private_openings;

#[path = "../../../../programs/aspis-verifier/src/v5_fri_checks.rs"]
pub mod fri_checks;
