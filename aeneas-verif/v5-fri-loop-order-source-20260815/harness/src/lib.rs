#![allow(dead_code)]

// Compile the production files in a Solana-free harness.  The replay script
// applies the checked-in diagnostic patch only to a temporary source copy.
#[path = "../../../../programs/aspis-verifier/src/v5_private_openings.rs"]
pub mod private_openings;

#[path = "../../../../programs/aspis-verifier/src/v5_fri_checks.rs"]
pub mod fri_checks;
