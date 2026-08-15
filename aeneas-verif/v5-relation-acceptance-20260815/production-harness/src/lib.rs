#![allow(dead_code, unexpected_cfgs)]

// This Solana-host harness compiles the repository's unchanged production
// modules but does not register an entrypoint.  It exists solely so Charon can
// start from the module-private compact relation state and mode-9 caller.
#[path = "../../../../programs/aspis-verifier/src/atomic_payment.rs"]
pub mod atomic_payment;
#[path = "../../../../programs/aspis-verifier/src/lifecycle.rs"]
pub mod lifecycle;
#[path = "../../../../programs/aspis-verifier/src/v5_atomic_terminal.rs"]
pub mod v5_atomic_terminal;
#[path = "../../../../programs/aspis-verifier/src/v5_cu_probe.rs"]
pub mod v5_cu_probe;
#[path = "../../../../programs/aspis-verifier/src/v5_full_transaction.rs"]
pub mod v5_full_transaction;
#[path = "../../../../programs/aspis-verifier/src/v5_relation_stress.rs"]
pub mod v5_relation_stress;
#[path = "../../../../programs/aspis-verifier/src/verify.rs"]
pub mod verify;

pub use lifecycle::PROOF_ACCOUNT_HEADER_LEN;
