#![allow(dead_code)]

// The extraction root below is the unchanged production module. Keeping the
// `#[path]` import here avoids linking the Solana cdylib while preserving the
// production function body and its source locations in Charon's output.
#[path = "../../../../programs/aspis-verifier/src/v5_atomic_terminal.rs"]
pub mod v5_atomic_terminal;
