//! Host-only release-evidence helpers.
//!
//! Nothing in this crate is linked into a Pool or verifier SBF.  The helpers
//! deliberately accept only finalized, coherently sampled account images and
//! stop before proof generation, transaction signing, or submission.

pub mod fresh_deposit_witness_adapter;
