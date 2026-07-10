//! Aspis SpendV0 statement layer, built evaluator-first.
//!
//! This crate deliberately contains no proof system. It defines the exact
//! M31-native hash, spend relations, economic failure modes, and isolated
//! constraint-composition kernel that Stage 2 must make correct before any
//! statement proof is wired into the PCS.

#![no_std]

extern crate alloc;

pub mod composition;
pub mod poseidon2;
pub mod spend;
pub mod split;

pub use composition::{
    evaluate_composition_probe, evaluate_composition_probe_optimized, CompositionProbe,
    CompositionProbeResult,
};
pub use poseidon2::{hash_fields, permute, Digest, DIGEST_ELEMS, POSEIDON2_WIDTH, RATE};
pub use spend::{
    derive_nullifier, derive_owner_key, evaluate_spend, merkle_root, note_commitment,
    output_commitment, EvaluationContext, MerklePath, SpendError, SpendPublic, SpendWitness,
    VALUE_LIMIT,
};
pub use split::{
    ReceiptBinding, ReceiptError, ReceiptStatus, SplitVerificationReceipt, TERMINAL_POINT_LEN,
};
