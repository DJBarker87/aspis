#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

pub mod field;
pub mod merkle;
pub mod profile;
pub mod proof;
pub mod statement;
pub mod transcript;
pub mod verifier;

pub use field::{Cm31, LiftPolicy, Qm31, CM31, M31, QM31};
pub use profile::{
    profile_manifest, HashMode, ProfileId, SvmRuntimeLimits, WhirFoldMode, WhirProfileManifest,
};
pub use proof::{
    CommitmentRoot, FoldRoundProof, MerkleMultiProof, MerkleProof, QueryBlock, QueryIndex,
    QueryOpening, TranscriptCommitmentSection, WhirEnvelopeV1, WhirEnvelopeView, WhirProofV0,
    ENVELOPE_VERSION,
};
pub use statement::{SpendV0Binding, StatementDigest, MAX_NULLIFIERS, MAX_OUTPUTS};
pub use verifier::{verify_proof_bytes, VerificationReport, VerifyError};
