//! aspis-core: shared no_std verifier core for the Aspis native WHIR-style
//! M31 PCS substrate (Stage 0).
//!
//! This crate knows nothing about spends, notes, or pools. Its public
//! surface is `verify(proof_bytes, statement_digest, hash_backend)`. The
//! same code path runs byte-exact on the host (sha2 backend) and on SBF
//! (SHA-256 syscall backend).
//!
//! Claim discipline (design section 5): this is a WHIR-STYLE multilinear PCS
//! substrate, not paper WHIR. What v0 verifies is transcript-bound local
//! fold consistency; the soundness delta to a stated proximity assumption is
//! Stage 1 work and no soundness figure may be quoted from this code alone.

#![no_std]

extern crate alloc;

pub mod circle;
pub mod circle_fri;
pub mod circle_hiding_prefix;
pub mod circle_hiding_query;
pub mod circle_line_merkle;
pub mod circle_merkle;
pub mod circle_openings;
pub mod circle_pcs_shape;
pub mod circle_prefix;
pub mod circle_query;
pub mod field;
pub mod merkle;
pub mod params;
pub mod proof;
pub mod state_only_hiding;
pub mod state_only_masked_switch;
pub mod state_only_masked_switch_basis;
pub mod state_only_prefix;
pub mod state_only_private_merkle;
pub mod state_only_private_openings;
pub mod state_only_query;
pub mod state_only_relation;
pub mod state_only_spend_openings;
pub mod state_only_spend_query;
pub mod state_only_spend_relation;
pub mod state_only_sumcheck;
pub mod statement_hiding;
pub mod statement_sumcheck;
pub mod sumcheck;
pub mod transcript;
pub mod v6_onefold;
pub mod v6_query_batch;
pub mod v6_transcript;
pub mod v7_code_switch;
pub mod v7_compact_onefold;
pub mod v7_lane_zeta;
pub mod v7_merkle;
pub mod v7_merkle208;
pub mod v7_onefold;
pub mod v7_profile;
pub mod v7_staged_pair;
pub mod verify;

pub use params::{FoldPayload, MerkleMode, Profile, PROFILES};
pub use transcript::HashFn;
#[cfg(feature = "insecure-test-framing")]
pub use verify::verify_with_insecure_m31_circle_as_legacy_for_tests;
pub use verify::{
    verify, verify_with_claim, verify_with_claim_and_trace, verify_with_claim_trace_and_inverse,
    verify_with_trace, EvaluationClaim, M31InverseFn, TraceEvent, TraceFn, VerifyError,
};
#[cfg(feature = "insecure-test-ordering")]
pub use verify::{verify_with_insecure_ordering, InsecureOrdering};

#[cfg(test)]
mod tests {
    use crate::field::CM31;
    use crate::params::{CIRCLE_GEN, CIRCLE_LOG_ORDER};

    #[test]
    fn circle_generator_order() {
        // on the unit circle: a^2 + b^2 == 1
        let norm = CIRCLE_GEN
            .a
            .mul(CIRCLE_GEN.a)
            .add(CIRCLE_GEN.b.mul(CIRCLE_GEN.b));
        assert_eq!(norm, crate::field::M31::ONE);
        // order exactly 2^31: G^(2^30) == -1, G^(2^31) == 1
        let half = CIRCLE_GEN.pow(1u64 << (CIRCLE_LOG_ORDER - 1));
        assert_eq!(half, CM31::from_m31(crate::field::M31(crate::field::P - 1)));
        assert_eq!(half.mul(half), CM31::ONE);
    }
}
