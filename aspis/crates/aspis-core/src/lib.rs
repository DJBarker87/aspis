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

pub mod field;
pub mod merkle;
pub mod params;
pub mod proof;
pub mod transcript;
pub mod verify;

pub use params::{FoldPayload, MerkleMode, Profile, PROFILES};
pub use transcript::HashFn;
pub use verify::{verify, VerifyError};

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
        assert_eq!(
            half,
            CM31::from_m31(crate::field::M31(crate::field::P - 1))
        );
        assert_eq!(half.mul(half), CM31::ONE);
    }
}
