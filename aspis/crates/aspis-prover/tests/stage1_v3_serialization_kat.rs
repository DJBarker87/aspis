//! Forward compatibility pin for the frozen v3 claim-carrying envelope.
//!
//! The expected length/hash were independently generated from detached
//! commit `ca7045a` with this exact deterministic input before being checked
//! against the current implementation.

use aspis_core::field::{CM31, M31, QM31};
use aspis_core::params::PROFILE_CAPACITY_LR10_Q36_G16 as PROFILE;
use aspis_core::proof::{Header, VERSION_V3};
use aspis_core::{verify_with_claim, EvaluationClaim, FoldPayload, MerkleMode};
use aspis_prover::{multilinear_eval, prove_with_claim, seeded_coeffs, ProveOptions, HOST_HASH};
use sha2::{Digest, Sha256};

const SOURCE_COMMIT: &str = "ca7045a";
const EXPECTED_PROOF_LEN: usize = 21_156;
const EXPECTED_PROOF_SHA256: [u8; 32] = [
    0x1a, 0xb4, 0xd0, 0x79, 0xea, 0x6d, 0x00, 0xef, 0x82, 0x34, 0x7f, 0x4a, 0x53, 0x79, 0x94, 0xad,
    0xf6, 0xcc, 0xc4, 0x35, 0x3b, 0xea, 0xf4, 0xb4, 0x16, 0x47, 0x5d, 0xe8, 0x6c, 0x4b, 0xfa, 0xe8,
];

#[test]
fn v3_claim_proof_serialization_matches_detached_anchor() {
    let coeffs = seeded_coeffs(PROFILE.log_rows, 0x5eed_c2a5);
    let z = (0..PROFILE.log_rows)
        .map(|index| QM31::from_cm31(CM31::from_m31(M31(101 + 17 * index))))
        .collect::<Vec<_>>();
    let claim = EvaluationClaim {
        v: multilinear_eval(&coeffs, &z),
        z,
    };
    let statement = [0x5au8; 32];
    let proof = prove_with_claim(
        &PROFILE,
        &coeffs,
        &statement,
        &claim,
        &ProveOptions {
            fold_payload: FoldPayload::RawFibers,
            merkle_mode: MerkleMode::MinimalSubtree,
        },
        HOST_HASH,
    );

    assert_eq!(Header::parse(&proof).unwrap().version, VERSION_V3);
    assert_eq!(
        verify_with_claim(&proof, &statement, Some(&claim), HOST_HASH),
        Ok(())
    );
    assert_eq!(
        proof.len(),
        EXPECTED_PROOF_LEN,
        "v3 proof length drifted from independently generated detached {SOURCE_COMMIT} anchor"
    );
    assert_eq!(
        <[u8; 32]>::from(Sha256::digest(&proof)),
        EXPECTED_PROOF_SHA256,
        "v3 proof bytes drifted from independently generated detached {SOURCE_COMMIT} anchor"
    );
}
