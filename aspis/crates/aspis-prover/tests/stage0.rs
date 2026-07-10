//! Stage 0 gate tests: prove/verify parity, the four corruption classes,
//! statement binding, framing, and cross-mode behavior.
//!
//! The verifier code exercised here is the identical no_std path the SBF
//! program runs (hash backend swapped), so host acceptance here is the host
//! half of the accept/reject parity gate item.

use aspis_core::params::{PROFILE_CAPACITY, PROFILE_CAPACITY_LR14, PROFILE_JOHNSON};
use aspis_core::proof::{HEADER_LEN, ROUND_COMMITMENT_LEN};
use aspis_core::{verify, FoldPayload, MerkleMode, Profile, VerifyError};
use aspis_prover::{prove, seeded_coeffs, ProveOptions, HOST_HASH};

fn digest(seed: u64) -> [u8; 32] {
    use sha2::Digest;
    let mut h = sha2::Sha256::new();
    h.update(b"aspis-stage0-test");
    h.update(seed.to_le_bytes());
    h.finalize().into()
}

fn prove_one(
    profile: &Profile,
    seed: u64,
    payload: FoldPayload,
    mode: MerkleMode,
) -> (Vec<u8>, [u8; 32]) {
    let coeffs = seeded_coeffs(profile.log_rows, seed + 1);
    let d = digest(seed);
    let proof = prove(
        profile,
        &coeffs,
        &d,
        &ProveOptions {
            fold_payload: payload,
            merkle_mode: mode,
        },
        HOST_HASH,
    );
    (proof, d)
}

#[test]
fn parity_10_of_10_all_variants() {
    for profile in [&PROFILE_CAPACITY, &PROFILE_JOHNSON] {
        for payload in [FoldPayload::RawFibers, FoldPayload::ProofCarriedRoundLocal] {
            for mode in [MerkleMode::MinimalSubtree, MerkleMode::SinglePaths] {
                for seed in 0..10 {
                    let (proof, d) = prove_one(profile, seed, payload, mode);
                    assert_eq!(
                        verify(&proof, &d, HOST_HASH),
                        Ok(()),
                        "profile {} payload {:?} mode {:?} seed {}",
                        profile.name,
                        payload,
                        mode,
                        seed
                    );
                }
            }
        }
    }
}

#[test]
fn statement_sized_profile_lr14() {
    let (proof, d) = prove_one(
        &PROFILE_CAPACITY_LR14,
        7,
        FoldPayload::RawFibers,
        MerkleMode::MinimalSubtree,
    );
    assert_eq!(verify(&proof, &d, HOST_HASH), Ok(()));
}

#[test]
fn radix4_minimal_subtree_roundtrip_and_frontier_corruption() {
    let profile = &PROFILE_CAPACITY;
    let (radix4_proof, d) = prove_one(
        profile,
        11,
        FoldPayload::RawFibers,
        MerkleMode::Radix4MinimalSubtree,
    );
    assert_eq!(verify(&radix4_proof, &d, HOST_HASH), Ok(()));

    let (binary_proof, _) = prove_one(
        profile,
        11,
        FoldPayload::RawFibers,
        MerkleMode::MinimalSubtree,
    );
    assert_ne!(
        &radix4_proof[HEADER_LEN..HEADER_LEN + 32],
        &binary_proof[HEADER_LEN..HEADER_LEN + 32],
        "radix-4 commitment must be domain-separated from the binary tree"
    );

    let body = HEADER_LEN
        + profile.num_rounds() as usize * ROUND_COMMITMENT_LEN
        + profile.final_poly_len() as usize * 16
        + 8;
    let unique_count = u16::from_le_bytes(radix4_proof[body..body + 2].try_into().unwrap());
    let node_count_offset = body + 2 + usize::from(unique_count) * 32;
    let node_count = u32::from_le_bytes(
        radix4_proof[node_count_offset..node_count_offset + 4]
            .try_into()
            .unwrap(),
    );
    assert!(node_count > 0);
    let corrupted = corrupt_at(&radix4_proof, node_count_offset + 4);
    assert!(matches!(
        verify(&corrupted, &d, HOST_HASH),
        Err(VerifyError::MerkleMismatch { layer: 0 })
    ));
}

fn corrupt_at(proof: &[u8], offset: usize) -> Vec<u8> {
    let mut v = proof.to_vec();
    v[offset] ^= 1;
    v
}

#[test]
fn corruption_class_1_root() {
    let (proof, d) = prove_one(
        &PROFILE_CAPACITY,
        0,
        FoldPayload::RawFibers,
        MerkleMode::MinimalSubtree,
    );
    let bad = corrupt_at(&proof, HEADER_LEN + 5);
    assert!(verify(&bad, &d, HOST_HASH).is_err());
}

#[test]
fn corruption_class_2_fold_payload() {
    let profile = &PROFILE_CAPACITY;
    let (proof, d) = prove_one(
        profile,
        0,
        FoldPayload::RawFibers,
        MerkleMode::MinimalSubtree,
    );
    let body = HEADER_LEN
        + profile.num_rounds() as usize * ROUND_COMMITMENT_LEN
        + profile.final_poly_len() as usize * 16
        + 8;
    // inside layer 0's first opened fiber (skip the u16 unique count)
    let bad = corrupt_at(&proof, body + 2 + 3);
    assert!(verify(&bad, &d, HOST_HASH).is_err());
}

#[test]
fn corruption_class_3_final_poly() {
    let profile = &PROFILE_CAPACITY;
    let (proof, d) = prove_one(
        profile,
        0,
        FoldPayload::RawFibers,
        MerkleMode::MinimalSubtree,
    );
    let final_off = HEADER_LEN + profile.num_rounds() as usize * ROUND_COMMITMENT_LEN;
    let bad = corrupt_at(&proof, final_off + 1);
    assert!(verify(&bad, &d, HOST_HASH).is_err());
}

#[test]
fn corruption_class_4_grinding() {
    let profile = &PROFILE_CAPACITY;
    let (proof, d) = prove_one(
        profile,
        0,
        FoldPayload::RawFibers,
        MerkleMode::MinimalSubtree,
    );
    let nonce_off = HEADER_LEN
        + profile.num_rounds() as usize * ROUND_COMMITMENT_LEN
        + profile.final_poly_len() as usize * 16;
    let bad = corrupt_at(&proof, nonce_off);
    let outcome = verify(&bad, &d, HOST_HASH);
    assert!(matches!(
        outcome,
        Err(VerifyError::GrindingFailed) | Err(VerifyError::BadLength)
    ));
}

#[test]
fn statement_digest_binding() {
    let (proof, _) = prove_one(
        &PROFILE_CAPACITY,
        0,
        FoldPayload::RawFibers,
        MerkleMode::MinimalSubtree,
    );
    assert!(verify(&proof, &digest(999), HOST_HASH).is_err());
}

#[test]
fn framing_rejects() {
    let (proof, d) = prove_one(
        &PROFILE_CAPACITY,
        0,
        FoldPayload::RawFibers,
        MerkleMode::MinimalSubtree,
    );
    let mut extended = proof.clone();
    extended.push(0);
    assert_eq!(
        verify(&extended, &d, HOST_HASH),
        Err(VerifyError::TrailingBytes)
    );
    assert!(verify(&proof[..proof.len() - 1], &d, HOST_HASH).is_err());
    assert!(verify(&[], &d, HOST_HASH).is_err());
}

#[test]
fn mode_flag_replay_rejects() {
    // A proof built for one packaging must not verify under a flipped header
    // flag: the header is transcript-absorbed, so all challenges shift.
    let (proof, d) = prove_one(
        &PROFILE_CAPACITY,
        0,
        FoldPayload::RawFibers,
        MerkleMode::MinimalSubtree,
    );
    let mut flipped = proof.clone();
    flipped[12] = MerkleMode::SinglePaths as u8; // merkle_mode header byte
    assert!(verify(&flipped, &d, HOST_HASH).is_err());
    let mut flipped = proof;
    flipped[11] = FoldPayload::ProofCarriedRoundLocal as u8;
    assert!(verify(&flipped, &d, HOST_HASH).is_err());
}

#[test]
fn profile_swap_rejects() {
    // capacity proof presented under the johnson profile id
    let (proof, d) = prove_one(
        &PROFILE_CAPACITY,
        0,
        FoldPayload::RawFibers,
        MerkleMode::MinimalSubtree,
    );
    let mut swapped = proof;
    swapped[5] = PROFILE_JOHNSON.id;
    assert!(verify(&swapped, &d, HOST_HASH).is_err());
}

#[test]
fn degree_overflow_rejects() {
    // Commit a polynomial of degree >= 2^log_rows by evaluating with one
    // extra coefficient folded into the honest pipeline: simplest honest
    // check at this stage is that a final-poly with the wrong length framing
    // rejects; the full false-statement adversarial corpus is a Stage 1
    // deliverable (design section 8.2).
    let profile = &PROFILE_CAPACITY;
    let (proof, d) = prove_one(
        profile,
        3,
        FoldPayload::RawFibers,
        MerkleMode::MinimalSubtree,
    );
    // strip the last final-poly coefficient and splice the sections back
    let final_off = HEADER_LEN + profile.num_rounds() as usize * ROUND_COMMITMENT_LEN;
    let final_len = profile.final_poly_len() as usize * 16;
    let mut shortened = Vec::new();
    shortened.extend_from_slice(&proof[..final_off]);
    shortened.extend_from_slice(&proof[final_off..final_off + final_len - 16]);
    shortened.extend_from_slice(&proof[final_off + final_len..]);
    assert!(verify(&shortened, &d, HOST_HASH).is_err());
}
