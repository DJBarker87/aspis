//! Byte-level correspondence tests for the V5 Fiat--Shamir event trace.
//!
//! The fixed test replays the released accepted proof through the same
//! transcript driver used by the production verifier.  The varied test drives
//! the shared final/query helper with different final polynomials, nonces, and
//! selectors.  These tests support, but do not replace, the Lean theorem and
//! the remaining universal Rust-to-Lean source equality.

#![cfg(any(feature = "v5-cu-probe", feature = "v5-production-tag67"))]

use std::cell::RefCell;

use aspis_core::field::M31;
use aspis_core::proof::M31_CIRCLE_BASIS_DISCRIMINATOR;
use aspis_core::state_only_sumcheck::{
    STATE_ONLY_CONSTRAINT_REGISTRY_BYTES, STATE_ONLY_SUMCHECK_ROUND_BYTES,
};
use aspis_core::sumcheck::SUMCHECK_COEFFICIENTS;
use aspis_core::transcript::{label, Transcript};
use aspis_statement::{
    atomic_payment_statement_digest_v4, decode_digest_canonical, AtomicPaymentStatementV4,
    SpendPublic,
};
use aspis_verifier::v5_cu_probe::fri_checks::{
    bind_final_and_derive_v5_queries, V5_FRI_FINAL_BYTES,
};
use aspis_verifier::v5_cu_probe::{
    v5_complete_queries_with_statement_digest, V5_CU_PROBE_BATCH_NONCE_OFFSET,
    V5_CU_PROBE_FINAL_COEFFICIENTS_OFFSET, V5_CU_PROBE_FINAL_NONCE_OFFSET,
    V5_CU_PROBE_PREFIX_OFFSET, V5_CU_PROBE_PRIVATE_ROOTS_OFFSET, V5_CU_PROBE_QUERY_SELECTOR_OFFSET,
    V5_CU_PROBE_RELATION_CLAIMS_OFFSET, V5_CU_PROBE_RELATION_FINAL_OFFSET,
    V5_CU_PROBE_RELATION_POINTS_OFFSET, V5_CU_PROBE_RELATION_STRESS_OFFSET,
    V5_CU_REAL_PREFIX_C1_ROOT_OFFSET, V5_CU_REAL_PREFIX_C2_ROOT_OFFSET,
    V5_CU_REAL_PREFIX_CLAIMS_OFFSET, V5_CU_REAL_PREFIX_INACTIVE_CLAIM_OFFSET,
    V5_CU_REAL_PREFIX_INITIAL_B_CLAIM_OFFSET, V5_CU_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET,
    V5_CU_REAL_PREFIX_RESERVED_OFFSET, V5_CU_REAL_PREFIX_SUMCHECK_OFFSET,
    V5_CU_REAL_PREFIX_TERMINAL_OFFSET,
};
use aspis_verifier::v5_relation_stress::V5_RELATION_STRESS_FINAL_OFFSET;
use aspis_verifier::v5_relation_stress::{
    V5_RELATION_STRESS_OOD_OFFSET, V5_RELATION_STRESS_OOD_SAMPLES, V5_RELATION_STRESS_ROUNDS,
    V5_RELATION_STRESS_SUMCHECK_OFFSET,
};
use solana_program::hash::hashv;

const MAINNET_PROOF: &[u8] =
    include_bytes!("../../../release/aspis-v5-tag67-mainnet-v1/proof/v5-mainnet-proof.bin");
const PROFILE_DOMAIN: &[u8] = b"aspis-v5-real-witness-cu-v1";
const QM31_BYTES: usize = 16;
const PUBLIC_SALT_BYTES: usize = 32;

#[derive(Clone, Debug, PartialEq, Eq)]
enum ObservedEvent {
    Absorb { label: u8, payload: Vec<u8> },
    SqueezeOutput,
    SqueezeAdvance,
    WorkCheck { nonce_le: Vec<u8> },
}

thread_local! {
    static OBSERVED: RefCell<Vec<ObservedEvent>> = const { RefCell::new(Vec::new()) };
}

fn record_transcript_hash_call(inputs: &[&[u8]]) {
    if inputs.first().is_none_or(|state| state.len() != 32) {
        return;
    }
    match inputs {
        [_, domain_label, payload] if domain_label.len() == 2 && domain_label[0] == 0 => {
            OBSERVED.with(|events| {
                events.borrow_mut().push(ObservedEvent::Absorb {
                    label: domain_label[1],
                    payload: payload.to_vec(),
                });
            });
        }
        [_, domain] if *domain == [1] => {
            OBSERVED.with(|events| events.borrow_mut().push(ObservedEvent::SqueezeOutput));
        }
        [_, domain] if *domain == [2] => {
            OBSERVED.with(|events| events.borrow_mut().push(ObservedEvent::SqueezeAdvance));
        }
        [_, domain, nonce] if *domain == [3] && nonce.len() == 8 => {
            OBSERVED.with(|events| {
                events.borrow_mut().push(ObservedEvent::WorkCheck {
                    nonce_le: nonce.to_vec(),
                });
            });
        }
        _ => {}
    }
}

fn tracing_hashv(inputs: &[&[u8]]) -> [u8; 32] {
    record_transcript_hash_call(inputs);
    hashv(inputs).to_bytes()
}

fn permissive_work_tracing_hashv(inputs: &[&[u8]]) -> [u8; 32] {
    record_transcript_hash_call(inputs);
    if matches!(inputs, [state, domain, nonce]
        if state.len() == 32 && *domain == [3] && nonce.len() == 8)
    {
        [0u8; 32]
    } else {
        hashv(inputs).to_bytes()
    }
}

fn take_observed() -> Vec<ObservedEvent> {
    OBSERVED.with(|events| std::mem::take(&mut *events.borrow_mut()))
}

fn clear_observed() {
    OBSERVED.with(|events| events.borrow_mut().clear());
}

fn push_absorb(events: &mut Vec<ObservedEvent>, event_label: u8, payload: impl AsRef<[u8]>) {
    events.push(ObservedEvent::Absorb {
        label: event_label,
        payload: payload.as_ref().to_vec(),
    });
}

fn push_squeeze(events: &mut Vec<ObservedEvent>) {
    events.push(ObservedEvent::SqueezeOutput);
    events.push(ObservedEvent::SqueezeAdvance);
}

fn push_work(events: &mut Vec<ObservedEvent>, nonce_le: impl AsRef<[u8]>) {
    events.push(ObservedEvent::WorkCheck {
        nonce_le: nonce_le.as_ref().to_vec(),
    });
}

fn round_root_record(layer: usize, root: &[u8], salt: &[u8]) -> Vec<u8> {
    let mut record = Vec::with_capacity(65);
    record.push(layer as u8);
    record.extend_from_slice(root);
    record.extend_from_slice(salt);
    record
}

fn c2_root_record(root: &[u8], salt: &[u8]) -> Vec<u8> {
    let mut record = Vec::with_capacity(64);
    record.extend_from_slice(root);
    record.extend_from_slice(salt);
    record
}

fn state_only_constraint_registry() -> [u8; STATE_ONLY_CONSTRAINT_REGISTRY_BYTES] {
    [
        1, 29, 95, 0, 10, 27, 28, 102, 0, 17, 48, 33, 175, 20, 236, 180, 29, 18, 251, 234, 229,
        239, 81, 34, 103, 18, 0, 0,
    ]
}

fn public_salt(prefix: &[u8], section: usize) -> &[u8] {
    let start = V5_CU_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET + section * PUBLIC_SALT_BYTES;
    &prefix[start..start + PUBLIC_SALT_BYTES]
}

fn private_root(proof: &[u8], section: usize) -> &[u8] {
    let start = V5_CU_PROBE_PRIVATE_ROOTS_OFFSET + section * 32;
    &proof[start..start + 32]
}

fn expected_mainnet_trace(proof: &[u8]) -> Vec<ObservedEvent> {
    let prefix = &proof[V5_CU_PROBE_PREFIX_OFFSET..V5_CU_PROBE_PREFIX_OFFSET + 6_423];
    let stress = &proof[V5_CU_PROBE_RELATION_STRESS_OFFSET..V5_CU_PROBE_FINAL_NONCE_OFFSET];
    let mut expected = Vec::new();

    push_absorb(&mut expected, label::PROFILE, PROFILE_DOMAIN);
    push_absorb(
        &mut expected,
        label::M31_CIRCLE_BASIS,
        M31_CIRCLE_BASIS_DISCRIMINATOR,
    );
    // The statement digest is filled by the caller after this trace is built.
    push_absorb(&mut expected, label::STATEMENT, [0u8; 32]);
    push_absorb(
        &mut expected,
        label::M31_CIRCLE_ROUND_ROOT,
        round_root_record(0, private_root(proof, 0), public_salt(prefix, 0)),
    );
    push_squeeze(&mut expected); // lambda
    push_squeeze(&mut expected); // chi
    push_absorb(
        &mut expected,
        label::M31_CIRCLE_C2_ROOT,
        c2_root_record(private_root(proof, 1), public_salt(prefix, 1)),
    );
    push_absorb(
        &mut expected,
        label::M31_STATE_ONLY_CONSTRAINT_REGISTRY,
        state_only_constraint_registry(),
    );
    push_absorb(&mut expected, label::M31_STATE_ONLY_HELPER_SUM, [0u8; 16]);
    for _ in 0..12 {
        push_squeeze(&mut expected); // theta, ten equality coordinates, mu
    }
    let mut mask_claim = Vec::with_capacity(18);
    mask_claim.extend_from_slice(&[27, 10]);
    mask_claim.extend_from_slice(
        &prefix[V5_CU_REAL_PREFIX_INITIAL_B_CLAIM_OFFSET..V5_CU_REAL_PREFIX_SUMCHECK_OFFSET],
    );
    push_absorb(
        &mut expected,
        label::M31_STATE_ONLY_HIDING_MASK_CLAIM,
        mask_claim,
    );
    push_squeeze(&mut expected); // eta
    for round in 0..10 {
        let start = V5_CU_REAL_PREFIX_SUMCHECK_OFFSET + round * STATE_ONLY_SUMCHECK_ROUND_BYTES;
        let mut framed = Vec::with_capacity(1 + STATE_ONLY_SUMCHECK_ROUND_BYTES);
        framed.push(round as u8);
        framed.extend_from_slice(&prefix[start..start + STATE_ONLY_SUMCHECK_ROUND_BYTES]);
        push_absorb(
            &mut expected,
            label::M31_STATE_ONLY_ZEROCHECK_SUMCHECK,
            framed,
        );
        push_squeeze(&mut expected);
    }
    push_absorb(
        &mut expected,
        label::M31_CIRCLE_STATEMENT_POINTS,
        &proof[V5_CU_PROBE_RELATION_POINTS_OFFSET..V5_CU_PROBE_RELATION_CLAIMS_OFFSET],
    );
    push_absorb(
        &mut expected,
        label::M31_CIRCLE_STATEMENT_EVALUATIONS,
        &prefix[V5_CU_REAL_PREFIX_CLAIMS_OFFSET..V5_CU_REAL_PREFIX_TERMINAL_OFFSET],
    );
    push_absorb(
        &mut expected,
        label::CLAIM,
        &prefix[V5_CU_REAL_PREFIX_TERMINAL_OFFSET..V5_CU_REAL_PREFIX_INACTIVE_CLAIM_OFFSET],
    );
    let batch_nonce = &proof[V5_CU_PROBE_BATCH_NONCE_OFFSET..V5_CU_PROBE_BATCH_NONCE_OFFSET + 8];
    push_work(&mut expected, batch_nonce);
    push_absorb(
        &mut expected,
        label::M31_PAYMENT_BATCH_POW_NONCE,
        batch_nonce,
    );
    push_squeeze(&mut expected); // gamma
    push_absorb(
        &mut expected,
        label::SECOND_PHASE_CLAIM,
        &prefix[V5_CU_REAL_PREFIX_INACTIVE_CLAIM_OFFSET..V5_CU_REAL_PREFIX_RESERVED_OFFSET],
    );
    push_squeeze(&mut expected); // kappa

    for round in 0..V5_RELATION_STRESS_ROUNDS {
        for sample in 0..V5_RELATION_STRESS_OOD_SAMPLES {
            push_squeeze(&mut expected); // circle parameter or line point
            let observation = round * V5_RELATION_STRESS_OOD_SAMPLES + sample;
            let value_start = V5_RELATION_STRESS_OOD_OFFSET + observation * QM31_BYTES;
            let mut record = Vec::with_capacity(18);
            record.extend_from_slice(&[round as u8, sample as u8]);
            record.extend_from_slice(&stress[value_start..value_start + QM31_BYTES]);
            push_absorb(
                &mut expected,
                if round == 0 {
                    label::M31_CIRCLE_OOD_VALUE
                } else {
                    label::M31_LINE_OOD_VALUE
                },
                record,
            );
            push_squeeze(&mut expected); // mix
        }
        let sumcheck_start =
            V5_RELATION_STRESS_SUMCHECK_OFFSET + round * SUMCHECK_COEFFICIENTS * QM31_BYTES;
        let mut sumcheck = Vec::with_capacity(1 + SUMCHECK_COEFFICIENTS * QM31_BYTES);
        sumcheck.push(round as u8);
        sumcheck.extend_from_slice(
            &stress[sumcheck_start..sumcheck_start + SUMCHECK_COEFFICIENTS * QM31_BYTES],
        );
        push_absorb(&mut expected, label::M31_CIRCLE_RELATION_SUMCHECK, sumcheck);
        let nonce_start = V5_CU_PROBE_RELATION_FINAL_OFFSET + round * 8;
        let nonce = &proof[nonce_start..nonce_start + 8];
        push_work(&mut expected, nonce);
        let mut fold_work = Vec::with_capacity(9);
        fold_work.push(round as u8);
        fold_work.extend_from_slice(nonce);
        push_absorb(&mut expected, label::M31_CIRCLE_FOLD_POW_NONCE, fold_work);
        push_squeeze(&mut expected); // alpha
        if round < 3 {
            push_absorb(
                &mut expected,
                label::M31_CIRCLE_ROUND_ROOT,
                round_root_record(
                    round + 1,
                    private_root(proof, round + 2),
                    public_salt(prefix, round + 2),
                ),
            );
        }
    }

    let final_polynomial = &proof[V5_CU_PROBE_FINAL_COEFFICIENTS_OFFSET
        ..V5_CU_PROBE_FINAL_COEFFICIENTS_OFFSET + V5_FRI_FINAL_BYTES];
    assert_eq!(
        final_polynomial,
        &stress
            [V5_RELATION_STRESS_FINAL_OFFSET..V5_RELATION_STRESS_FINAL_OFFSET + V5_FRI_FINAL_BYTES]
    );
    push_absorb(
        &mut expected,
        label::M31_CIRCLE_FINAL_TENSOR_POLY,
        final_polynomial,
    );
    let final_nonce = &proof[V5_CU_PROBE_FINAL_NONCE_OFFSET..V5_CU_PROBE_FINAL_NONCE_OFFSET + 8];
    push_work(&mut expected, final_nonce);
    push_absorb(&mut expected, label::GRIND_NONCE, final_nonce);
    push_absorb(
        &mut expected,
        label::M31_STATE_ONLY_QUERY_CANDIDATE,
        [proof[V5_CU_PROBE_QUERY_SELECTOR_OFFSET]],
    );
    for _ in 0..3 {
        push_squeeze(&mut expected); // 18 distinct words fit in three blocks
    }
    expected
}

fn decode_hex_32(value: &str) -> [u8; 32] {
    assert_eq!(value.len(), 64);
    let mut output = [0u8; 32];
    for (index, byte) in output.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16).unwrap();
    }
    output
}

fn decode_digest(value: &str) -> [M31; 8] {
    decode_digest_canonical(&decode_hex_32(value)).unwrap()
}

fn mainnet_statement() -> AtomicPaymentStatementV4 {
    AtomicPaymentStatementV4 {
        pool: decode_hex_32("0d5b6b8aef565a35887ad0c60acbaa27a7c8db501a1adfc1ad2171c44664de48"),
        sequence: 0,
        spend: SpendPublic {
            anchor: decode_digest(
                "2f1c920dc6b3ad1fa6d29a0da5eb3232892c4c0edcd86c4a3825215a9fb7da63",
            ),
            nullifier: decode_digest(
                "251bbb2be96bef3b6eccab04da5ab27bc3b3c04bfb9ef5598a417d3406759317",
            ),
            output_commitment: decode_digest(
                "7a08e0333baf4b7bc34e14690adcb507ef6e32021e5767628d388337eab0c30e",
            ),
            asset_id: M31(17),
            fee: 1,
        },
        output_anchor: decode_digest(
            "e0de9172992f6e4803419a5fca909d3d3507ee7d81cc956ef4977a1ceeab967f",
        ),
        deployment_domain: decode_hex_32(
            "87682be1a518ecc95f7aac6e7f400a1419c0383a0d554877a6ab0a3ce6e31936",
        ),
    }
}

#[test]
fn accepted_v5_proof_matches_the_complete_modeled_event_trace() {
    clear_observed();
    let statement_digest =
        atomic_payment_statement_digest_v4(&mainnet_statement(), tracing_hashv).unwrap();
    // Digest construction is outside the transcript itself.
    clear_observed();
    let queries =
        v5_complete_queries_with_statement_digest(tracing_hashv, MAINNET_PROOF, &statement_digest)
            .expect("released proof has an accepted transcript");
    assert_eq!(queries.len(), 18);
    let mut sorted = queries;
    sorted.sort_unstable();
    assert!(sorted.windows(2).all(|pair| pair[0] != pair[1]));

    let mut expected = expected_mainnet_trace(MAINNET_PROOF);
    match &mut expected[2] {
        ObservedEvent::Absorb { label, payload } => {
            assert_eq!(*label, label::STATEMENT);
            payload.copy_from_slice(&statement_digest);
        }
        _ => panic!("statement must be the third transcript event"),
    }
    let observed = take_observed();
    assert_eq!(observed.len(), 151);
    assert_eq!(observed, expected);

    // The two prefix roots are the same authenticated roots used by the
    // private-opening verifier, rather than independent proof copies.
    assert_eq!(
        &MAINNET_PROOF[V5_CU_PROBE_PREFIX_OFFSET + V5_CU_REAL_PREFIX_C1_ROOT_OFFSET
            ..V5_CU_PROBE_PREFIX_OFFSET + V5_CU_REAL_PREFIX_C1_ROOT_OFFSET + 32],
        private_root(MAINNET_PROOF, 0)
    );
    assert_eq!(
        &MAINNET_PROOF[V5_CU_PROBE_PREFIX_OFFSET + V5_CU_REAL_PREFIX_C2_ROOT_OFFSET
            ..V5_CU_PROBE_PREFIX_OFFSET + V5_CU_REAL_PREFIX_C2_ROOT_OFFSET + 32],
        private_root(MAINNET_PROOF, 1)
    );
}

#[test]
fn final_query_helper_matches_modeled_tail_for_varied_inputs() {
    for seed in [0x11u8, 0x57, 0xa3] {
        for selector in 0u8..3 {
            clear_observed();
            let mut transcript = Transcript::new(permissive_work_tracing_hashv);
            transcript.absorb(label::PROFILE, &[seed; 27]);
            clear_observed();

            let mut final_polynomial = [0u8; V5_FRI_FINAL_BYTES];
            for coefficient in 0..4 {
                for limb in 0..4 {
                    let value = u32::from(seed) + (coefficient * 19 + limb * 3) as u32;
                    let start = coefficient * 16 + limb * 4;
                    final_polynomial[start..start + 4].copy_from_slice(&value.to_le_bytes());
                }
            }
            let nonce = u64::from(seed) << 40 | u64::from(selector) << 8 | 0x5a;
            let (_, queries) = bind_final_and_derive_v5_queries(
                &mut transcript,
                &final_polynomial,
                nonce,
                selector,
                true,
            )
            .expect("permissive work hash accepts the varied tail");
            assert_eq!(queries.len(), 18);
            let mut sorted = queries;
            sorted.sort_unstable();
            assert!(sorted.windows(2).all(|pair| pair[0] != pair[1]));

            let mut expected = Vec::new();
            push_absorb(
                &mut expected,
                label::M31_CIRCLE_FINAL_TENSOR_POLY,
                final_polynomial,
            );
            push_work(&mut expected, nonce.to_le_bytes());
            push_absorb(&mut expected, label::GRIND_NONCE, nonce.to_le_bytes());
            push_absorb(
                &mut expected,
                label::M31_STATE_ONLY_QUERY_CANDIDATE,
                [selector],
            );
            for _ in 0..3 {
                push_squeeze(&mut expected);
            }
            assert_eq!(
                take_observed(),
                expected,
                "seed {seed:#04x}, selector {selector}"
            );
        }
    }
}
