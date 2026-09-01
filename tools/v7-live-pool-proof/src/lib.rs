//! Production-prover handoff for authenticated live pair-forest plans.
//!
//! This crate intentionally has no insecure fixture feature and no API that
//! accepts a caller-supplied verifier result. The proof account public key is
//! the public attempt nonce used by the verifier.

use std::{io, path::Path};

use aspis_core::v7_fixed_canonical_audit::transcode_tag73_to_canonical_fixed;
use aspis_pool_wallet_v1::live_pool_witness_adapter_v2::{
    LivePairForestTransferPlanV2, LivePairForestWithdrawalPlanV2,
};
use aspis_prover::{
    state_only_entropy::{DurableStateOnlyMaskNonceStore, StateOnlyAttemptSecrets},
    v6_onefold_prover::{
        build_v7_pool_pair_forest_private_transfer_onefold_proof_production,
        build_v7_pool_pair_forest_withdrawal_onefold_proof_production, BuiltV7CompactOneFoldProof,
        V6ProverError, V7ProverContext,
    },
    HOST_HASH,
};
use aspis_statement::pool_v1::{
    encode_pool_v1_pair_verified_afterstate_v1, PoolV1PairVerifierTransportErrorV1,
    PoolV1PaymentRelationContextV1,
};

#[derive(Debug)]
pub enum LivePoolProofErrorV1 {
    NonceLedger(io::Error),
    Entropy,
    Prover(V6ProverError),
    ProverWire(aspis_core::v6_onefold::V6WireError),
    Afterstate(PoolV1PairVerifierTransportErrorV1),
}

pub struct BuiltLivePoolProofV1 {
    pub proof: BuiltV7CompactOneFoldProof,
    pub proof_payload: Vec<u8>,
}

fn payload(
    afterstate: &aspis_statement::pool_v1::PoolV1PairVerifiedAfterstateV1,
    mut proof: BuiltV7CompactOneFoldProof,
) -> Result<BuiltLivePoolProofV1, LivePoolProofErrorV1> {
    // The frozen one-transaction candidate verifier consumes the audit wire
    // whose 641 fixed QM31 values are canonical 16-byte records. The honest
    // prover emits the equivalent packed Tag-73 wire, so transcode only that
    // fixed section before upload. Roots, work nonces, query records, salts,
    // and both Merkle frontiers remain byte-identical.
    proof.bytes = transcode_tag73_to_canonical_fixed(&proof.bytes, proof.frontier_nodes)
        .map_err(LivePoolProofErrorV1::ProverWire)?;
    let candidate = encode_pool_v1_pair_verified_afterstate_v1(afterstate)
        .map_err(LivePoolProofErrorV1::Afterstate)?;
    let mut proof_payload = Vec::with_capacity(candidate.len() + proof.bytes.len());
    proof_payload.extend_from_slice(&candidate);
    proof_payload.extend_from_slice(&proof.bytes);
    Ok(BuiltLivePoolProofV1 {
        proof,
        proof_payload,
    })
}

pub fn prove_live_pair_forest_transfer_v1(
    plan: &LivePairForestTransferPlanV2,
    nonce_ledger: impl AsRef<Path>,
) -> Result<BuiltLivePoolProofV1, LivePoolProofErrorV1> {
    let attempt = StateOnlyAttemptSecrets::generate_for_mask_nonce(plan.attempt_id)
        .map_err(|_| LivePoolProofErrorV1::Entropy)?;
    let mut nonce_store = DurableStateOnlyMaskNonceStore::open(nonce_ledger)
        .map_err(LivePoolProofErrorV1::NonceLedger)?;
    let proof = build_v7_pool_pair_forest_private_transfer_onefold_proof_production(
        &plan.public,
        &plan.witness,
        PoolV1PaymentRelationContextV1 {
            runtime_binding: plan.runtime_binding,
            spent_nullifiers: &[],
        },
        &plan.transition,
        plan.statement_digest,
        V7ProverContext {
            program_id: plan.verifier_program,
            release_binding: plan.request.verifier_release,
            attempt_id: plan.attempt_id,
        },
        attempt,
        &mut nonce_store,
        HOST_HASH,
    )
    .map_err(LivePoolProofErrorV1::Prover)?;
    payload(&plan.transition.candidate_afterstate, proof)
}

pub fn prove_live_pair_forest_withdrawal_v1(
    plan: &LivePairForestWithdrawalPlanV2,
    nonce_ledger: impl AsRef<Path>,
) -> Result<BuiltLivePoolProofV1, LivePoolProofErrorV1> {
    let attempt = StateOnlyAttemptSecrets::generate_for_mask_nonce(plan.attempt_id)
        .map_err(|_| LivePoolProofErrorV1::Entropy)?;
    let mut nonce_store = DurableStateOnlyMaskNonceStore::open(nonce_ledger)
        .map_err(LivePoolProofErrorV1::NonceLedger)?;
    let proof = build_v7_pool_pair_forest_withdrawal_onefold_proof_production(
        &plan.public,
        &plan.witness,
        PoolV1PaymentRelationContextV1 {
            runtime_binding: plan.runtime_binding,
            spent_nullifiers: &[],
        },
        &plan.transition,
        plan.statement_digest,
        V7ProverContext {
            program_id: plan.verifier_program,
            release_binding: plan.request.verifier_release,
            attempt_id: plan.attempt_id,
        },
        attempt,
        &mut nonce_store,
        HOST_HASH,
    )
    .map_err(LivePoolProofErrorV1::Prover)?;
    payload(&plan.transition.candidate_afterstate, proof)
}
