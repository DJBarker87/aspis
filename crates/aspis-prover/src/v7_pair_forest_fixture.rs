//! Deterministic eight-lane Tag-73 fixture for host-only integration tests.
//!
//! The containing module exists only under `cfg(test)` or the explicitly
//! insecure `insecure-spend-fixture` feature.  In particular, the unmined
//! proof builder below is absent from an ordinary production prover build.

use aspis_core::field::{M31, P};
use aspis_statement::{
    derive_owner_key,
    pool_v1::{
        compile_pool_v1_pair_forest_private_transfer_merged_c1_v1,
        encode_pool_v1_pair_forest_terminal_statement_v1,
        pair_trace::{PoolV1PairInputNoteWitnessV1, PoolV1PairTraceErrorV1},
        pool_v1_note_commitment, pool_v1_nullifier, pool_v1_pair_forest_output_lane_v1,
        pool_v1_tree_parent, PoolV1MembershipWitnessV1, PoolV1OutputNoteWitnessV1,
        PoolV1PairForestInputNoteWitnessV1, PoolV1PairForestPrivateTransferWitnessV1,
        PoolV1PairForestTerminalCommonV1, PoolV1PairForestTerminalFormatErrorV1,
        PoolV1PairForestTerminalStatementV1, PoolV1PairForestWithdrawalWitnessV1,
        PoolV1PairLatePublicStatementV1, PoolV1PairLeafErrorV1, PoolV1PairLeafWitnessV1,
        PoolV1PairLiveSnapshotV1, PoolV1PaymentRelationContextV1, PoolV1PaymentRuntimeBindingV1,
        PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1,
        V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
    },
    poseidon2::Digest,
};

use crate::{
    state_only_candidate_prefix::StateOnlyPowMode,
    state_only_entropy::StateOnlyAttemptSecrets,
    state_only_hiding::InMemoryStateOnlyMaskNonceStore,
    v6_onefold_prover::{
        build_v7_pool_pair_forest_private_transfer_onefold_proof,
        build_v7_pool_pair_forest_private_transfer_onefold_proof_production,
        build_v7_pool_pair_forest_withdrawal_onefold_proof, BuiltV7CompactOneFoldProof,
        V6ProverError, V7ProverContext,
    },
    HOST_HASH,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V7PairForestFixtureErrorV1 {
    PairLeaf(PoolV1PairLeafErrorV1),
    Trace(PoolV1PairTraceErrorV1),
    Terminal(PoolV1PairForestTerminalFormatErrorV1),
    Prover(V6ProverError),
}

impl From<PoolV1PairLeafErrorV1> for V7PairForestFixtureErrorV1 {
    fn from(error: PoolV1PairLeafErrorV1) -> Self {
        Self::PairLeaf(error)
    }
}

impl From<PoolV1PairTraceErrorV1> for V7PairForestFixtureErrorV1 {
    fn from(error: PoolV1PairTraceErrorV1) -> Self {
        Self::Trace(error)
    }
}

impl From<PoolV1PairForestTerminalFormatErrorV1> for V7PairForestFixtureErrorV1 {
    fn from(error: PoolV1PairForestTerminalFormatErrorV1) -> Self {
        Self::Terminal(error)
    }
}

impl From<V6ProverError> for V7PairForestFixtureErrorV1 {
    fn from(error: V6ProverError) -> Self {
        Self::Prover(error)
    }
}

#[derive(Clone, Debug)]
pub struct BuiltV7PairForestTransferFixtureV1 {
    pub public: PoolV1PrivateTransferPublicV1,
    pub witness: PoolV1PairForestPrivateTransferWitnessV1,
    pub transition: PoolV1PairLatePublicStatementV1,
    pub statement: PoolV1PairForestTerminalStatementV1,
    pub statement_digest: [u8; 32],
    pub proof: BuiltV7CompactOneFoldProof,
}

#[derive(Clone, Debug)]
pub struct PreparedV7PairForestTransferFixtureV1 {
    pub public: PoolV1PrivateTransferPublicV1,
    pub witness: PoolV1PairForestPrivateTransferWitnessV1,
    pub transition: PoolV1PairLatePublicStatementV1,
    pub statement: PoolV1PairForestTerminalStatementV1,
    pub statement_digest: [u8; 32],
}

#[derive(Clone, Debug)]
pub struct BuiltV7PairForestWithdrawalFixtureV1 {
    pub public: PoolV1WithdrawalPublicV1,
    pub witness: PoolV1PairForestWithdrawalWitnessV1,
    pub transition: PoolV1PairLatePublicStatementV1,
    pub statement: PoolV1PairForestTerminalStatementV1,
    pub statement_digest: [u8; 32],
    pub proof: BuiltV7CompactOneFoldProof,
}

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|lane| M31((seed + 17 * lane as u32 + 1) % P))
}

fn deterministic_input_witness_v1(
) -> Result<PoolV1PairForestInputNoteWitnessV1, PoolV1PairLeafErrorV1> {
    let nullifier_key = digest(10);
    let salt = digest(100);
    let asset_id = M31(77);
    let input_commitment =
        pool_v1_note_commitment(&derive_owner_key(&nullifier_key), 1_000, asset_id, &salt);
    Ok(PoolV1PairForestInputNoteWitnessV1 {
        pair: PoolV1PairInputNoteWitnessV1 {
            nullifier_key,
            salt,
            value: 1_000,
            pair_leaf: PoolV1PairLeafWitnessV1::two_outputs(input_commitment, digest(900))?,
            selected_second: false,
            membership: PoolV1MembershipWitnessV1 {
                siblings: core::array::from_fn(|level| digest(2_000 + 20 * level as u32)),
                index: 0x5_4321,
            },
        },
        super_root_siblings: [digest(3_000), digest(3_100), digest(3_200)],
        super_root_directions: [true, false, true],
    })
}

fn global_anchor_v1(
    input: &PoolV1PairForestInputNoteWitnessV1,
) -> Result<Digest, PoolV1PairLeafErrorV1> {
    let mut current = input.pair.pair_leaf.leaf_digest()?;
    for level in 0..20 {
        let sibling = input.pair.membership.siblings[level];
        current = if ((input.pair.membership.index >> level) & 1) == 0 {
            pool_v1_tree_parent(&current, &sibling)
        } else {
            pool_v1_tree_parent(&sibling, &current)
        };
    }
    for level in 0..3 {
        current = if input.super_root_directions[level] {
            pool_v1_tree_parent(&input.super_root_siblings[level], &current)
        } else {
            pool_v1_tree_parent(&current, &input.super_root_siblings[level])
        };
    }
    Ok(current)
}

/// Nullifier used by [`build_v7_pair_forest_transfer_fixture_unmined_v1`].
/// Callers use it to derive the canonical selected-lane PDA before building
/// the exact selected-lane snapshot.
pub fn deterministic_v7_pair_forest_transfer_nullifier_v1() -> Digest {
    let nullifier_key = digest(10);
    let salt = digest(100);
    pool_v1_nullifier(&nullifier_key, &salt)
}

#[allow(clippy::too_many_arguments)]
pub fn prepare_v7_pair_forest_transfer_fixture_v1(
    master_account: [u8; 32],
    checkpoint_account: [u8; 32],
    selected_lane_account: [u8; 32],
    checkpoint_sequence: u64,
    deployment_domain: [u8; 32],
    output_lane_snapshot: PoolV1PairLiveSnapshotV1,
) -> Result<PreparedV7PairForestTransferFixtureV1, V7PairForestFixtureErrorV1> {
    let input = deterministic_input_witness_v1()?;
    let recipient = PoolV1OutputNoteWitnessV1 {
        owner_key: digest(300),
        salt: digest(400),
        value: 600,
    };
    let change = PoolV1OutputNoteWitnessV1 {
        owner_key: digest(500),
        salt: digest(600),
        value: 400,
    };
    let asset_id = M31(77);
    let anchor_root = global_anchor_v1(&input)?;
    let witness = PoolV1PairForestPrivateTransferWitnessV1 {
        input,
        recipient,
        change,
    };
    let public = PoolV1PrivateTransferPublicV1 {
        pool: master_account,
        deployment_domain,
        anchor_sequence: checkpoint_sequence,
        anchor_root,
        nullifier: deterministic_v7_pair_forest_transfer_nullifier_v1(),
        asset_id,
        recipient_commitment: pool_v1_note_commitment(
            &recipient.owner_key,
            recipient.value,
            asset_id,
            &recipient.salt,
        ),
        change_commitment: pool_v1_note_commitment(
            &change.owner_key,
            change.value,
            asset_id,
            &change.salt,
        ),
    };
    let relation_context = PoolV1PaymentRelationContextV1 {
        runtime_binding: PoolV1PaymentRuntimeBindingV1 {
            pool: master_account,
            deployment_domain,
            anchor_sequence: checkpoint_sequence,
            anchor_root,
            asset_id,
        },
        spent_nullifiers: &[],
    };
    let compiled = compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
        &public,
        &witness,
        relation_context,
        output_lane_snapshot,
    )?;
    let output_lane = pool_v1_pair_forest_output_lane_v1(&public.nullifier)
        .map_err(|_| V7PairForestFixtureErrorV1::Trace(PoolV1PairTraceErrorV1::MetadataMismatch))?;
    let statement = PoolV1PairForestTerminalStatementV1::PrivateTransfer {
        common: PoolV1PairForestTerminalCommonV1 {
            master_account,
            checkpoint_account,
            selected_lane_account,
            output_lane,
            checkpoint_sequence,
            historical_global_anchor: anchor_root,
            lane_transition: compiled.public_statement,
        },
        public,
    };
    let statement_bytes = encode_pool_v1_pair_forest_terminal_statement_v1(&statement)?;
    let statement_digest = aspis_statement::pool_v1::v7_pool_pair_forest_tag73_statement_digest_v1(
        &statement_bytes,
        HOST_HASH,
    );
    Ok(PreparedV7PairForestTransferFixtureV1 {
        public,
        witness,
        transition: compiled.public_statement,
        statement,
        statement_digest,
    })
}

fn transfer_relation_context_v1(
    prepared: &PreparedV7PairForestTransferFixtureV1,
) -> PoolV1PaymentRelationContextV1<'static> {
    PoolV1PaymentRelationContextV1 {
        runtime_binding: PoolV1PaymentRuntimeBindingV1 {
            pool: prepared.public.pool,
            deployment_domain: prepared.public.deployment_domain,
            anchor_sequence: prepared.public.anchor_sequence,
            anchor_root: prepared.public.anchor_root,
            asset_id: prepared.public.asset_id,
        },
        spent_nullifiers: &[],
    }
}

#[allow(clippy::too_many_arguments)]
pub fn build_v7_pair_forest_transfer_fixture_unmined_v1(
    program_id: [u8; 32],
    attempt_id: [u8; 32],
    master_account: [u8; 32],
    checkpoint_account: [u8; 32],
    selected_lane_account: [u8; 32],
    checkpoint_sequence: u64,
    deployment_domain: [u8; 32],
    output_lane_snapshot: PoolV1PairLiveSnapshotV1,
) -> Result<BuiltV7PairForestTransferFixtureV1, V7PairForestFixtureErrorV1> {
    let prepared = prepare_v7_pair_forest_transfer_fixture_v1(
        master_account,
        checkpoint_account,
        selected_lane_account,
        checkpoint_sequence,
        deployment_domain,
        output_lane_snapshot,
    )?;
    let context = V7ProverContext {
        program_id,
        release_binding: V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
        attempt_id,
    };
    let attempt =
        StateOnlyAttemptSecrets::deterministic_spend_fixture(attempt_id, [0x4b; 32], [0x6d; 32]);
    let mut nonce_store = InMemoryStateOnlyMaskNonceStore::default();
    let proof = build_v7_pool_pair_forest_private_transfer_onefold_proof(
        &prepared.public,
        &prepared.witness,
        transfer_relation_context_v1(&prepared),
        &prepared.transition,
        prepared.statement_digest,
        context,
        attempt,
        &mut nonce_store,
        HOST_HASH,
        StateOnlyPowMode::UnminedZero,
    )?;
    Ok(BuiltV7PairForestTransferFixtureV1 {
        public: prepared.public,
        witness: prepared.witness,
        transition: prepared.transition,
        statement: prepared.statement,
        statement_digest: prepared.statement_digest,
        proof,
    })
}

/// Reproducible strict-work KAT builder. This calls the same production proof
/// entry point as an honest wallet; the containing module's fixture gate is
/// the only reason deterministic attempt entropy is available here.
#[allow(clippy::too_many_arguments)]
pub fn build_v7_pair_forest_transfer_fixture_mined_v1(
    program_id: [u8; 32],
    attempt_id: [u8; 32],
    master_account: [u8; 32],
    checkpoint_account: [u8; 32],
    selected_lane_account: [u8; 32],
    checkpoint_sequence: u64,
    deployment_domain: [u8; 32],
    output_lane_snapshot: PoolV1PairLiveSnapshotV1,
) -> Result<BuiltV7PairForestTransferFixtureV1, V7PairForestFixtureErrorV1> {
    let prepared = prepare_v7_pair_forest_transfer_fixture_v1(
        master_account,
        checkpoint_account,
        selected_lane_account,
        checkpoint_sequence,
        deployment_domain,
        output_lane_snapshot,
    )?;
    let context = V7ProverContext {
        program_id,
        release_binding: V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
        attempt_id,
    };
    let attempt =
        StateOnlyAttemptSecrets::deterministic_spend_fixture(attempt_id, [0x4b; 32], [0x6d; 32]);
    let mut nonce_store = InMemoryStateOnlyMaskNonceStore::default();
    let proof = build_v7_pool_pair_forest_private_transfer_onefold_proof_production(
        &prepared.public,
        &prepared.witness,
        transfer_relation_context_v1(&prepared),
        &prepared.transition,
        prepared.statement_digest,
        context,
        attempt,
        &mut nonce_store,
        HOST_HASH,
    )?;
    Ok(BuiltV7PairForestTransferFixtureV1 {
        public: prepared.public,
        witness: prepared.witness,
        transition: prepared.transition,
        statement: prepared.statement,
        statement_digest: prepared.statement_digest,
        proof,
    })
}
