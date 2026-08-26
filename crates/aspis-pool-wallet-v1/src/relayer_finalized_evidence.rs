//! Correlation of relayer finality with the authenticated finalized indexer.
//!
//! Signature status is only a liveness hint. A successful journal outcome is
//! derived here from the exact primary signature in a finalized `getBlock`,
//! its fee/CU metadata, and exactly one authenticated Pool lifecycle effect.

use aspis_pool::instruction::{encode_initialization_receipt_v1, encode_transition_receipt_v1};
use aspis_statement::pool_v1::PoolV1TransitionKind;
use sha2::{Digest as _, Sha256};

use crate::{
    finalized_indexer::{FinalizedBlockIngestResultV1, FinalizedTransitionEvidenceV1},
    pool_transport::{
        AuthenticatedCancelledSettlementV1, AuthenticatedInitializationV1,
        AuthenticatedPreparedSettlementPlanIdentityV1, AuthenticatedPreparedSettlementV1,
    },
    relayer::{RelayerPlanV1, RelayerRequestKindV1},
    relayer_execution_journal::RelayerFinalizedEvidenceV1,
    rpc_json::FinalizedTransactionExecutionV1,
    scan_state::DepositEventIdV1,
};

pub const RELAYER_EXECUTION_RESULT_DOMAIN_V1: &[u8] =
    b"aspis:pool-v1:relayer-finalized-execution:sha256:v1";
pub const RELAYER_POSTSTATE_DOMAIN_V1: &[u8] =
    b"aspis:pool-v1:relayer-authenticated-poststate:sha256:v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerFinalizedEvidenceErrorV1 {
    ZeroProviderSetDigest,
    MissingLifecycleEvidence,
    MultipleLifecycleEvidence,
    WrongLifecycleEvidence,
    WrongTransitionKind,
    WrongPreparedPlan,
    WrongAuthenticatedTransport,
    CountOverflow,
}

pub fn derive_relayer_finalized_evidence_v1(
    plan: &RelayerPlanV1,
    execution: FinalizedTransactionExecutionV1,
    result: &FinalizedBlockIngestResultV1,
    provider_set_digest: [u8; 32],
) -> Result<RelayerFinalizedEvidenceV1, RelayerFinalizedEvidenceErrorV1> {
    if provider_set_digest == [0u8; 32] {
        return Err(RelayerFinalizedEvidenceErrorV1::ZeroProviderSetDigest);
    }
    let mut poststate = Sha256::new();
    poststate.update(RELAYER_POSTSTATE_DOMAIN_V1);
    poststate.update(plan.request_id);
    poststate.update([request_kind_byte_v1(plan.kind)]);
    poststate.update(execution.point().slot().to_le_bytes());
    poststate.update(execution.point().block_hash());
    poststate.update(execution.transaction_signature());
    hash_exact_plan_v1(&mut poststate, plan)?;

    match plan.kind {
        RelayerRequestKindV1::Initialize => {
            let initialization = exactly_one_v1(
                result
                    .initializations
                    .iter()
                    .filter(|item| event_matches_execution_v1(&item.id, execution)),
            )?;
            if plan
                .instruction
                .accounts
                .get(1)
                .map(|meta| meta.pubkey.to_bytes())
                != Some(initialization.receipt.pool)
                || plan
                    .instruction
                    .accounts
                    .get(2)
                    .map(|meta| meta.pubkey.to_bytes())
                    != Some(initialization.receipt.root_page_zero)
                || plan
                    .instruction
                    .accounts
                    .get(4)
                    .map(|meta| meta.pubkey.to_bytes())
                    != Some(initialization.receipt.vault_token_account)
            {
                return Err(RelayerFinalizedEvidenceErrorV1::WrongLifecycleEvidence);
            }
            hash_initialization_v1(&mut poststate, initialization);
        }
        RelayerRequestKindV1::Deposit => {
            let id = exactly_one_v1(
                result
                    .deposit_event_ids
                    .iter()
                    .filter(|id| event_matches_execution_v1(id, execution)),
            )?;
            let append = exactly_one_v1(
                result
                    .append_evidence
                    .iter()
                    .filter(|append| append.event_id == *id),
            )?;
            let root = exactly_one_v1(
                result
                    .root_evidence
                    .iter()
                    .filter(|root| root.event_id == *id),
            )?;
            if append.root_sequence != root.root_sequence || append.root != root.root {
                return Err(RelayerFinalizedEvidenceErrorV1::WrongLifecycleEvidence);
            }
            hash_event_id_v1(&mut poststate, id);
            poststate.update(append.leaf_index.to_le_bytes());
            poststate.update(append.root_sequence.to_le_bytes());
            poststate.update(append.note_commitment);
            poststate.update(append.root);
            poststate.update(root.page_number.to_le_bytes());
            poststate.update(root.page_address);
            poststate.update(root.snapshot_context_slot.to_le_bytes());
        }
        RelayerRequestKindV1::PrepareSettlement => {
            let prepared = exactly_one_v1(
                result
                    .prepared_settlements
                    .iter()
                    .filter(|item| event_matches_execution_v1(&item.id, execution)),
            )?;
            hash_prepared_v1(&mut poststate, prepared);
        }
        RelayerRequestKindV1::CancelPrepared => {
            let cancelled = exactly_one_v1(
                result
                    .cancelled_settlements
                    .iter()
                    .filter(|item| event_matches_execution_v1(&item.id, execution)),
            )?;
            require_prepared_identity_v1(
                plan,
                cancelled.plan_authority,
                cancelled.core_plan,
                cancelled.rollover_shard,
            )?;
            hash_cancelled_v1(&mut poststate, cancelled);
        }
        RelayerRequestKindV1::PrivateTransfer
        | RelayerRequestKindV1::Withdrawal
        | RelayerRequestKindV1::SettlePrepared => {
            let transition = exactly_one_v1(result.transition_evidence.iter().filter(|item| {
                item.output_ids
                    .first()
                    .is_some_and(|id| event_matches_execution_v1(id, execution))
            }))?;
            validate_transition_v1(plan, transition)?;
            hash_transition_v1(&mut poststate, transition)?;
        }
    }
    let poststate_sha256: [u8; 32] = poststate.finalize().into();

    let mut execution_result = Sha256::new();
    execution_result.update(RELAYER_EXECUTION_RESULT_DOMAIN_V1);
    execution_result.update(plan.request_id);
    execution_result.update(execution.point().slot().to_le_bytes());
    execution_result.update(execution.point().block_hash());
    execution_result.update(execution.transaction_signature());
    execution_result.update(execution.fee_lamports().to_le_bytes());
    execution_result.update(execution.compute_units_consumed().to_le_bytes());
    execution_result.update(poststate_sha256);

    Ok(RelayerFinalizedEvidenceV1 {
        point: execution.point(),
        fee_lamports: execution.fee_lamports(),
        compute_units_consumed: execution.compute_units_consumed(),
        execution_result_sha256: execution_result.finalize().into(),
        poststate_sha256,
        provider_set_digest,
    })
}

fn exactly_one_v1<'a, T>(
    mut values: impl Iterator<Item = &'a T>,
) -> Result<&'a T, RelayerFinalizedEvidenceErrorV1> {
    let first = values
        .next()
        .ok_or(RelayerFinalizedEvidenceErrorV1::MissingLifecycleEvidence)?;
    if values.next().is_some() {
        return Err(RelayerFinalizedEvidenceErrorV1::MultipleLifecycleEvidence);
    }
    Ok(first)
}

fn event_matches_execution_v1(
    id: &DepositEventIdV1,
    execution: FinalizedTransactionExecutionV1,
) -> bool {
    id.point() == execution.point()
        && id.transaction_signature() == execution.transaction_signature()
}

fn request_kind_byte_v1(kind: RelayerRequestKindV1) -> u8 {
    match kind {
        RelayerRequestKindV1::Initialize => 0,
        RelayerRequestKindV1::Deposit => 1,
        RelayerRequestKindV1::PrepareSettlement => 2,
        RelayerRequestKindV1::SettlePrepared => 3,
        RelayerRequestKindV1::CancelPrepared => 4,
        RelayerRequestKindV1::PrivateTransfer => 5,
        RelayerRequestKindV1::Withdrawal => 6,
    }
}

fn hash_exact_plan_v1(
    hasher: &mut Sha256,
    plan: &RelayerPlanV1,
) -> Result<(), RelayerFinalizedEvidenceErrorV1> {
    hasher.update(plan.snapshot.pinned_program_id.as_ref());
    hasher.update(plan.snapshot.registry_program.as_ref());
    hasher.update(plan.snapshot.current_root_sequence.to_le_bytes());
    hasher.update(plan.snapshot.observed_slot.to_le_bytes());
    hasher.update(plan.snapshot.pool_state_sha256);
    hasher.update(plan.fee_payer.as_ref());
    hasher.update(
        u16::try_from(plan.instruction.accounts.len())
            .map_err(|_| RelayerFinalizedEvidenceErrorV1::CountOverflow)?
            .to_le_bytes(),
    );
    for account in &plan.instruction.accounts {
        hasher.update(account.pubkey.as_ref());
        hasher.update([u8::from(account.is_signer), u8::from(account.is_writable)]);
    }
    hasher.update(
        u32::try_from(plan.instruction.data.len())
            .map_err(|_| RelayerFinalizedEvidenceErrorV1::CountOverflow)?
            .to_le_bytes(),
    );
    hasher.update(&plan.instruction.data);
    Ok(())
}

fn hash_event_id_v1(hasher: &mut Sha256, id: &DepositEventIdV1) {
    hasher.update(id.point().slot().to_le_bytes());
    hasher.update(id.point().block_hash());
    hasher.update(id.transaction_signature());
    hasher.update(id.instruction_index().to_le_bytes());
    hasher.update(id.event_index().to_le_bytes());
}

fn hash_initialization_v1(hasher: &mut Sha256, value: &AuthenticatedInitializationV1) {
    hash_event_id_v1(hasher, &value.id);
    let bytes = encode_initialization_receipt_v1(
        &value.receipt.pool.into(),
        &value.receipt.root_page_zero.into(),
        &value.receipt.vault_token_account.into(),
    );
    hasher.update(bytes);
}

fn hash_prepared_v1(hasher: &mut Sha256, value: &AuthenticatedPreparedSettlementV1) {
    hash_event_id_v1(hasher, &value.id);
    hasher.update([value.transition_kind as u8]);
    hasher.update(value.source_root_sequence.to_le_bytes());
    hasher.update(value.not_before_slot.to_le_bytes());
    hasher.update(value.expires_at_slot.to_le_bytes());
    hasher.update(value.plan_authority);
    hasher.update(value.authorization_receipt);
    hasher.update(value.verifier_registry);
    hasher.update(value.verifier_entry);
    hasher.update(value.verifier_profile);
    hasher.update(value.verifier_release);
    hasher.update(value.core_plan);
    hash_optional_pubkey_v1(hasher, value.rollover_page);
    hash_optional_pubkey_v1(hasher, value.rollover_shard);
}

fn hash_cancelled_v1(hasher: &mut Sha256, value: &AuthenticatedCancelledSettlementV1) {
    hash_event_id_v1(hasher, &value.id);
    hasher.update(value.plan_authority);
    hasher.update(value.core_plan);
    hash_optional_pubkey_v1(hasher, value.rollover_shard);
}

fn hash_optional_pubkey_v1(hasher: &mut Sha256, value: Option<[u8; 32]>) {
    match value {
        Some(value) => {
            hasher.update([1]);
            hasher.update(value);
        }
        None => hasher.update([0]),
    }
}

fn validate_transition_v1(
    plan: &RelayerPlanV1,
    transition: &FinalizedTransitionEvidenceV1,
) -> Result<(), RelayerFinalizedEvidenceErrorV1> {
    let expected_kind = match plan.kind {
        RelayerRequestKindV1::PrivateTransfer => PoolV1TransitionKind::PrivateTransfer,
        RelayerRequestKindV1::Withdrawal => PoolV1TransitionKind::Withdrawal,
        RelayerRequestKindV1::SettlePrepared => {
            plan.prepared_plan
                .ok_or(RelayerFinalizedEvidenceErrorV1::WrongPreparedPlan)?
                .transition_kind
        }
        _ => return Err(RelayerFinalizedEvidenceErrorV1::WrongTransitionKind),
    };
    if transition.receipt.transition_kind != expected_kind || transition.output_ids.is_empty() {
        return Err(RelayerFinalizedEvidenceErrorV1::WrongTransitionKind);
    }
    let receipt = encode_transition_receipt_v1(&transition.receipt)
        .map_err(|_| RelayerFinalizedEvidenceErrorV1::WrongAuthenticatedTransport)?;
    let expected_length = plan
        .instruction
        .data
        .len()
        .checked_add(receipt.len())
        .ok_or(RelayerFinalizedEvidenceErrorV1::CountOverflow)?;
    if transition.authenticated_transport.len() != expected_length
        || !transition
            .authenticated_transport
            .starts_with(&plan.instruction.data)
        || !transition.authenticated_transport.ends_with(&receipt)
    {
        return Err(RelayerFinalizedEvidenceErrorV1::WrongAuthenticatedTransport);
    }
    match plan.kind {
        RelayerRequestKindV1::SettlePrepared => {
            let settled = transition
                .settled_plan
                .ok_or(RelayerFinalizedEvidenceErrorV1::WrongPreparedPlan)?;
            require_prepared_identity_v1(
                plan,
                settled.plan_authority,
                settled.core_plan,
                settled.rollover_shard,
            )?;
        }
        _ if transition.settled_plan.is_some() => {
            return Err(RelayerFinalizedEvidenceErrorV1::WrongPreparedPlan)
        }
        _ => {}
    }
    Ok(())
}

fn require_prepared_identity_v1(
    plan: &RelayerPlanV1,
    plan_authority: [u8; 32],
    core_plan: [u8; 32],
    rollover_shard: Option<[u8; 32]>,
) -> Result<(), RelayerFinalizedEvidenceErrorV1> {
    let expected = plan
        .prepared_plan
        .ok_or(RelayerFinalizedEvidenceErrorV1::WrongPreparedPlan)?;
    if expected.plan_authority.to_bytes() != plan_authority
        || expected.core_plan.to_bytes() != core_plan
        || expected.rollover_shard.map(|value| value.to_bytes()) != rollover_shard
    {
        return Err(RelayerFinalizedEvidenceErrorV1::WrongPreparedPlan);
    }
    Ok(())
}

fn hash_transition_v1(
    hasher: &mut Sha256,
    value: &FinalizedTransitionEvidenceV1,
) -> Result<(), RelayerFinalizedEvidenceErrorV1> {
    hasher.update(
        u32::try_from(value.output_ids.len())
            .map_err(|_| RelayerFinalizedEvidenceErrorV1::CountOverflow)?
            .to_le_bytes(),
    );
    for id in &value.output_ids {
        hash_event_id_v1(hasher, id);
    }
    hasher.update(
        u32::try_from(value.authenticated_transport.len())
            .map_err(|_| RelayerFinalizedEvidenceErrorV1::CountOverflow)?
            .to_le_bytes(),
    );
    hasher.update(&value.authenticated_transport);
    match value.settled_plan {
        Some(identity) => {
            hasher.update([1]);
            hash_prepared_identity_v1(hasher, identity);
        }
        None => hasher.update([0]),
    }
    Ok(())
}

fn hash_prepared_identity_v1(
    hasher: &mut Sha256,
    identity: AuthenticatedPreparedSettlementPlanIdentityV1,
) {
    hasher.update(identity.plan_authority);
    hasher.update(identity.core_plan);
    hash_optional_pubkey_v1(hasher, identity.rollover_shard);
}

#[cfg(test)]
mod tests {
    use aspis_core::field::M31;
    use aspis_pool::{PoolInitializationV1, LEGACY_SPL_TOKEN_PROGRAM_ID};
    use aspis_statement::pool_v1::{
        VerifierPolicyV1, POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY,
    };
    use solana_program::pubkey::Pubkey;

    use super::*;
    use crate::{
        finalized_indexer::FinalizedBlockIngestResultV1,
        pool_transport::InitializationReceiptV1,
        relayer::{prepare_permissionless_relayer_plan_v1, RelayerSnapshotV1},
        scan_state::{DepositEventIdV1, FinalizedBlockAdvanceV1, FinalizedChainPointV1},
        transaction_builder::build_initialize_instruction_v1,
    };

    fn key(seed: u8) -> Pubkey {
        Pubkey::new_from_array([seed; 32])
    }

    fn fixture() -> (
        RelayerPlanV1,
        FinalizedTransactionExecutionV1,
        FinalizedBlockIngestResultV1,
    ) {
        let program_id = key(1);
        let payer = key(2);
        let mint = key(3);
        let registry_program = key(4);
        let initialization = PoolInitializationV1 {
            asset_mint: mint.to_bytes(),
            token_program: LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
            asset_id: M31(9),
            deployment_domain: [0x31; 32],
            verifier_policy: VerifierPolicyV1 {
                flags: POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY,
                registry_program: registry_program.to_bytes(),
                registry_authority: [0; 32],
                policy_binding: [0x33; 32],
            },
        };
        let instruction =
            build_initialize_instruction_v1(program_id, payer, &initialization).unwrap();
        let plan = prepare_permissionless_relayer_plan_v1(
            RelayerSnapshotV1 {
                pinned_program_id: program_id,
                registry_program,
                current_root_sequence: 0,
                observed_slot: 90,
                pool_state_sha256: [0x41; 32],
            },
            payer,
            &instruction,
        )
        .unwrap();
        let point = FinalizedChainPointV1::new(100, [0x51; 32]).unwrap();
        let signature = [0x61; 64];
        let execution =
            FinalizedTransactionExecutionV1::test_only_v1(point, signature, 5_000, 88_000);
        let id = DepositEventIdV1::new(point, signature, 1, 0).unwrap();
        let result = FinalizedBlockIngestResultV1 {
            advance: FinalizedBlockAdvanceV1::Advanced,
            rollback: None,
            deposit_event_ids: Vec::new(),
            deposit_outcomes: Vec::new(),
            transition_outcomes: Vec::new(),
            transition_evidence: Vec::new(),
            initializations: vec![AuthenticatedInitializationV1 {
                id,
                receipt: InitializationReceiptV1 {
                    pool: instruction.accounts[1].pubkey.to_bytes(),
                    root_page_zero: instruction.accounts[2].pubkey.to_bytes(),
                    vault_token_account: instruction.accounts[4].pubkey.to_bytes(),
                },
            }],
            append_evidence: Vec::new(),
            prepared_settlements: Vec::new(),
            cancelled_settlements: Vec::new(),
            plan_lifecycle: Vec::new(),
            root_evidence: Vec::new(),
            ignored_failed_pool_transactions: 0,
        };
        (plan, execution, result)
    }

    #[test]
    fn finalized_initialization_binds_exact_signature_metadata_and_pool_poststate() {
        let (plan, execution, result) = fixture();
        let evidence =
            derive_relayer_finalized_evidence_v1(&plan, execution, &result, [0x71; 32]).unwrap();
        assert_eq!(evidence.point, execution.point());
        assert_eq!(evidence.fee_lamports, 5_000);
        assert_eq!(evidence.compute_units_consumed, 88_000);
        assert_ne!(evidence.execution_result_sha256, [0u8; 32]);
        assert_ne!(evidence.poststate_sha256, [0u8; 32]);

        let mut wrong = result;
        wrong.initializations[0].receipt.pool = [0x72; 32];
        assert_eq!(
            derive_relayer_finalized_evidence_v1(&plan, execution, &wrong, [0x71; 32]),
            Err(RelayerFinalizedEvidenceErrorV1::WrongLifecycleEvidence)
        );
    }
}
