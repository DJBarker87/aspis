//! Restart-safe relayer execution and reconciliation coordinator.
//!
//! This module owns the ordering across the durable admission queue and the
//! execution journal. Network transport and signer custody are explicit ports,
//! but the coordinator never submits before the exact signed wire has been
//! verified and fsync/rename committed. Each call advances at most one durable
//! or external transition so a process crash at every boundary is replayable.

use crate::{
    durable_state::{DurableRelayerStateV1, DurableRelayerStatusV1, DurableStateErrorV1},
    operator_startup::OperatorStartupReceiptV1,
    relayer::{relayer_policy_id_v1, RelayerPlanV1, RelayerPolicyV1},
    relayer_execution_journal::{
        DurableRelayerExecutionJournalV1, RelayerExecutionJournalErrorV1,
        RelayerFinalizedEvidenceV1, RelayerSimulationEvidenceV1, RelayerSubmissionEvidenceV1,
        RelayerTerminalFailureEvidenceV1, SolanaSdkSignedTransactionInspectorV1,
    },
};

pub const RELAYER_TERMINAL_BLOCKHASH_EXPIRED_V1: u32 = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelayerExecutionContextV1 {
    pub now_slot: u64,
    pub estimated_fee_lamports: u64,
    pub fee_payer_balance_lamports: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerSignatureObservationV1 {
    /// The signature is known but has not reached finalized commitment.
    Pending { provider_set_digest: [u8; 32] },
    /// Every pinned provider returned not-found at this block height.
    NotFound {
        observed_block_height: u64,
        evidence_sha256: [u8; 32],
        provider_set_digest: [u8; 32],
    },
    /// Finalized status and poststate were obtained from the pinned providers.
    Finalized(RelayerFinalizedEvidenceV1),
}

/// Production ports must assemble the exact canonical transaction represented
/// by `plan`, simulate that same unsigned message, and ask the external signer
/// to sign only that message. The returned signed wire is independently parsed
/// and signature-verified before it can reach `submit_exact_signed_wire_v1`.
/// A restart must rebuild the unsigned message from the durable plan and
/// simulation evidence; its SHA-256 must therefore remain identical.
pub trait RelayerExecutionPortV1 {
    type Error;

    fn simulate_exact_plan_v1(
        &mut self,
        plan: &RelayerPlanV1,
        startup: &OperatorStartupReceiptV1,
    ) -> Result<RelayerSimulationEvidenceV1, Self::Error>;

    fn sign_exact_simulated_plan_v1(
        &mut self,
        plan: &RelayerPlanV1,
        simulation: RelayerSimulationEvidenceV1,
    ) -> Result<Vec<u8>, Self::Error>;

    fn observe_signature_v1(
        &mut self,
        transaction_signature: [u8; 64],
        startup: &OperatorStartupReceiptV1,
    ) -> Result<RelayerSignatureObservationV1, Self::Error>;

    fn submit_exact_signed_wire_v1(
        &mut self,
        transaction_signature: [u8; 64],
        signed_wire: &[u8],
        startup: &OperatorStartupReceiptV1,
    ) -> Result<RelayerSubmissionEvidenceV1, Self::Error>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerExecutionStepV1 {
    InflightMarked,
    SimulationRecorded,
    SignedWireRecorded,
    Submitted,
    Resubmitted,
    SubmissionSuppressedByPolicy,
    AwaitingFinality,
    FinalOutcomeRecorded,
    QueueCompleted,
    AlreadyCompleted,
}

#[derive(Debug, PartialEq, Eq)]
pub enum RelayerOperatorExecutionErrorV1<E> {
    Durable(DurableStateErrorV1),
    Journal(RelayerExecutionJournalErrorV1),
    Runtime(E),
    UnknownRequest,
    CrossStoreMismatch,
    StartupReceiptMismatch,
    PlanBeforeStartupCheckpoint,
    PolicyChangedBeforeSigning,
    InvalidRuntimeEvidence,
    ProviderSetMismatch,
}

/// Advance one request by exactly one restart boundary.
///
/// The caller repeatedly invokes this function until it returns
/// `QueueCompleted`, `AlreadyCompleted`, `AwaitingFinality`, or
/// `SubmissionSuppressedByPolicy`. The strict order is queue inflight →
/// successful simulation → verified signed wire → signature
/// observation/submission → durable final outcome → queue removal.
pub fn advance_relayer_execution_v1<R: RelayerExecutionPortV1>(
    queue: &mut DurableRelayerStateV1,
    journal: &mut DurableRelayerExecutionJournalV1,
    policy: RelayerPolicyV1,
    context: RelayerExecutionContextV1,
    request_id: [u8; 32],
    startup: &OperatorStartupReceiptV1,
    runtime: &mut R,
) -> Result<RelayerExecutionStepV1, RelayerOperatorExecutionErrorV1<R::Error>> {
    let existing_record = journal.record_v1(request_id).cloned();
    let Some(entry) = queue
        .entries()
        .iter()
        .find(|entry| entry.plan.request_id == request_id)
        .cloned()
    else {
        return match existing_record {
            Some(record) if record.outcome.is_some() => {
                Ok(RelayerExecutionStepV1::AlreadyCompleted)
            }
            Some(_) => Err(RelayerOperatorExecutionErrorV1::CrossStoreMismatch),
            None => Err(RelayerOperatorExecutionErrorV1::UnknownRequest),
        };
    };

    if let Some(record) = &existing_record {
        if record.outcome.is_some() {
            if entry.status != DurableRelayerStatusV1::Inflight {
                return Err(RelayerOperatorExecutionErrorV1::CrossStoreMismatch);
            }
            queue
                .complete_inflight_v1(request_id)
                .map_err(RelayerOperatorExecutionErrorV1::Durable)?;
            return Ok(RelayerExecutionStepV1::QueueCompleted);
        }
    }

    validate_startup_receipt_shape_v1(startup)?;

    if entry.status == DurableRelayerStatusV1::Queued {
        validate_plan_checkpoint_v1(startup, &entry.plan)?;
        if existing_record.is_some() {
            return Err(RelayerOperatorExecutionErrorV1::CrossStoreMismatch);
        }
        queue
            .mark_inflight_v1(
                policy,
                request_id,
                context.now_slot,
                context.estimated_fee_lamports,
                context.fee_payer_balance_lamports,
            )
            .map_err(RelayerOperatorExecutionErrorV1::Durable)?;
        return Ok(RelayerExecutionStepV1::InflightMarked);
    }

    let Some(record) = existing_record else {
        validate_plan_checkpoint_v1(startup, &entry.plan)?;
        let simulation = runtime
            .simulate_exact_plan_v1(&entry.plan, startup)
            .map_err(RelayerOperatorExecutionErrorV1::Runtime)?;
        validate_simulation_evidence_v1(startup, &entry.plan, context, simulation)?;
        journal
            .record_simulation_v1(request_id, relayer_policy_id_v1(policy), simulation)
            .map_err(RelayerOperatorExecutionErrorV1::Journal)?;
        return Ok(RelayerExecutionStepV1::SimulationRecorded);
    };

    if record.signed.is_none() {
        validate_plan_checkpoint_v1(startup, &entry.plan)?;
        if record.simulation.startup_receipt_digest != *startup.receipt_digest() {
            return Err(RelayerOperatorExecutionErrorV1::StartupReceiptMismatch);
        }
        if record.policy_id != relayer_policy_id_v1(policy) {
            return Err(RelayerOperatorExecutionErrorV1::PolicyChangedBeforeSigning);
        }
        let signed_wire = runtime
            .sign_exact_simulated_plan_v1(&entry.plan, record.simulation)
            .map_err(RelayerOperatorExecutionErrorV1::Runtime)?;
        journal
            .record_signed_wire_v1(
                request_id,
                &signed_wire,
                &SolanaSdkSignedTransactionInspectorV1,
            )
            .map_err(RelayerOperatorExecutionErrorV1::Journal)?;
        return Ok(RelayerExecutionStepV1::SignedWireRecorded);
    }

    let Some(signed) = record.signed.as_ref() else {
        return Err(RelayerOperatorExecutionErrorV1::CrossStoreMismatch);
    };
    let observation = runtime
        .observe_signature_v1(signed.transaction_signature, startup)
        .map_err(RelayerOperatorExecutionErrorV1::Runtime)?;
    match observation {
        RelayerSignatureObservationV1::Pending {
            provider_set_digest,
        } => {
            validate_provider_set_v1(startup, provider_set_digest)?;
            Ok(RelayerExecutionStepV1::AwaitingFinality)
        }
        RelayerSignatureObservationV1::Finalized(finalized) => {
            validate_provider_set_v1(startup, finalized.provider_set_digest)?;
            journal
                .record_finalized_v1(request_id, signed.transaction_signature, finalized)
                .map_err(RelayerOperatorExecutionErrorV1::Journal)?;
            Ok(RelayerExecutionStepV1::FinalOutcomeRecorded)
        }
        RelayerSignatureObservationV1::NotFound {
            observed_block_height,
            evidence_sha256,
            provider_set_digest,
        } => {
            validate_provider_set_v1(startup, provider_set_digest)?;
            if observed_block_height == 0 || evidence_sha256 == [0u8; 32] {
                return Err(RelayerOperatorExecutionErrorV1::InvalidRuntimeEvidence);
            }
            if observed_block_height > record.simulation.last_valid_block_height {
                journal
                    .record_terminal_failure_v1(
                        request_id,
                        RelayerTerminalFailureEvidenceV1 {
                            observed_block_height,
                            failure_code: RELAYER_TERMINAL_BLOCKHASH_EXPIRED_V1,
                            evidence_sha256,
                            provider_set_digest,
                        },
                    )
                    .map_err(RelayerOperatorExecutionErrorV1::Journal)?;
                return Ok(RelayerExecutionStepV1::FinalOutcomeRecorded);
            }
            if policy.paused || record.policy_id != relayer_policy_id_v1(policy) {
                return Ok(RelayerExecutionStepV1::SubmissionSuppressedByPolicy);
            }

            let submission = runtime
                .submit_exact_signed_wire_v1(
                    signed.transaction_signature,
                    &signed.signed_wire,
                    startup,
                )
                .map_err(RelayerOperatorExecutionErrorV1::Runtime)?;
            validate_provider_set_v1(startup, submission.provider_set_digest)?;
            if submission.submitted_at_slot < record.simulation.simulated_at_slot {
                return Err(RelayerOperatorExecutionErrorV1::InvalidRuntimeEvidence);
            }
            if record.submission.is_none() {
                journal
                    .record_submission_v1(request_id, signed.transaction_signature, submission)
                    .map_err(RelayerOperatorExecutionErrorV1::Journal)?;
                Ok(RelayerExecutionStepV1::Submitted)
            } else {
                Ok(RelayerExecutionStepV1::Resubmitted)
            }
        }
    }
}

fn validate_startup_receipt_shape_v1<E>(
    startup: &OperatorStartupReceiptV1,
) -> Result<(), RelayerOperatorExecutionErrorV1<E>> {
    if startup.manifest_digest() == &[0u8; 32]
        || startup.provider_set_digest() == &[0u8; 32]
        || startup.receipt_digest() == &[0u8; 32]
    {
        return Err(RelayerOperatorExecutionErrorV1::StartupReceiptMismatch);
    }
    Ok(())
}

fn validate_plan_checkpoint_v1<E>(
    startup: &OperatorStartupReceiptV1,
    plan: &RelayerPlanV1,
) -> Result<(), RelayerOperatorExecutionErrorV1<E>> {
    let checkpoint = startup.checkpoint();
    if plan.snapshot.observed_slot < checkpoint.point.slot()
        || plan.snapshot.current_root_sequence < checkpoint.root_sequence
    {
        return Err(RelayerOperatorExecutionErrorV1::PlanBeforeStartupCheckpoint);
    }
    Ok(())
}

fn validate_simulation_evidence_v1<E>(
    startup: &OperatorStartupReceiptV1,
    plan: &RelayerPlanV1,
    context: RelayerExecutionContextV1,
    simulation: RelayerSimulationEvidenceV1,
) -> Result<(), RelayerOperatorExecutionErrorV1<E>> {
    if simulation.startup_receipt_digest != *startup.receipt_digest()
        || simulation.simulated_at_slot < startup.checkpoint().point.slot()
        || simulation.simulated_at_slot < plan.snapshot.observed_slot
        || simulation.fee_payer != plan.fee_payer.to_bytes()
        || simulation.estimated_fee_lamports != context.estimated_fee_lamports
    {
        return Err(RelayerOperatorExecutionErrorV1::InvalidRuntimeEvidence);
    }
    Ok(())
}

fn validate_provider_set_v1<E>(
    startup: &OperatorStartupReceiptV1,
    provider_set_digest: [u8; 32],
) -> Result<(), RelayerOperatorExecutionErrorV1<E>> {
    if provider_set_digest == [0u8; 32] || provider_set_digest != *startup.provider_set_digest() {
        return Err(RelayerOperatorExecutionErrorV1::ProviderSetMismatch);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::{
        collections::VecDeque,
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };

    use aspis_core::field::M31;
    use aspis_pool::{deposit::DepositRequestV1, pool_v1_state_address};
    use aspis_statement::poseidon2::Digest;
    use sha2::{Digest as _, Sha256};
    use solana_program::pubkey::Pubkey;

    use super::*;
    use crate::{
        operator_startup::FinalizedReleaseCheckpointV1,
        relayer::{prepare_permissionless_relayer_plan_v1, RelayerSnapshotV1},
        relayer_execution_journal::RelayerExecutionOutcomeV1,
        scan_state::FinalizedChainPointV1,
        transaction_builder::build_deposit_instruction_v1,
    };

    static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    struct TestDirectory(std::path::PathBuf);

    impl TestDirectory {
        fn new() -> Self {
            let serial = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "aspis-operator-execution-{}-{}",
                std::process::id(),
                serial
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn key(seed: u8) -> Pubkey {
        Pubkey::new_from_array([seed; 32])
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn signed_wire() -> (Vec<u8>, [u8; 32], [u8; 32], [u8; 64]) {
        let fee_payer = [
            49, 222, 190, 85, 211, 124, 114, 39, 104, 177, 55, 19, 28, 170, 96, 135, 8, 11, 46, 11,
            96, 185, 75, 215, 133, 209, 69, 117, 207, 164, 152, 188,
        ];
        let signature = [
            2, 0, 58, 29, 54, 47, 159, 159, 182, 228, 68, 52, 6, 68, 92, 201, 145, 37, 112, 106,
            212, 97, 236, 215, 222, 166, 5, 122, 85, 202, 178, 51, 233, 46, 100, 243, 212, 11, 88,
            51, 39, 138, 120, 228, 232, 127, 204, 152, 227, 118, 45, 118, 113, 67, 152, 14, 170,
            216, 59, 170, 209, 6, 116, 14,
        ];
        let mut message = Vec::new();
        message.extend_from_slice(&[1, 0, 1, 2]);
        message.extend_from_slice(&fee_payer);
        message.extend_from_slice(&[0x29; 32]);
        message.extend_from_slice(&[0x39; 32]);
        message.extend_from_slice(&[1, 1, 1, 0, 0]);
        let mut wire = Vec::new();
        wire.push(1);
        wire.extend_from_slice(&signature);
        wire.extend_from_slice(&message);
        (wire, fee_payer, Sha256::digest(&message).into(), signature)
    }

    fn fixture() -> (
        RelayerPlanV1,
        RelayerPolicyV1,
        OperatorStartupReceiptV1,
        RelayerExecutionContextV1,
    ) {
        let (.., fee_payer, _, _) = signed_wire();
        let program_id = key(1);
        let mint = key(2);
        let pool = pool_v1_state_address(&program_id, &mint).0;
        let request = DepositRequestV1 {
            owner_key: digest(10),
            amount: 77,
            salt: digest(20),
            encrypted_note_payload: &[],
        };
        let instruction =
            build_deposit_instruction_v1(program_id, pool, mint, 7, key(3), key(4), None, &request)
                .unwrap();
        let snapshot = RelayerSnapshotV1 {
            pinned_program_id: program_id,
            registry_program: key(5),
            current_root_sequence: 7,
            observed_slot: 900,
            pool_state_sha256: [0xab; 32],
        };
        let plan = prepare_permissionless_relayer_plan_v1(
            snapshot,
            Pubkey::new_from_array(fee_payer),
            &instruction,
        )
        .unwrap();
        let policy = RelayerPolicyV1 {
            paused: false,
            operator_fee_payer: plan.fee_payer,
            allow_initialize: false,
            allow_deposit: true,
            allow_prepare_settlement: true,
            allow_settle_prepared: true,
            allow_cancel_prepared: true,
            allow_private_transfer: true,
            allow_withdrawal: true,
            max_snapshot_age_slots: 32,
            max_queue_depth: 64,
            max_inflight: 4,
            rate_window_slots: 16,
            max_admissions_per_window: 8,
            max_estimated_fee_lamports: 20_000,
            minimum_fee_payer_reserve_lamports: 1_000_000,
        };
        let checkpoint = FinalizedReleaseCheckpointV1 {
            point: FinalizedChainPointV1::new(900, [0x91; 32]).unwrap(),
            pool_state_sha256: snapshot.pool_state_sha256,
            root_sequence: snapshot.current_root_sequence,
            root: [0x92; 32],
        };
        let startup = OperatorStartupReceiptV1::test_only_v1([0x93; 32], [0x94; 32], checkpoint);
        let context = RelayerExecutionContextV1 {
            now_slot: 901,
            estimated_fee_lamports: 10_000,
            fee_payer_balance_lamports: 2_000_000,
        };
        (plan, policy, startup, context)
    }

    struct Runtime {
        simulation: RelayerSimulationEvidenceV1,
        signed_wire: Vec<u8>,
        observations: VecDeque<RelayerSignatureObservationV1>,
        submitted_wires: Vec<Vec<u8>>,
    }

    impl RelayerExecutionPortV1 for Runtime {
        type Error = ();

        fn simulate_exact_plan_v1(
            &mut self,
            _plan: &RelayerPlanV1,
            _startup: &OperatorStartupReceiptV1,
        ) -> Result<RelayerSimulationEvidenceV1, Self::Error> {
            Ok(self.simulation)
        }

        fn sign_exact_simulated_plan_v1(
            &mut self,
            _plan: &RelayerPlanV1,
            _simulation: RelayerSimulationEvidenceV1,
        ) -> Result<Vec<u8>, Self::Error> {
            Ok(self.signed_wire.clone())
        }

        fn observe_signature_v1(
            &mut self,
            _transaction_signature: [u8; 64],
            _startup: &OperatorStartupReceiptV1,
        ) -> Result<RelayerSignatureObservationV1, Self::Error> {
            self.observations.pop_front().ok_or(())
        }

        fn submit_exact_signed_wire_v1(
            &mut self,
            _transaction_signature: [u8; 64],
            signed_wire: &[u8],
            _startup: &OperatorStartupReceiptV1,
        ) -> Result<RelayerSubmissionEvidenceV1, Self::Error> {
            self.submitted_wires.push(signed_wire.to_vec());
            Ok(RelayerSubmissionEvidenceV1 {
                submitted_at_slot: 902,
                provider_set_digest: [0x94; 32],
            })
        }
    }

    fn advance_after_restart(
        queue_path: &std::path::Path,
        journal_path: &std::path::Path,
        policy: RelayerPolicyV1,
        context: RelayerExecutionContextV1,
        request_id: [u8; 32],
        startup: &OperatorStartupReceiptV1,
        runtime: &mut Runtime,
    ) -> Result<RelayerExecutionStepV1, RelayerOperatorExecutionErrorV1<()>> {
        let mut queue = DurableRelayerStateV1::open_or_create_v1(queue_path, policy).unwrap();
        let mut journal =
            DurableRelayerExecutionJournalV1::open_or_create_v1(journal_path).unwrap();
        advance_relayer_execution_v1(
            &mut queue,
            &mut journal,
            policy,
            context,
            request_id,
            startup,
            runtime,
        )
    }

    #[test]
    fn each_crash_boundary_restarts_without_rebuilding_or_double_completion() {
        let directory = TestDirectory::new();
        let queue_path = directory.0.join("queue.state");
        let journal_path = directory.0.join("execution.state");
        let (plan, policy, startup, context) = fixture();
        let request_id = plan.request_id;
        {
            let mut queue = DurableRelayerStateV1::open_or_create_v1(&queue_path, policy).unwrap();
            assert_eq!(
                queue
                    .admit_and_enqueue_v1(
                        policy,
                        context.now_slot,
                        context.estimated_fee_lamports,
                        context.fee_payer_balance_lamports,
                        &plan,
                    )
                    .unwrap(),
                crate::relayer::RelayerEnqueueOutcomeV1::Inserted
            );
        }

        let (signed_wire, fee_payer, unsigned_message_sha256, signature) = signed_wire();
        let simulation = RelayerSimulationEvidenceV1 {
            simulated_at_slot: 901,
            recent_blockhash: [0x39; 32],
            last_valid_block_height: 500,
            fee_payer,
            unsigned_message_sha256,
            simulation_result_sha256: [0xa1; 32],
            simulation_accounts_sha256: [0xa2; 32],
            startup_receipt_digest: *startup.receipt_digest(),
            compute_unit_limit: 1_400_000,
            compute_units_consumed: 1_200_000,
            estimated_fee_lamports: context.estimated_fee_lamports,
        };
        let finalized = RelayerFinalizedEvidenceV1 {
            point: FinalizedChainPointV1::new(903, [0xb1; 32]).unwrap(),
            fee_lamports: context.estimated_fee_lamports,
            compute_units_consumed: simulation.compute_units_consumed,
            execution_result_sha256: [0xb2; 32],
            poststate_sha256: [0xb3; 32],
            provider_set_digest: *startup.provider_set_digest(),
        };
        let mut runtime = Runtime {
            simulation,
            signed_wire: signed_wire.clone(),
            observations: VecDeque::from([
                RelayerSignatureObservationV1::NotFound {
                    observed_block_height: 450,
                    evidence_sha256: [0xa3; 32],
                    provider_set_digest: *startup.provider_set_digest(),
                },
                RelayerSignatureObservationV1::NotFound {
                    observed_block_height: 451,
                    evidence_sha256: [0xa4; 32],
                    provider_set_digest: *startup.provider_set_digest(),
                },
                RelayerSignatureObservationV1::Finalized(finalized),
            ]),
            submitted_wires: Vec::new(),
        };

        for step in [
            RelayerExecutionStepV1::InflightMarked,
            RelayerExecutionStepV1::SimulationRecorded,
        ] {
            assert_eq!(
                advance_after_restart(
                    &queue_path,
                    &journal_path,
                    policy,
                    context,
                    request_id,
                    &startup,
                    &mut runtime,
                )
                .unwrap(),
                step
            );
        }

        let wrong_startup = OperatorStartupReceiptV1::test_only_v1(
            [0x95; 32],
            *startup.provider_set_digest(),
            startup.checkpoint(),
        );
        assert_eq!(
            advance_after_restart(
                &queue_path,
                &journal_path,
                policy,
                context,
                request_id,
                &wrong_startup,
                &mut runtime,
            ),
            Err(RelayerOperatorExecutionErrorV1::StartupReceiptMismatch)
        );
        assert_eq!(
            advance_after_restart(
                &queue_path,
                &journal_path,
                policy,
                context,
                request_id,
                &startup,
                &mut runtime,
            )
            .unwrap(),
            RelayerExecutionStepV1::SignedWireRecorded
        );

        let paused_policy = RelayerPolicyV1 {
            paused: true,
            ..policy
        };
        {
            let mut queue = DurableRelayerStateV1::open_or_create_v1(&queue_path, policy).unwrap();
            queue.update_policy_v1(policy, paused_policy).unwrap();
        }
        assert_eq!(
            advance_after_restart(
                &queue_path,
                &journal_path,
                paused_policy,
                context,
                request_id,
                &startup,
                &mut runtime,
            )
            .unwrap(),
            RelayerExecutionStepV1::SubmissionSuppressedByPolicy
        );
        assert!(runtime.submitted_wires.is_empty());
        {
            let mut queue =
                DurableRelayerStateV1::open_or_create_v1(&queue_path, paused_policy).unwrap();
            queue.update_policy_v1(paused_policy, policy).unwrap();
        }

        let expected = [
            RelayerExecutionStepV1::Submitted,
            RelayerExecutionStepV1::FinalOutcomeRecorded,
            RelayerExecutionStepV1::QueueCompleted,
            RelayerExecutionStepV1::AlreadyCompleted,
        ];
        for step in expected {
            assert_eq!(
                advance_after_restart(
                    &queue_path,
                    &journal_path,
                    policy,
                    context,
                    request_id,
                    &startup,
                    &mut runtime,
                )
                .unwrap(),
                step
            );
        }
        assert_eq!(runtime.submitted_wires, vec![signed_wire]);

        let journal = DurableRelayerExecutionJournalV1::open_or_create_v1(&journal_path).unwrap();
        let record = journal.record_v1(request_id).unwrap();
        assert_eq!(
            record.signed.as_ref().unwrap().transaction_signature,
            signature
        );
        assert_eq!(
            record.outcome,
            Some(RelayerExecutionOutcomeV1::Finalized(finalized))
        );
    }
}
