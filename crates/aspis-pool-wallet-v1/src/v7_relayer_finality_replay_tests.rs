use std::{
    collections::VecDeque,
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use aspis_core::field::M31;
use aspis_pool::{deposit::DepositRequestV1, pool_v1_state_address};
use aspis_statement::{encode_digest_canonical, poseidon2::Digest};
use serde_json::json;
use sha2::{Digest as _, Sha256};
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_keypair::Keypair;
use solana_message::{legacy, VersionedMessage};
use solana_program::{hash::Hash, pubkey::Pubkey};
use solana_signer::Signer;
use solana_transaction::versioned::VersionedTransaction;

use crate::{
    durable_state::{DurableRelayerStateV1, DurableRelayerStatusV1},
    finalized_indexer::{
        FinalizedAppendEvidenceV1, FinalizedBlockIngestResultV1, HistoricalRootEvidenceV1,
    },
    operator_execution::{
        advance_relayer_execution_v1, RelayerExecutionContextV1, RelayerExecutionPortV1,
        RelayerExecutionStepV1, RelayerFinalizedObservationV1, RelayerNotFoundObservationV1,
        RelayerOperatorExecutionErrorV1, RelayerPendingObservationV1,
        RelayerSignatureObservationV1, RelayerSimulationArtifactV1,
    },
    operator_startup::{
        provider_set_digest_v1, FinalizedReleaseCheckpointV1, OperatorStartupReceiptV1,
    },
    relayer::{
        prepare_permissionless_relayer_plan_v1, RelayerPlanV1, RelayerPolicyV1, RelayerSnapshotV1,
    },
    relayer_execution_journal::{
        DurableRelayerExecutionJournalV1, RelayerExecutionJournalErrorV1,
        RelayerExecutionJournalUpdateV1, RelayerExecutionOutcomeV1, RelayerFinalizedEvidenceV1,
        RelayerSimulationEvidenceV1, RelayerSubmissionEvidenceV1,
    },
    relayer_finalized_evidence::derive_relayer_finalized_evidence_v1,
    relayer_rpc_json::SignatureStatusesRequestV1,
    relayer_rpc_quorum::{
        ExactProviderRpcExchangeV1, ExactTwoProviderRelayerRpcV1, RelayerRpcQuorumErrorV1,
    },
    relayer_transaction::{
        canonical_relayer_instruction_index_v1, relayer_simulation_accounts_sha256_v1,
        RelayerSignedTransactionArtifactV1,
    },
    rpc_json::FinalizedTransactionExecutionV1,
    scan_state::{
        DepositEventIdV1, DepositScanOutcomeV1, FinalizedBlockAdvanceV1, FinalizedChainPointV1,
    },
    transaction_builder::build_deposit_instruction_v1,
};

const PROVIDERS: [[u8; 32]; 2] = [[0x11; 32], [0x22; 32]];
const STARTUP_SLOT: u64 = 900;
const SIMULATION_SLOT: u64 = 901;
const FINALIZED_SLOT: u64 = 903;

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct TestDirectory(std::path::PathBuf);

impl TestDirectory {
    fn new() -> Self {
        let serial = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "aspis-v7-relayer-finality-replay-{}-{serial}",
            std::process::id()
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

fn fixture_v1(
    fee_payer: Pubkey,
    source_authority: Pubkey,
) -> (
    RelayerPlanV1,
    RelayerPolicyV1,
    OperatorStartupReceiptV1,
    RelayerExecutionContextV1,
) {
    let program_id = key(1);
    let mint = key(2);
    let pool = pool_v1_state_address(&program_id, &mint).0;
    let request = DepositRequestV1 {
        owner_key: digest(10),
        amount: 77,
        salt: digest(20),
        encrypted_note_payload: &[],
    };
    let instruction = build_deposit_instruction_v1(
        program_id,
        pool,
        mint,
        7,
        key(3),
        source_authority,
        None,
        &request,
    )
    .unwrap();
    let snapshot = RelayerSnapshotV1 {
        pinned_program_id: program_id,
        registry_program: key(5),
        current_root_sequence: 7,
        observed_slot: STARTUP_SLOT,
        pool_state_sha256: [0xab; 32],
    };
    let plan = prepare_permissionless_relayer_plan_v1(snapshot, fee_payer, &instruction).unwrap();
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
        point: FinalizedChainPointV1::new(STARTUP_SLOT, [0x91; 32]).unwrap(),
        pool_state_sha256: snapshot.pool_state_sha256,
        root_sequence: snapshot.current_root_sequence,
        root: [0x92; 32],
    };
    let startup = OperatorStartupReceiptV1::test_only_v1(
        [0x93; 32],
        provider_set_digest_v1(&PROVIDERS),
        checkpoint,
    );
    let context = RelayerExecutionContextV1 {
        now_slot: SIMULATION_SLOT,
        estimated_fee_lamports: 10_000,
        fee_payer_balance_lamports: 2_000_000,
    };
    (plan, policy, startup, context)
}

fn signed_simulation_v1(
    plan: &RelayerPlanV1,
    startup: &OperatorStartupReceiptV1,
    context: RelayerExecutionContextV1,
    fee_payer: &Keypair,
    source_authority: &Keypair,
) -> (
    RelayerSimulationEvidenceV1,
    RelayerSignedTransactionArtifactV1,
    Vec<u8>,
    [u8; 64],
) {
    let recent_blockhash = Hash::new_from_array([0x39; 32]);
    let instructions = [
        ComputeBudgetInstruction::set_compute_unit_limit(1_400_000),
        plan.instruction.clone(),
    ];
    let message = VersionedMessage::Legacy(legacy::Message::new_with_blockhash(
        &instructions,
        Some(&plan.fee_payer),
        &recent_blockhash,
    ));
    let exact_unsigned_message = message.serialize();
    let transaction =
        VersionedTransaction::try_new(message, &[fee_payer, source_authority]).unwrap();
    let signature = *transaction.signatures[0].as_array();
    let signed_wire = bincode::serialize(&transaction).unwrap();
    let simulation = RelayerSimulationEvidenceV1 {
        simulated_at_slot: SIMULATION_SLOT,
        recent_blockhash: [0x39; 32],
        last_valid_block_height: 500,
        fee_payer: plan.fee_payer.to_bytes(),
        unsigned_message_sha256: Sha256::digest(&exact_unsigned_message).into(),
        simulation_result_sha256: [0xa1; 32],
        simulation_accounts_sha256: relayer_simulation_accounts_sha256_v1(
            plan,
            SIMULATION_SLOT,
            *startup.provider_set_digest(),
            &[],
        )
        .unwrap(),
        startup_receipt_digest: *startup.receipt_digest(),
        compute_unit_limit: 1_400_000,
        compute_unit_price_micro_lamports: 0,
        compute_units_consumed: 1_200_000,
        estimated_fee_lamports: context.estimated_fee_lamports,
    };
    (
        simulation,
        RelayerSignedTransactionArtifactV1 {
            signed_wire,
            lookup_tables: Vec::new(),
        },
        exact_unsigned_message,
        signature,
    )
}

fn finalized_observation_v1(
    plan: &RelayerPlanV1,
    startup: &OperatorStartupReceiptV1,
    simulation: RelayerSimulationEvidenceV1,
    signature: [u8; 64],
) -> (RelayerSignatureObservationV1, RelayerFinalizedEvidenceV1) {
    let point = FinalizedChainPointV1::new(FINALIZED_SLOT, [0xb1; 32]).unwrap();
    let execution = FinalizedTransactionExecutionV1::test_only_v1(
        point,
        signature,
        simulation.estimated_fee_lamports,
        simulation.compute_units_consumed,
    );
    let instruction_index = canonical_relayer_instruction_index_v1(simulation);
    let event_id = DepositEventIdV1::new(point, signature, instruction_index, 0).unwrap();
    let finalized_root = encode_digest_canonical(&digest(500));
    let note_commitment = encode_digest_canonical(&digest(400));
    let indexed_pool = FinalizedBlockIngestResultV1 {
        advance: FinalizedBlockAdvanceV1::Advanced,
        rollback: None,
        deposit_event_ids: vec![event_id],
        deposit_outcomes: vec![DepositScanOutcomeV1::NotForViewingKey],
        transition_outcomes: Vec::new(),
        transition_evidence: Vec::new(),
        initializations: Vec::new(),
        append_evidence: vec![FinalizedAppendEvidenceV1 {
            event_id,
            leaf_index: 7,
            root_sequence: 8,
            note_commitment,
            root: finalized_root,
        }],
        prepared_settlements: Vec::new(),
        cancelled_settlements: Vec::new(),
        plan_lifecycle: Vec::new(),
        root_evidence: vec![HistoricalRootEvidenceV1 {
            event_id,
            root_sequence: 8,
            root: finalized_root,
            page_number: 0,
            page_address: [0xb4; 32],
            snapshot_context_slot: FINALIZED_SLOT,
        }],
        ignored_failed_pool_transactions: 0,
    };
    let status_evidence_sha256 = [0xb5; 32];
    let block_request_binding_sha256 = [0xb6; 32];
    let finalized = derive_relayer_finalized_evidence_v1(
        plan,
        execution,
        &indexed_pool,
        instruction_index,
        *startup.provider_set_digest(),
        status_evidence_sha256,
        block_request_binding_sha256,
        None,
    )
    .unwrap();
    (
        RelayerSignatureObservationV1::Finalized(
            RelayerFinalizedObservationV1::from_agreed_finality_v1(
                execution,
                indexed_pool,
                *startup.provider_set_digest(),
                status_evidence_sha256,
                block_request_binding_sha256,
                None,
            ),
        ),
        finalized,
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RuntimeErrorV1 {
    MissingObservation,
    MissingSubmissionResult,
    LostSubmissionResponse,
}

struct RuntimeV1 {
    simulation: RelayerSimulationEvidenceV1,
    signed: RelayerSignedTransactionArtifactV1,
    observations: VecDeque<RelayerSignatureObservationV1>,
    submission_results: VecDeque<Result<RelayerSubmissionEvidenceV1, RuntimeErrorV1>>,
    signed_messages: Vec<Vec<u8>>,
    submitted_wires: Vec<Vec<u8>>,
    observation_calls: usize,
}

impl RelayerExecutionPortV1 for RuntimeV1 {
    type Error = RuntimeErrorV1;

    fn simulate_exact_plan_v1(
        &mut self,
        _plan: &RelayerPlanV1,
        _startup: &OperatorStartupReceiptV1,
    ) -> Result<RelayerSimulationArtifactV1, Self::Error> {
        Ok(RelayerSimulationArtifactV1::from_exact_rpc_composition_v1(
            self.simulation,
            self.signed.lookup_tables.clone(),
        ))
    }

    fn sign_exact_unsigned_message_v1(
        &mut self,
        _plan: &RelayerPlanV1,
        _simulation: RelayerSimulationEvidenceV1,
        exact_unsigned_message: &[u8],
    ) -> Result<Vec<u8>, Self::Error> {
        self.signed_messages.push(exact_unsigned_message.to_vec());
        Ok(self.signed.signed_wire.clone())
    }

    fn observe_signature_v1(
        &mut self,
        _transaction_signature: [u8; 64],
        _startup: &OperatorStartupReceiptV1,
    ) -> Result<RelayerSignatureObservationV1, Self::Error> {
        self.observation_calls += 1;
        self.observations
            .pop_front()
            .ok_or(RuntimeErrorV1::MissingObservation)
    }

    fn submit_exact_signed_wire_v1(
        &mut self,
        _transaction_signature: [u8; 64],
        signed_wire: &[u8],
        _simulation: RelayerSimulationEvidenceV1,
        _startup: &OperatorStartupReceiptV1,
    ) -> Result<RelayerSubmissionEvidenceV1, Self::Error> {
        self.submitted_wires.push(signed_wire.to_vec());
        self.submission_results
            .pop_front()
            .ok_or(RuntimeErrorV1::MissingSubmissionResult)?
    }
}

fn advance_after_restart_v1(
    queue_path: &std::path::Path,
    journal_path: &std::path::Path,
    policy: RelayerPolicyV1,
    context: RelayerExecutionContextV1,
    request_id: [u8; 32],
    startup: &OperatorStartupReceiptV1,
    runtime: &mut RuntimeV1,
) -> Result<RelayerExecutionStepV1, RelayerOperatorExecutionErrorV1<RuntimeErrorV1>> {
    let mut queue = DurableRelayerStateV1::open_or_create_v1(queue_path, policy).unwrap();
    let mut journal = DurableRelayerExecutionJournalV1::open_or_create_v1(journal_path).unwrap();
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

fn rpc_response_v1(request_id: u64, context_slot: u64, value: serde_json::Value) -> Vec<u8> {
    serde_json::to_vec(&json!({
        "jsonrpc": "2.0",
        "id": request_id,
        "result": {"context": {"slot": context_slot}, "value": value},
    }))
    .unwrap()
}

fn assert_conflicting_finality_quorum_has_no_journal_effect_v1(
    startup: &OperatorStartupReceiptV1,
    signature: [u8; 64],
    journal_path: &std::path::Path,
) {
    let before = fs::read(journal_path).unwrap();
    let quorum = ExactTwoProviderRelayerRpcV1::new(PROVIDERS, startup).unwrap();
    let request = SignatureStatusesRequestV1::new(77, signature).unwrap();
    let request_json = request.encode_json_v1();
    let finalized = rpc_response_v1(
        request.request_id(),
        FINALIZED_SLOT + 2,
        json!([{
            "slot": FINALIZED_SLOT,
            "confirmations": null,
            "err": null,
            "confirmationStatus": "finalized",
            "status": {"Ok": null}
        }]),
    );
    let merely_confirmed = rpc_response_v1(
        request.request_id(),
        FINALIZED_SLOT + 2,
        json!([{
            "slot": FINALIZED_SLOT,
            "confirmations": 1,
            "err": null,
            "confirmationStatus": "confirmed",
            "status": {"Ok": null}
        }]),
    );
    assert_eq!(
        quorum.agree_signature_status_v1(
            &request,
            [
                ExactProviderRpcExchangeV1::new(PROVIDERS[0], &request_json, &finalized),
                ExactProviderRpcExchangeV1::new(PROVIDERS[1], &request_json, &merely_confirmed,),
            ],
        ),
        Err(RelayerRpcQuorumErrorV1::ProviderDisagreement)
    );
    assert_eq!(fs::read(journal_path).unwrap(), before);
}

#[test]
fn lost_submit_response_and_replayed_finality_remain_conservative_and_idempotent() {
    let directory = TestDirectory::new();
    let queue_path = directory.0.join("queue.state");
    let journal_path = directory.0.join("execution.state");
    let fee_payer = Keypair::new_from_array([0x31; 32]);
    let source_authority = Keypair::new_from_array([0x32; 32]);
    let (plan, policy, startup, context) =
        fixture_v1(fee_payer.pubkey(), source_authority.pubkey());
    let request_id = plan.request_id;
    {
        let mut queue = DurableRelayerStateV1::open_or_create_v1(&queue_path, policy).unwrap();
        queue
            .admit_and_enqueue_v1(
                policy,
                context.now_slot,
                context.estimated_fee_lamports,
                context.fee_payer_balance_lamports,
                &plan,
            )
            .unwrap();
    }

    let (simulation, signed, exact_unsigned_message, signature) =
        signed_simulation_v1(&plan, &startup, context, &fee_payer, &source_authority);
    let signed_wire = signed.signed_wire.clone();
    let (finalized_observation, finalized_evidence) =
        finalized_observation_v1(&plan, &startup, simulation, signature);
    let not_found = |height, evidence| {
        RelayerSignatureObservationV1::NotFound(
            RelayerNotFoundObservationV1::from_agreed_status_v1(
                height,
                evidence,
                *startup.provider_set_digest(),
            ),
        )
    };
    let mut runtime = RuntimeV1 {
        simulation,
        signed,
        observations: VecDeque::from([
            not_found(450, [0xa3; 32]),
            RelayerSignatureObservationV1::Pending(
                RelayerPendingObservationV1::from_agreed_status_v1(*startup.provider_set_digest()),
            ),
            not_found(451, [0xa4; 32]),
            finalized_observation,
        ]),
        submission_results: VecDeque::from([
            Err(RuntimeErrorV1::LostSubmissionResponse),
            Ok(RelayerSubmissionEvidenceV1 {
                submitted_at_slot: SIMULATION_SLOT,
                provider_set_digest: *startup.provider_set_digest(),
            }),
        ]),
        signed_messages: Vec::new(),
        submitted_wires: Vec::new(),
        observation_calls: 0,
    };

    for expected in [
        RelayerExecutionStepV1::InflightMarked,
        RelayerExecutionStepV1::SimulationRecorded,
        RelayerExecutionStepV1::SignedWireRecorded,
    ] {
        assert_eq!(
            advance_after_restart_v1(
                &queue_path,
                &journal_path,
                policy,
                context,
                request_id,
                &startup,
                &mut runtime,
            )
            .unwrap(),
            expected
        );
    }

    // The exact signed wire is durable before any RPC submission begins.
    assert!(runtime.submitted_wires.is_empty());
    {
        let journal = DurableRelayerExecutionJournalV1::open_or_create_v1(&journal_path).unwrap();
        let record = journal.record_v1(request_id).unwrap();
        assert_eq!(record.signed.as_ref().unwrap().signed_wire, signed_wire);
        assert_eq!(record.submission, None);
        assert_eq!(record.outcome, None);
    }

    // A finalized/confirmed disagreement never reaches the coordinator and
    // cannot mutate the already durable execution record.
    assert_conflicting_finality_quorum_has_no_journal_effect_v1(&startup, signature, &journal_path);

    // The first send may have reached a provider, but its response was lost.
    // Restart retains the signed wire while recording neither submission nor
    // successful finality from that ambiguous network outcome.
    assert_eq!(
        advance_after_restart_v1(
            &queue_path,
            &journal_path,
            policy,
            context,
            request_id,
            &startup,
            &mut runtime,
        ),
        Err(RelayerOperatorExecutionErrorV1::Runtime(
            RuntimeErrorV1::LostSubmissionResponse
        ))
    );
    {
        let queue = DurableRelayerStateV1::open_or_create_v1(&queue_path, policy).unwrap();
        assert_eq!(queue.entries()[0].status, DurableRelayerStatusV1::Inflight);
        let journal = DurableRelayerExecutionJournalV1::open_or_create_v1(&journal_path).unwrap();
        let record = journal.record_v1(request_id).unwrap();
        assert_eq!(record.submission, None);
        assert_eq!(record.outcome, None);
    }

    // Restart queries status before considering a byte-for-byte retry. A
    // merely pending status cannot promote the request or trigger another send.
    assert_eq!(
        advance_after_restart_v1(
            &queue_path,
            &journal_path,
            policy,
            context,
            request_id,
            &startup,
            &mut runtime,
        )
        .unwrap(),
        RelayerExecutionStepV1::AwaitingFinality
    );
    assert_eq!(runtime.submitted_wires, vec![signed_wire.clone()]);
    {
        let journal = DurableRelayerExecutionJournalV1::open_or_create_v1(&journal_path).unwrap();
        let record = journal.record_v1(request_id).unwrap();
        assert_eq!(record.submission, None);
        assert_eq!(record.outcome, None);
    }

    // A later not-found observation retries only the already journaled wire.
    assert_eq!(
        advance_after_restart_v1(
            &queue_path,
            &journal_path,
            policy,
            context,
            request_id,
            &startup,
            &mut runtime,
        )
        .unwrap(),
        RelayerExecutionStepV1::Submitted
    );
    assert_eq!(
        runtime.submitted_wires,
        vec![signed_wire.clone(), signed_wire.clone()]
    );
    {
        let journal = DurableRelayerExecutionJournalV1::open_or_create_v1(&journal_path).unwrap();
        let record = journal.record_v1(request_id).unwrap();
        assert!(record.submission.is_some());
        assert_eq!(record.outcome, None);
    }

    assert_eq!(
        advance_after_restart_v1(
            &queue_path,
            &journal_path,
            policy,
            context,
            request_id,
            &startup,
            &mut runtime,
        )
        .unwrap(),
        RelayerExecutionStepV1::FinalOutcomeRecorded
    );

    // Replaying the same finalized observation is idempotent; conflicting
    // finalized evidence is rejected without replacing the first outcome.
    {
        let mut journal =
            DurableRelayerExecutionJournalV1::open_or_create_v1(&journal_path).unwrap();
        assert_eq!(
            journal
                .record_finalized_v1(request_id, signature, finalized_evidence)
                .unwrap(),
            RelayerExecutionJournalUpdateV1::AlreadyPresent
        );
        let conflicting = RelayerFinalizedEvidenceV1 {
            poststate_sha256: [0xf1; 32],
            ..finalized_evidence
        };
        assert_eq!(
            journal.record_finalized_v1(request_id, signature, conflicting),
            Err(RelayerExecutionJournalErrorV1::OutcomeMismatch)
        );
        assert_eq!(
            journal.record_v1(request_id).unwrap().outcome,
            Some(RelayerExecutionOutcomeV1::Finalized(finalized_evidence))
        );
    }

    let observations_before_completion = runtime.observation_calls;
    assert_eq!(
        advance_after_restart_v1(
            &queue_path,
            &journal_path,
            policy,
            context,
            request_id,
            &startup,
            &mut runtime,
        )
        .unwrap(),
        RelayerExecutionStepV1::QueueCompleted
    );
    assert_eq!(
        advance_after_restart_v1(
            &queue_path,
            &journal_path,
            policy,
            context,
            request_id,
            &startup,
            &mut runtime,
        )
        .unwrap(),
        RelayerExecutionStepV1::AlreadyCompleted
    );
    assert_eq!(runtime.observation_calls, observations_before_completion);
    assert_eq!(runtime.signed_messages, vec![exact_unsigned_message]);
}
