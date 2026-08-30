#![cfg(feature = "eight-lane-plumbing-v2")]

use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use aspis_core::field::M31;
use aspis_pool::{
    pool_v1_pair_forest_lane_address, pool_v1_pair_forest_master_address, pool_v1_state_address,
    pool_v1_vault_token_account_address, POOL_V1_PAIR_EMPTY_ROOTS,
};
use aspis_pool_wallet_v1::{
    durable_state::{DurableRelayerStateV1, DurableWalletStateV1},
    durable_witness_state::DurableWalletWitnessStateV1,
    lane_forest_durable_v2::{
        ForestFinalizedAppendEventV2, ForestFinalizedAppendKindV2, LaneForestDurableStateV2,
    },
    lane_forest_v2::LaneIdV2,
    lane_forest_wallet_txn_v2::{
        EmptyV1LaneForestWalletActivationV2, LaneForestWalletActivationPolicyV2,
        LaneForestWalletEmptyFinalizedBlockV2, LaneForestWalletTentativeCommitmentV2,
        LaneForestWalletTxnAtomicBoundaryV2, LaneForestWalletTxnAtomicFaultPointV2,
        LaneForestWalletTxnCoordinatorV2, LaneForestWalletTxnErrorV2,
        LaneForestWalletTxnFaultInjectorV2, LaneForestWalletTxnFaultPointV2,
        LaneForestWalletTxnPhaseV2, LaneForestWalletTxnPrepareV2, LaneForestWalletTxnRecoveryV2,
        LaneForestWalletTxnWriteV2,
    },
    note_store_crypto::NoteStoreCipherV1,
    relayer::RelayerPolicyV1,
    relayer_execution_journal::DurableRelayerExecutionJournalV1,
    scan_state::{
        DepositEventIdV1, DepositScanIdentityV1, FinalizedBlockV1, FinalizedChainPointV1,
        ScanStateV1,
    },
    witness_state::WalletWitnessStateV1,
};
use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{
        encode_pool_v1_pair_forest_lane_state_v1, encode_pool_v1_pair_forest_master_v1,
        IncrementalMerkleTreeV1, PoolIdentityV1, PoolV1PairForestLaneStateV1,
        PoolV1PairForestMasterV1, PoolV1PairLeafWitnessV1, VerifierPolicyV1,
        POOL_V1_PAIR_FOREST_ALL_LANES_MASK, POOL_V1_PAIR_TREE_DEPTH,
    },
};
use solana_program::pubkey::Pubkey;

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct TestDirectory(PathBuf);

impl TestDirectory {
    fn new(label: &str) -> Self {
        let serial = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "aspis-v7-empty-finalized-{label}-{}-{serial}",
            std::process::id()
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for TestDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn point(slot: u64, byte: u8) -> FinalizedChainPointV1 {
    FinalizedChainPointV1::new(slot, [byte; 32]).unwrap()
}

fn scan_identity() -> DepositScanIdentityV1 {
    let program = Pubkey::new_from_array([0x91; 32]);
    let mint = Pubkey::new_from_array([0xb2; 32]);
    let pool = pool_v1_state_address(&program, &mint).0;
    let vault = pool_v1_vault_token_account_address(&program, &pool).0;
    DepositScanIdentityV1::new(
        pool.to_bytes(),
        [0xb4; 32],
        mint.to_bytes(),
        vault.to_bytes(),
        4,
    )
    .unwrap()
}

fn empty_relayer_policy() -> RelayerPolicyV1 {
    RelayerPolicyV1 {
        paused: false,
        operator_fee_payer: Pubkey::new_from_array([0xd1; 32]),
        allow_initialize: false,
        allow_deposit: true,
        allow_prepare_settlement: true,
        allow_settle_prepared: true,
        allow_cancel_prepared: true,
        allow_private_transfer: true,
        allow_withdrawal: true,
        max_snapshot_age_slots: 32,
        max_queue_depth: 4,
        max_inflight: 2,
        rate_window_slots: 16,
        max_admissions_per_window: 2,
        max_estimated_fee_lamports: 10_000,
        minimum_fee_payer_reserve_lamports: 1_000_000,
    }
}

fn empty_forest() -> LaneForestDurableStateV2 {
    let program = Pubkey::new_from_array([0xb1; 32]);
    let mint = Pubkey::new_from_array([0xb2; 32]);
    let master = pool_v1_pair_forest_master_address(&program, &mint).0;
    let master_value = PoolV1PairForestMasterV1 {
        identity: PoolIdentityV1 {
            pool: master.to_bytes(),
            asset_mint: mint.to_bytes(),
            token_program: [0xb3; 32],
            asset_id: M31(4),
            deployment_domain: [0xb4; 32],
        },
        verifier_policy: VerifierPolicyV1 {
            flags: 1,
            registry_program: [0xb5; 32],
            registry_authority: [0; 32],
            policy_binding: [0xb6; 32],
        },
        initialized_lane_mask: POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
        has_checkpoint: false,
        next_checkpoint_sequence: 0,
        last_checkpoint_lane_sequences: [0; 8],
    };
    let master_image = encode_pool_v1_pair_forest_master_v1(&master_value).unwrap();
    let lanes = (0..8u8)
        .map(|lane_id| {
            let address = pool_v1_pair_forest_lane_address(&program, &master, lane_id)
                .unwrap()
                .0;
            let value = PoolV1PairForestLaneStateV1 {
                master: master.to_bytes(),
                lane_id,
                tree: IncrementalMerkleTreeV1 {
                    next_leaf_index: 0,
                    root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
                    frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
                },
            };
            (
                address.to_bytes(),
                encode_pool_v1_pair_forest_lane_state_v1(&value, &POOL_V1_PAIR_EMPTY_ROOTS)
                    .unwrap()
                    .to_vec(),
            )
        })
        .collect::<Vec<_>>();
    LaneForestDurableStateV2::from_authenticated_accounts_v2(
        program.to_bytes(),
        master.to_bytes(),
        &master_image,
        &lanes,
        None,
    )
    .unwrap()
}

struct ApproveTopology;

impl LaneForestWalletActivationPolicyV2 for ApproveTopology {
    fn approves_topology_transition_v2(
        &self,
        legacy_pool: &[u8; 32],
        legacy_vault: &[u8; 32],
        forest_master: &[u8; 32],
        forest_pool: &[u8; 32],
        forest_token_program: &[u8; 32],
    ) -> bool {
        legacy_pool != &[0; 32]
            && legacy_vault != &[0; 32]
            && forest_master == forest_pool
            && forest_token_program != &[0; 32]
    }
}

struct Fixture {
    _directory: TestDirectory,
    path: PathBuf,
    activation: EmptyV1LaneForestWalletActivationV2,
    cipher: NoteStoreCipherV1,
    anchor: FinalizedChainPointV1,
}

fn fixture(label: &str) -> Fixture {
    let directory = TestDirectory::new(label);
    let cipher = NoteStoreCipherV1::from_key_bytes([0x71; 32]).unwrap();
    let empty_witness = WalletWitnessStateV1::empty();
    let anchor = point(100, 0xa0);
    let scan = ScanStateV1::new(
        scan_identity(),
        anchor,
        0,
        encode_digest_canonical(&empty_witness.tree().root),
    )
    .unwrap();
    let wallet = DurableWalletStateV1::open_or_create_v1(
        directory.path("wallet-v1.state"),
        scan.clone(),
        cipher.cipher_id(),
    )
    .unwrap();
    let witness = DurableWalletWitnessStateV1::open_or_create_v1(
        directory.path("witness-v1.state"),
        &scan,
        empty_witness,
    )
    .unwrap();
    let admission = DurableRelayerStateV1::open_or_create_v1(
        directory.path("relayer-admission-v1.state"),
        empty_relayer_policy(),
    )
    .unwrap();
    let relayer =
        DurableRelayerExecutionJournalV1::open_or_create_v1(directory.path("relayer-v1.state"))
            .unwrap();
    let forest = empty_forest();
    let activation = EmptyV1LaneForestWalletActivationV2::from_empty_v1(
        &wallet,
        &witness,
        &admission,
        &relayer,
        &forest,
        &ApproveTopology,
    )
    .unwrap();
    let path = directory.path("wallet-v2.state");
    Fixture {
        _directory: directory,
        path,
        activation,
        cipher,
        anchor,
    }
}

fn empty_block(
    parent: FinalizedChainPointV1,
    slot: u64,
    byte: u8,
) -> LaneForestWalletEmptyFinalizedBlockV2 {
    LaneForestWalletEmptyFinalizedBlockV2::new_v2(
        FinalizedBlockV1::new(point(slot, byte), parent).unwrap(),
        [0x31; 32],
        [0x32; 32],
        [0x33; 32],
    )
    .unwrap()
}

fn tentative_event(
    state: &LaneForestDurableStateV2,
    at: FinalizedChainPointV1,
) -> ForestFinalizedAppendEventV2 {
    let id = DepositEventIdV1::new(at, [0x44; 64], 0, 0).unwrap();
    let commitment = encode_digest_canonical(&POOL_V1_PAIR_EMPTY_ROOTS[0]);
    let lane_id = LaneIdV2::new(commitment[0] & 7).unwrap();
    let lane = state.lane(lane_id).0;
    let pair_leaf =
        PoolV1PairLeafWitnessV1::single_output(decode_digest_canonical(&commitment).unwrap())
            .unwrap()
            .leaf_digest()
            .unwrap();
    let next_tree = lane
        .value
        .tree
        .append_one_with_empty_roots(pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
        .unwrap()
        .0;
    let after_lane = PoolV1PairForestLaneStateV1 {
        tree: next_tree,
        ..lane.value
    };
    ForestFinalizedAppendEventV2 {
        master: state.master().address,
        lane_id,
        pair_leaf_index: lane.value.tree.next_leaf_index,
        root_sequence: lane.value.tree.next_leaf_index + 1,
        after_lane_address: lane.address,
        after_lane_image: encode_pool_v1_pair_forest_lane_state_v1(
            &after_lane,
            &POOL_V1_PAIR_EMPTY_ROOTS,
        )
        .unwrap(),
        kind: ForestFinalizedAppendKindV2::Deposit {
            event_id: id,
            commitment,
            encrypted_note: None,
        },
    }
}

#[derive(Clone, Copy)]
struct LogicalFaultOnce {
    target: LaneForestWalletTxnFaultPointV2,
    fired: bool,
}

impl LaneForestWalletTxnFaultInjectorV2 for LogicalFaultOnce {
    fn interrupt_v2(&mut self, point: LaneForestWalletTxnFaultPointV2) -> bool {
        if !self.fired && point == self.target {
            self.fired = true;
            true
        } else {
            false
        }
    }
}

#[derive(Clone, Copy)]
struct AtomicFaultOnce {
    target: LaneForestWalletTxnAtomicFaultPointV2,
    fired: bool,
}

impl LaneForestWalletTxnFaultInjectorV2 for AtomicFaultOnce {
    fn interrupt_v2(&mut self, _: LaneForestWalletTxnFaultPointV2) -> bool {
        false
    }

    fn interrupt_atomic_v2(&mut self, point: LaneForestWalletTxnAtomicFaultPointV2) -> bool {
        if !self.fired && point == self.target {
            self.fired = true;
            true
        } else {
            false
        }
    }
}

fn finish_and_assert(fixture: &Fixture, expected: FinalizedChainPointV1, expected_records: usize) {
    let mut restarted = LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
        &fixture.path,
        fixture.activation.clone(),
        &fixture.cipher,
    )
    .unwrap();
    restarted.recover_to_committed_v2().unwrap();
    assert_eq!(
        restarted.recover_to_committed_v2().unwrap(),
        LaneForestWalletTxnRecoveryV2::NoPending
    );
    let state = restarted.committed_state().unwrap();
    assert_eq!(state.finalized_head(), expected);
    assert_eq!(
        state.lane_state().finalized_head_v2(),
        (expected_records != 0).then_some(expected)
    );
    assert!(state.notes().is_empty());
    assert_eq!(state.lane_state().retained_event_count_v2(), 0);
    assert_eq!(state.lane_state().checkpoint_count(), 0);
    for lane in 0..8 {
        let lane = LaneIdV2::new(lane).unwrap();
        assert_eq!(
            state.lane_state().lane(lane).0.value.tree.next_leaf_index,
            0
        );
        assert!(state.lane_state().tracked_outputs(lane).is_empty());
    }
    assert_eq!(restarted.records().unwrap().len(), expected_records);
    drop(restarted);
    let mut restarted_again = LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
        &fixture.path,
        fixture.activation.clone(),
        &fixture.cipher,
    )
    .unwrap();
    assert_eq!(
        restarted_again.recover_to_committed_v2().unwrap(),
        LaneForestWalletTxnRecoveryV2::NoPending
    );
    assert_eq!(
        restarted_again.committed_state().unwrap().finalized_head(),
        expected
    );
    assert_eq!(restarted_again.records().unwrap().len(), expected_records);
}

fn run_with_large_stack(name: &str, body: fn()) {
    std::thread::Builder::new()
        .name(name.to_owned())
        .stack_size(16 * 1024 * 1024)
        .spawn(body)
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn empty_finalized_block_clean_replay_order_conflict_and_tentative_rejection() {
    run_with_large_stack("v7-empty-clean", empty_finalized_block_clean_body);
}

fn empty_finalized_block_clean_body() {
    let clean_fixture = fixture("clean");
    let mut coordinator = LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
        &clean_fixture.path,
        clean_fixture.activation.clone(),
        &clean_fixture.cipher,
    )
    .unwrap();
    let first = empty_block(clean_fixture.anchor, 101, 0xa1);
    assert!(matches!(
        coordinator.prepare_empty_finalized_block_v2(first).unwrap(),
        LaneForestWalletTxnPrepareV2::Prepared(_)
    ));
    coordinator.recover_to_committed_v2().unwrap();
    assert_eq!(
        coordinator.committed_state().unwrap().finalized_head(),
        first.block().point()
    );
    assert_eq!(coordinator.records().unwrap().len(), 1);
    assert_eq!(
        coordinator.records().unwrap()[0]
            .empty_finalized_block()
            .unwrap(),
        &first
    );
    assert!(matches!(
        coordinator.prepare_empty_finalized_block_v2(first).unwrap(),
        LaneForestWalletTxnPrepareV2::AlreadyPresent {
            phase: LaneForestWalletTxnPhaseV2::Committed,
            ..
        }
    ));
    assert_eq!(coordinator.records().unwrap().len(), 1);

    let conflicting = LaneForestWalletEmptyFinalizedBlockV2::new_v2(
        first.block(),
        [0x41; 32],
        [0x32; 32],
        [0x33; 32],
    )
    .unwrap();
    assert_eq!(
        coordinator
            .prepare_empty_finalized_block_v2(conflicting)
            .err(),
        Some(LaneForestWalletTxnErrorV2::EventConflict)
    );
    let stale = empty_block(point(99, 0x99), 100, 0x98);
    assert_eq!(
        coordinator.prepare_empty_finalized_block_v2(stale).err(),
        Some(LaneForestWalletTxnErrorV2::FinalizedRollback)
    );
    let unknown_parent = empty_block(clean_fixture.anchor, 102, 0xa2);
    assert_eq!(
        coordinator
            .prepare_empty_finalized_block_v2(unknown_parent)
            .err(),
        Some(LaneForestWalletTxnErrorV2::FinalizedRollback)
    );
    let skipped_slot = empty_block(first.block().point(), 103, 0xa3);
    coordinator
        .prepare_empty_finalized_block_v2(skipped_slot)
        .unwrap();
    coordinator.recover_to_committed_v2().unwrap();
    assert_eq!(
        coordinator.committed_state().unwrap().finalized_head(),
        skipped_slot.block().point()
    );
    drop(coordinator);

    let tentative_fixture = fixture("tentative");
    let mut tentative = LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
        &tentative_fixture.path,
        tentative_fixture.activation.clone(),
        &tentative_fixture.cipher,
    )
    .unwrap();
    let at = point(101, 0xb1);
    let event = tentative_event(tentative.committed_state().unwrap().lane_state(), at);
    tentative
        .observe_tentative_v2(
            event.clone(),
            LaneForestWalletTentativeCommitmentV2::Confirmed,
            [0x51; 32],
        )
        .unwrap();
    assert_eq!(
        tentative
            .prepare_empty_finalized_block_v2(empty_block(tentative_fixture.anchor, 101, 0xb1))
            .err(),
        Some(LaneForestWalletTxnErrorV2::InvalidRelayerObservation)
    );
    assert_eq!(
        tentative.committed_state().unwrap().finalized_head(),
        tentative_fixture.anchor
    );
    assert_eq!(tentative.tentative_observations().unwrap().len(), 1);
}

#[test]
fn empty_finalized_block_logical_phase_faults_recover_exactly_and_idempotently() {
    run_with_large_stack("v7-empty-logical", empty_finalized_block_logical_body);
}

fn empty_finalized_block_logical_body() {
    let points = [
        LaneForestWalletTxnFaultPointV2::BeforePreparedReplace,
        LaneForestWalletTxnFaultPointV2::AfterPreparedReplace,
        LaneForestWalletTxnFaultPointV2::BeforeStoresAppliedReplace,
        LaneForestWalletTxnFaultPointV2::AfterStoresAppliedReplace,
        LaneForestWalletTxnFaultPointV2::BeforeCommittedReplace,
        LaneForestWalletTxnFaultPointV2::AfterCommittedReplace,
    ];
    for (index, target) in points.into_iter().enumerate() {
        let fixture = fixture(&format!("logical-{index}"));
        let mut coordinator = LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
            &fixture.path,
            fixture.activation.clone(),
            &fixture.cipher,
        )
        .unwrap();
        let empty = empty_block(fixture.anchor, 101, 0xc1);
        let mut faults = LogicalFaultOnce {
            target,
            fired: false,
        };
        let error = match target {
            LaneForestWalletTxnFaultPointV2::BeforePreparedReplace
            | LaneForestWalletTxnFaultPointV2::AfterPreparedReplace => coordinator
                .prepare_empty_finalized_block_with_faults_v2(empty, &mut faults)
                .err(),
            LaneForestWalletTxnFaultPointV2::BeforeStoresAppliedReplace
            | LaneForestWalletTxnFaultPointV2::AfterStoresAppliedReplace => {
                coordinator.prepare_empty_finalized_block_v2(empty).unwrap();
                coordinator
                    .advance_recovery_with_faults_v2(&mut faults)
                    .err()
            }
            LaneForestWalletTxnFaultPointV2::BeforeCommittedReplace
            | LaneForestWalletTxnFaultPointV2::AfterCommittedReplace => {
                coordinator.prepare_empty_finalized_block_v2(empty).unwrap();
                coordinator.advance_recovery_v2().unwrap();
                coordinator
                    .advance_recovery_with_faults_v2(&mut faults)
                    .err()
            }
        };
        assert_eq!(
            error,
            Some(LaneForestWalletTxnErrorV2::InjectedFault(target))
        );
        drop(coordinator);
        let pre = target == LaneForestWalletTxnFaultPointV2::BeforePreparedReplace;
        finish_and_assert(
            &fixture,
            if pre {
                fixture.anchor
            } else {
                empty.block().point()
            },
            if pre { 0 } else { 1 },
        );
    }
}

#[test]
fn empty_finalized_block_all_atomic_boundaries_recover_exactly_and_idempotently() {
    run_with_large_stack("v7-empty-atomic", empty_finalized_block_atomic_body);
}

fn empty_finalized_block_atomic_body() {
    let writes = [
        LaneForestWalletTxnWriteV2::Prepared,
        LaneForestWalletTxnWriteV2::StoresApplied,
        LaneForestWalletTxnWriteV2::Committed,
    ];
    let boundaries = [
        LaneForestWalletTxnAtomicBoundaryV2::TemporaryWrite,
        LaneForestWalletTxnAtomicBoundaryV2::TemporaryFileSync,
        LaneForestWalletTxnAtomicBoundaryV2::TargetRename,
        LaneForestWalletTxnAtomicBoundaryV2::ParentDirectorySync,
    ];
    for (write_index, write) in writes.into_iter().enumerate() {
        for (boundary_index, boundary) in boundaries.into_iter().enumerate() {
            let fixture = fixture(&format!("atomic-{write_index}-{boundary_index}"));
            let mut coordinator = LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
                &fixture.path,
                fixture.activation.clone(),
                &fixture.cipher,
            )
            .unwrap();
            let empty = empty_block(fixture.anchor, 101, 0xd1);
            let target = LaneForestWalletTxnAtomicFaultPointV2 { write, boundary };
            let mut faults = AtomicFaultOnce {
                target,
                fired: false,
            };
            let error = match write {
                LaneForestWalletTxnWriteV2::Prepared => coordinator
                    .prepare_empty_finalized_block_with_faults_v2(empty, &mut faults)
                    .err(),
                LaneForestWalletTxnWriteV2::StoresApplied => {
                    coordinator.prepare_empty_finalized_block_v2(empty).unwrap();
                    coordinator
                        .advance_recovery_with_faults_v2(&mut faults)
                        .err()
                }
                LaneForestWalletTxnWriteV2::Committed => {
                    coordinator.prepare_empty_finalized_block_v2(empty).unwrap();
                    coordinator.advance_recovery_v2().unwrap();
                    coordinator
                        .advance_recovery_with_faults_v2(&mut faults)
                        .err()
                }
                _ => unreachable!("matrix contains only journal phase writes"),
            };
            assert_eq!(
                error,
                Some(LaneForestWalletTxnErrorV2::InjectedAtomicFault(target))
            );
            drop(coordinator);
            let pre = write == LaneForestWalletTxnWriteV2::Prepared
                && matches!(
                    boundary,
                    LaneForestWalletTxnAtomicBoundaryV2::TemporaryWrite
                        | LaneForestWalletTxnAtomicBoundaryV2::TemporaryFileSync
                );
            finish_and_assert(
                &fixture,
                if pre {
                    fixture.anchor
                } else {
                    empty.block().point()
                },
                if pre { 0 } else { 1 },
            );
        }
    }
}
