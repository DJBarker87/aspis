#![cfg(feature = "eight-lane-plumbing-v2")]

use std::{
    convert::Infallible,
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use aspis_core::field::M31;
use aspis_pool::{
    pool_v1_pair_forest_checkpoint_address, pool_v1_pair_forest_lane_address,
    pool_v1_pair_forest_master_address, pool_v1_state_address, pool_v1_vault_token_account_address,
    POOL_V1_PAIR_EMPTY_ROOTS,
};
use aspis_pool_wallet_v1::{
    durable_state::{
        AuthenticatedSpentNoteUpdateV1, DurableRelayerStateV1, DurableWalletStateV1,
        LocalSpendAuthenticatorV1, SealedNoteAccessV1, SealedRecoveredNoteV1,
    },
    durable_witness_state::DurableWalletWitnessStateV1,
    lane_forest_durable_v2::{
        ForestFinalizedAppendEventV2, ForestFinalizedAppendKindV2, LaneForestDurableStateV2,
    },
    lane_forest_v2::{lane_forest_global_root_v2, LaneIdV2},
    lane_forest_wallet_txn_v2::{
        EmptyV1LaneForestWalletActivationV2, LaneForestWalletActivationPolicyV2,
        LaneForestWalletCheckpointBindingV2, LaneForestWalletCommittedStateV2,
        LaneForestWalletNoteBindingV2, LaneForestWalletSpendBindingV2,
        LaneForestWalletTentativeCommitmentV2, LaneForestWalletTentativeUpdateV2,
        LaneForestWalletTxnAtomicBoundaryV2, LaneForestWalletTxnAtomicFaultPointV2,
        LaneForestWalletTxnCoordinatorV2, LaneForestWalletTxnErrorV2,
        LaneForestWalletTxnFaultInjectorV2, LaneForestWalletTxnFaultPointV2,
        LaneForestWalletTxnIntentV2, LaneForestWalletTxnPhaseV2, LaneForestWalletTxnPrepareV2,
        LaneForestWalletTxnRecoveryV2, LaneForestWalletTxnWriteV2,
    },
    note_store_crypto::{seal_recovered_note_v1, NoteStoreCipherV1},
    recompute_note_commitment_v1,
    relayer::RelayerPolicyV1,
    relayer_execution_journal::DurableRelayerExecutionJournalV1,
    scan_state::{
        DepositEventIdV1, DepositScanIdentityV1, FinalizedBlockV1, FinalizedChainPointV1,
        ScanStateV1,
    },
    witness_state::WalletWitnessStateV1,
    NoteOpeningV1, POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES,
};
use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{
        encode_pool_v1_pair_forest_checkpoint_v1, encode_pool_v1_pair_forest_lane_state_v1,
        encode_pool_v1_pair_forest_master_v1, IncrementalMerkleTreeV1, PoolIdentityV1,
        PoolV1PairForestCheckpointV1, PoolV1PairForestLaneStateV1, PoolV1PairForestMasterV1,
        PoolV1PairLeafWitnessV1, VerifierPolicyV1, POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
        POOL_V1_PAIR_TREE_DEPTH,
    },
    Digest,
};
use hpke::rand_core::{TryCryptoRng, TryRng};
use solana_program::pubkey::Pubkey;

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct TestDirectory(PathBuf);

impl TestDirectory {
    fn new(label: &str) -> Self {
        let serial = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "aspis-v7-cross-store-{label}-{}-{serial}",
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

struct IncrementingRng(u8);

impl TryRng for IncrementingRng {
    type Error = Infallible;

    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        let mut bytes = [0u8; 4];
        self.try_fill_bytes(&mut bytes)?;
        Ok(u32::from_le_bytes(bytes))
    }

    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        let mut bytes = [0u8; 8];
        self.try_fill_bytes(&mut bytes)?;
        Ok(u64::from_le_bytes(bytes))
    }

    fn try_fill_bytes(&mut self, destination: &mut [u8]) -> Result<(), Self::Error> {
        for byte in destination {
            *byte = self.0;
            self.0 = self.0.wrapping_add(1);
        }
        Ok(())
    }
}

impl TryCryptoRng for IncrementingRng {}

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + 17 * index as u32))
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

fn point(slot: u64, seed: u8) -> FinalizedChainPointV1 {
    FinalizedChainPointV1::new(slot, [seed; 32]).unwrap()
}

fn event_id(slot: u64, seed: u8, event_index: u16) -> DepositEventIdV1 {
    DepositEventIdV1::new(
        point(slot, seed.wrapping_add(1)),
        [seed; 64],
        0,
        event_index,
    )
    .unwrap()
}

struct EmptyActivationFixture {
    directory: TestDirectory,
    wallet: DurableWalletStateV1,
    witness: DurableWalletWitnessStateV1,
    relayer_admission: DurableRelayerStateV1,
    relayer: DurableRelayerExecutionJournalV1,
    lane_state: LaneForestDurableStateV2,
    cipher: NoteStoreCipherV1,
}

struct ApproveFixtureTopology;

impl LaneForestWalletActivationPolicyV2 for ApproveFixtureTopology {
    fn approves_topology_transition_v2(
        &self,
        legacy_pool: &[u8; 32],
        legacy_vault_token_account: &[u8; 32],
        forest_master: &[u8; 32],
        forest_identity_pool: &[u8; 32],
        forest_token_program: &[u8; 32],
    ) -> bool {
        legacy_pool != &[0; 32]
            && legacy_vault_token_account != &[0; 32]
            && forest_master != &[0; 32]
            && forest_identity_pool == forest_master
            && forest_token_program != &[0; 32]
    }
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

fn empty_activation_fixture(label: &str) -> EmptyActivationFixture {
    let directory = TestDirectory::new(label);
    let cipher = NoteStoreCipherV1::from_key_bytes([0x71; 32]).unwrap();
    let empty_witness = WalletWitnessStateV1::empty();
    let scan = ScanStateV1::new(
        scan_identity(),
        point(100, 0xa0),
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
    let relayer_admission = DurableRelayerStateV1::open_or_create_v1(
        directory.path("relayer-admission-v1.state"),
        empty_relayer_policy(),
    )
    .unwrap();
    let relayer =
        DurableRelayerExecutionJournalV1::open_or_create_v1(directory.path("relayer-v1.state"))
            .unwrap();
    let lane_state = empty_forest_fixture();
    EmptyActivationFixture {
        directory,
        wallet,
        witness,
        relayer_admission,
        relayer,
        lane_state,
        cipher,
    }
}

impl EmptyActivationFixture {
    fn activation(&self) -> EmptyV1LaneForestWalletActivationV2 {
        EmptyV1LaneForestWalletActivationV2::from_empty_v1(
            &self.wallet,
            &self.witness,
            &self.relayer_admission,
            &self.relayer,
            &self.lane_state,
            &ApproveFixtureTopology,
        )
        .unwrap()
    }

    fn transaction_path(&self) -> PathBuf {
        self.directory.path("wallet-v2.state")
    }
}

fn empty_forest_fixture() -> LaneForestDurableStateV2 {
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

fn note_for_lane(
    target: LaneIdV2,
    owner_seed: u32,
    value: u32,
    first_salt_seed: u32,
) -> (NoteOpeningV1, [u8; 32]) {
    for salt_seed in first_salt_seed..first_salt_seed + 10_000 {
        let note = NoteOpeningV1::new(
            encode_digest_canonical(&digest(owner_seed)),
            value,
            4,
            encode_digest_canonical(&digest(salt_seed)),
        )
        .unwrap();
        let commitment = recompute_note_commitment_v1(&note).unwrap();
        if commitment[0] & 7 == target.as_u8() {
            return (note, commitment);
        }
    }
    panic!("deterministic note search did not reach target lane")
}

fn after_lane_for_pair_leaf(
    state: &LaneForestDurableStateV2,
    lane_id: LaneIdV2,
    pair_leaf: Digest,
) -> (
    [u8; 32],
    [u8; aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES],
) {
    let account = *state.lane(lane_id).0;
    let next_tree = account
        .value
        .tree
        .append_one_with_empty_roots(pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
        .unwrap()
        .0;
    let value = PoolV1PairForestLaneStateV1 {
        tree: next_tree,
        ..account.value
    };
    (
        account.address,
        encode_pool_v1_pair_forest_lane_state_v1(&value, &POOL_V1_PAIR_EMPTY_ROOTS).unwrap(),
    )
}

fn deposit_event(
    state: &LaneForestDurableStateV2,
    id: DepositEventIdV1,
    commitment: [u8; 32],
) -> ForestFinalizedAppendEventV2 {
    let lane_id = LaneIdV2::new(commitment[0] & 7).unwrap();
    let pair_leaf =
        PoolV1PairLeafWitnessV1::single_output(decode_digest_canonical(&commitment).unwrap())
            .unwrap()
            .leaf_digest()
            .unwrap();
    let pair_leaf_index = state.lane(lane_id).0.value.tree.next_leaf_index;
    let (after_lane_address, after_lane_image) =
        after_lane_for_pair_leaf(state, lane_id, pair_leaf);
    ForestFinalizedAppendEventV2 {
        master: state.master().address,
        lane_id,
        pair_leaf_index,
        root_sequence: pair_leaf_index + 1,
        after_lane_address,
        after_lane_image,
        kind: ForestFinalizedAppendKindV2::Deposit {
            event_id: id,
            commitment,
            encrypted_note: None,
        },
    }
}

fn private_transfer_event(
    state: &LaneForestDurableStateV2,
    recipient_id: DepositEventIdV1,
    change_id: DepositEventIdV1,
    nullifier: [u8; 32],
    recipient_commitment: [u8; 32],
    change_commitment: [u8; 32],
) -> ForestFinalizedAppendEventV2 {
    let lane_id = LaneIdV2::new(nullifier[0] & 7).unwrap();
    let pair_leaf = PoolV1PairLeafWitnessV1::two_outputs(
        decode_digest_canonical(&recipient_commitment).unwrap(),
        decode_digest_canonical(&change_commitment).unwrap(),
    )
    .unwrap()
    .leaf_digest()
    .unwrap();
    let pair_leaf_index = state.lane(lane_id).0.value.tree.next_leaf_index;
    let (after_lane_address, after_lane_image) =
        after_lane_for_pair_leaf(state, lane_id, pair_leaf);
    ForestFinalizedAppendEventV2 {
        master: state.master().address,
        lane_id,
        pair_leaf_index,
        root_sequence: pair_leaf_index + 1,
        after_lane_address,
        after_lane_image,
        kind: ForestFinalizedAppendKindV2::PrivateTransfer {
            recipient_event_id: recipient_id,
            change_event_id: change_id,
            nullifier,
            recipient_commitment,
            change_commitment,
            recipient_encrypted_note: None,
            change_encrypted_note: None,
        },
    }
}

type CheckpointInputs = (
    [u8; 32],
    Vec<u8>,
    Vec<([u8; 32], Vec<u8>)>,
    [u8; 32],
    Vec<u8>,
);

fn checkpoint_inputs(state: &LaneForestDurableStateV2) -> CheckpointInputs {
    let sequences: [u64; 8] = core::array::from_fn(|index| {
        state
            .lane(LaneIdV2::new(index as u8).unwrap())
            .0
            .value
            .tree
            .next_leaf_index
    });
    let roots: [[u8; 32]; 8] = core::array::from_fn(|index| {
        encode_digest_canonical(
            &state
                .lane(LaneIdV2::new(index as u8).unwrap())
                .0
                .value
                .tree
                .root,
        )
    });
    let checkpoint = PoolV1PairForestCheckpointV1 {
        master: state.master().address,
        deployment_domain: state.master().value.identity.deployment_domain,
        checkpoint_sequence: state.master().value.next_checkpoint_sequence,
        global_root: decode_digest_canonical(&lane_forest_global_root_v2(&roots).unwrap()).unwrap(),
        lane_sequences: sequences,
    };
    let program = Pubkey::new_from_array(*state.program_id());
    let master = Pubkey::new_from_array(state.master().address);
    let checkpoint_address =
        pool_v1_pair_forest_checkpoint_address(&program, &master, checkpoint.checkpoint_sequence)
            .0
            .to_bytes();
    let next_master = PoolV1PairForestMasterV1 {
        has_checkpoint: true,
        next_checkpoint_sequence: checkpoint.checkpoint_sequence + 1,
        last_checkpoint_lane_sequences: sequences,
        ..state.master().value
    };
    (
        state.master().address,
        encode_pool_v1_pair_forest_master_v1(&next_master)
            .unwrap()
            .to_vec(),
        (0..8)
            .map(|index| {
                let lane = state.lane(LaneIdV2::new(index).unwrap()).0;
                (lane.address, lane.image.to_vec())
            })
            .collect(),
        checkpoint_address,
        encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint)
            .unwrap()
            .to_vec(),
    )
}

fn checkpoint_binding(
    state_after_event: &LaneForestDurableStateV2,
    event_point: FinalizedChainPointV1,
) -> LaneForestWalletCheckpointBindingV2 {
    let (master, master_image, lanes, checkpoint, checkpoint_image) =
        checkpoint_inputs(state_after_event);
    LaneForestWalletCheckpointBindingV2::new_v2(
        event_point,
        master,
        master_image,
        lanes,
        checkpoint,
        checkpoint_image,
    )
    .unwrap()
}

fn sealed_note(
    cipher: &NoteStoreCipherV1,
    id: DepositEventIdV1,
    note: &NoteOpeningV1,
    nonce_seed: u8,
) -> (SealedRecoveredNoteV1, LaneForestWalletNoteBindingV2) {
    let sealed = seal_recovered_note_v1(
        &mut IncrementingRng(nonce_seed),
        cipher,
        id,
        SealedNoteAccessV1::Spendable,
        note,
    )
    .unwrap();
    let binding = LaneForestWalletNoteBindingV2::from_sealed_recovered_note_v2(&sealed).unwrap();
    (sealed, binding)
}

fn finalized_block(
    event: &ForestFinalizedAppendEventV2,
    parent: FinalizedChainPointV1,
) -> FinalizedBlockV1 {
    FinalizedBlockV1::new(event.point(), parent).unwrap()
}

fn finalized_deposit_intent(
    state: &LaneForestDurableStateV2,
    cipher: &NoteStoreCipherV1,
    parent: FinalizedChainPointV1,
    id: DepositEventIdV1,
    note: &NoteOpeningV1,
    commitment: [u8; 32],
    nonce_seed: u8,
    checkpoint: Option<LaneForestWalletCheckpointBindingV2>,
) -> (ForestFinalizedAppendEventV2, LaneForestWalletTxnIntentV2) {
    let event = deposit_event(state, id, commitment);
    let (_, binding) = sealed_note(cipher, id, note, nonce_seed);
    let intent = LaneForestWalletTxnIntentV2::new_v2(
        finalized_block(&event, parent),
        event.clone(),
        cipher.cipher_id(),
        vec![binding],
        vec![],
        checkpoint,
        None,
    )
    .unwrap();
    (event, intent)
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ProjectedNote {
    id: DepositEventIdV1,
    access: SealedNoteAccessV1,
    spent: bool,
    sealed_length: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ProjectedState {
    head: FinalizedChainPointV1,
    retained_events: usize,
    checkpoints: usize,
    lane_sequences: [u64; 8],
    notes: Vec<ProjectedNote>,
}

fn event_key(id: DepositEventIdV1) -> (u64, [u8; 32], [u8; 64], u16, u16) {
    (
        id.point().slot(),
        *id.point().block_hash(),
        *id.transaction_signature(),
        id.instruction_index(),
        id.event_index(),
    )
}

fn project(state: &LaneForestWalletCommittedStateV2) -> ProjectedState {
    let lane_sequences = core::array::from_fn(|index| {
        state
            .lane_state()
            .lane(LaneIdV2::new(index as u8).unwrap())
            .0
            .value
            .tree
            .next_leaf_index
    });
    let mut notes = state
        .notes()
        .iter()
        .map(|note| ProjectedNote {
            id: note.event_id(),
            access: note.access(),
            spent: note.is_spent(),
            sealed_length: note.sealed_note().len(),
        })
        .collect::<Vec<_>>();
    notes.sort_by_key(|note| event_key(note.id));
    ProjectedState {
        head: state.finalized_head(),
        retained_events: state.lane_state().retained_event_count_v2(),
        checkpoints: state.lane_state().checkpoint_count(),
        lane_sequences,
        notes,
    }
}

#[derive(Clone)]
struct PureExpected(ProjectedState);

impl PureExpected {
    fn from_committed(state: &LaneForestWalletCommittedStateV2) -> Self {
        Self(project(state))
    }

    fn apply_intent(&mut self, intent: &LaneForestWalletTxnIntentV2, has_checkpoint: bool) {
        self.0.head = intent.event().point();
        self.0.retained_events += 1;
        self.0.lane_sequences[intent.event().lane_id.as_u8() as usize] += 1;
        self.0.checkpoints += usize::from(has_checkpoint);
        for spend in intent.spends() {
            self.0
                .notes
                .iter_mut()
                .find(|note| note.id == spend.input_event_id())
                .unwrap()
                .spent = true;
        }
        self.0
            .notes
            .extend(intent.notes().iter().map(|note| ProjectedNote {
                id: note.event_id(),
                access: note.access(),
                spent: false,
                sealed_length: note.sealed_note().len(),
            }));
        self.0.notes.sort_by_key(|note| event_key(note.id));
    }
}

struct NeverAuthorizeSpend;

impl LocalSpendAuthenticatorV1 for NeverAuthorizeSpend {
    fn authenticates_spend_v1(&self, _: DepositEventIdV1, _: &[u8], _: &[u8; 32]) -> bool {
        false
    }
}

struct ExactSpendAuthenticator {
    input: DepositEventIdV1,
    nullifier: [u8; 32],
}

impl LocalSpendAuthenticatorV1 for ExactSpendAuthenticator {
    fn authenticates_spend_v1(
        &self,
        input_event_id: DepositEventIdV1,
        sealed_note: &[u8],
        nullifier: &[u8; 32],
    ) -> bool {
        input_event_id == self.input && !sealed_note.is_empty() && nullifier == &self.nullifier
    }
}

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

#[test]
fn production_clean_replay_tentative_reorg_and_same_lane_order_match_pure_state() {
    let fixture = empty_activation_fixture("clean");
    let activation = fixture.activation();
    let path = fixture.transaction_path();
    let mut coordinator =
        LaneForestWalletTxnCoordinatorV2::open_or_create_v2(&path, activation, &fixture.cipher)
            .unwrap();
    let mut expected = PureExpected::from_committed(coordinator.committed_state().unwrap());

    let lane = LaneIdV2::new(0).unwrap();
    let (note, commitment) = note_for_lane(lane, 1_000, 17, 2_000);
    let id = event_id(101, 0x41, 0);
    let (event, intent) = finalized_deposit_intent(
        coordinator.committed_state().unwrap().lane_state(),
        &fixture.cipher,
        expected.0.head,
        id,
        &note,
        commitment,
        0x80,
        None,
    );
    let initial = expected.0.clone();
    assert_eq!(
        coordinator
            .observe_tentative_v2(
                event.clone(),
                LaneForestWalletTentativeCommitmentV2::Unfinalized,
                [0xe1; 32]
            )
            .unwrap(),
        LaneForestWalletTentativeUpdateV2::Observed
    );
    assert_eq!(
        coordinator
            .observe_tentative_v2(
                event.clone(),
                LaneForestWalletTentativeCommitmentV2::Confirmed,
                [0xe1; 32]
            )
            .unwrap(),
        LaneForestWalletTentativeUpdateV2::Promoted
    );
    assert_eq!(project(coordinator.committed_state().unwrap()), initial);
    assert_eq!(coordinator.tentative_observations().unwrap().len(), 1);
    assert_eq!(
        coordinator
            .reorg_tentative_v2(&event, [0xe2; 32], [0xe1; 32])
            .unwrap(),
        LaneForestWalletTentativeUpdateV2::Removed
    );
    assert!(coordinator.tentative_observations().unwrap().is_empty());

    coordinator
        .observe_tentative_v2(
            event.clone(),
            LaneForestWalletTentativeCommitmentV2::Confirmed,
            [0xe1; 32],
        )
        .unwrap();
    assert!(matches!(
        coordinator
            .prepare_finalized_v2(intent.clone(), &fixture.cipher, &NeverAuthorizeSpend)
            .unwrap(),
        LaneForestWalletTxnPrepareV2::Prepared(_)
    ));
    assert_eq!(
        coordinator.pending_phase_v2().unwrap(),
        Some(LaneForestWalletTxnPhaseV2::Prepared)
    );
    assert_eq!(
        coordinator.committed_state().err(),
        Some(LaneForestWalletTxnErrorV2::PendingTransaction)
    );
    assert!(matches!(
        coordinator.recover_to_committed_v2().unwrap(),
        LaneForestWalletTxnRecoveryV2::Committed(_)
    ));
    expected.apply_intent(&intent, false);
    assert_eq!(project(coordinator.committed_state().unwrap()), expected.0);
    assert!(coordinator.tentative_observations().unwrap().is_empty());
    assert_eq!(
        coordinator.recover_to_committed_v2().unwrap(),
        LaneForestWalletTxnRecoveryV2::NoPending
    );

    let committed = project(coordinator.committed_state().unwrap());
    assert!(matches!(
        coordinator
            .prepare_finalized_v2(intent.clone(), &fixture.cipher, &NeverAuthorizeSpend)
            .unwrap(),
        LaneForestWalletTxnPrepareV2::AlreadyPresent {
            phase: LaneForestWalletTxnPhaseV2::Committed,
            ..
        }
    ));
    assert_eq!(project(coordinator.committed_state().unwrap()), committed);

    let mut conflict_event = event.clone();
    let ForestFinalizedAppendKindV2::Deposit { encrypted_note, .. } = &mut conflict_event.kind
    else {
        unreachable!("fixture is a deposit")
    };
    *encrypted_note = Some([0x33; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES]);
    let conflict = LaneForestWalletTxnIntentV2::new_v2(
        finalized_block(&conflict_event, initial.head),
        conflict_event,
        fixture.cipher.cipher_id(),
        vec![],
        vec![],
        None,
        None,
    )
    .unwrap();
    assert_eq!(
        coordinator.prepare_finalized_v2(conflict, &fixture.cipher, &NeverAuthorizeSpend),
        Err(LaneForestWalletTxnErrorV2::EventConflict)
    );
    assert_eq!(
        coordinator.reorg_tentative_v2(&event, [0xe2; 32], [0xe1; 32]),
        Err(LaneForestWalletTxnErrorV2::FinalizedRollback)
    );
    assert_eq!(project(coordinator.committed_state().unwrap()), committed);

    let lane_state = coordinator.committed_state().unwrap().lane_state().clone();
    let (second_note, second_commitment) = note_for_lane(lane, 1_100, 19, 2_100);
    let (_, second_intent) = finalized_deposit_intent(
        &lane_state,
        &fixture.cipher,
        expected.0.head,
        event_id(102, 0x51, 0),
        &second_note,
        second_commitment,
        0xa0,
        None,
    );
    coordinator
        .prepare_finalized_v2(second_intent.clone(), &fixture.cipher, &NeverAuthorizeSpend)
        .unwrap();
    coordinator.recover_to_committed_v2().unwrap();
    expected.apply_intent(&second_intent, false);
    assert_eq!(project(coordinator.committed_state().unwrap()), expected.0);
    assert_eq!(expected.0.lane_sequences[0], 2);
}

#[test]
fn cross_lane_finalized_spend_cannot_be_unauthorized_replayed_or_resurrected() {
    let fixture = empty_activation_fixture("spend");
    let mut coordinator = LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
        fixture.transaction_path(),
        fixture.activation(),
        &fixture.cipher,
    )
    .unwrap();
    let mut expected = PureExpected::from_committed(coordinator.committed_state().unwrap());
    let lane_zero = LaneIdV2::new(0).unwrap();
    let (input_note, input_commitment) = note_for_lane(lane_zero, 1_000, 31, 2_000);
    let input_id = event_id(101, 0x41, 0);
    let (_, deposit) = finalized_deposit_intent(
        coordinator.committed_state().unwrap().lane_state(),
        &fixture.cipher,
        expected.0.head,
        input_id,
        &input_note,
        input_commitment,
        0x80,
        None,
    );
    coordinator
        .prepare_finalized_v2(deposit.clone(), &fixture.cipher, &NeverAuthorizeSpend)
        .unwrap();
    coordinator.recover_to_committed_v2().unwrap();
    expected.apply_intent(&deposit, false);

    let (recipient, recipient_commitment) =
        note_for_lane(LaneIdV2::new(2).unwrap(), 1_100, 11, 2_100);
    let (change, change_commitment) = note_for_lane(LaneIdV2::new(3).unwrap(), 1_200, 20, 2_200);
    let recipient_id = event_id(102, 0x51, 0);
    let change_id = event_id(102, 0x51, 1);
    let nullifier = encode_digest_canonical(&digest(1));
    assert_eq!(nullifier[0] & 7, 1);
    let transfer_event = private_transfer_event(
        coordinator.committed_state().unwrap().lane_state(),
        recipient_id,
        change_id,
        nullifier,
        recipient_commitment,
        change_commitment,
    );
    let (_, recipient_binding) = sealed_note(&fixture.cipher, recipient_id, &recipient, 0xa0);
    let (_, change_binding) = sealed_note(&fixture.cipher, change_id, &change, 0xc0);
    let spend = LaneForestWalletSpendBindingV2::from_authenticated_update_v2(
        AuthenticatedSpentNoteUpdateV1 {
            input_event_id: input_id,
            transition_output_id: recipient_id,
            nullifier,
        },
    )
    .unwrap();
    let transfer = LaneForestWalletTxnIntentV2::new_v2(
        finalized_block(&transfer_event, expected.0.head),
        transfer_event.clone(),
        fixture.cipher.cipher_id(),
        vec![recipient_binding, change_binding],
        vec![spend],
        None,
        None,
    )
    .unwrap();
    let before_spend = project(coordinator.committed_state().unwrap());
    assert_eq!(
        coordinator.prepare_finalized_v2(transfer.clone(), &fixture.cipher, &NeverAuthorizeSpend),
        Err(LaneForestWalletTxnErrorV2::SpendNotAuthorized)
    );
    assert_eq!(
        project(coordinator.committed_state().unwrap()),
        before_spend
    );

    let authenticator = ExactSpendAuthenticator {
        input: input_id,
        nullifier,
    };
    coordinator
        .prepare_finalized_v2(transfer.clone(), &fixture.cipher, &authenticator)
        .unwrap();
    coordinator.recover_to_committed_v2().unwrap();
    expected.apply_intent(&transfer, false);
    assert_eq!(project(coordinator.committed_state().unwrap()), expected.0);
    assert_eq!(expected.0.lane_sequences[0], 1);
    assert_eq!(expected.0.lane_sequences[1], 1);
    assert!(
        expected
            .0
            .notes
            .iter()
            .find(|note| note.id == input_id)
            .unwrap()
            .spent
    );

    let committed = project(coordinator.committed_state().unwrap());
    assert_eq!(
        coordinator.reorg_tentative_v2(&transfer_event, [0xe2; 32], [0xe1; 32]),
        Err(LaneForestWalletTxnErrorV2::FinalizedRollback)
    );
    assert!(matches!(
        coordinator
            .prepare_finalized_v2(transfer, &fixture.cipher, &authenticator)
            .unwrap(),
        LaneForestWalletTxnPrepareV2::AlreadyPresent { .. }
    ));
    assert_eq!(project(coordinator.committed_state().unwrap()), committed);
}

const ATOMIC_BOUNDARIES: [LaneForestWalletTxnAtomicBoundaryV2; 4] = [
    LaneForestWalletTxnAtomicBoundaryV2::TemporaryWrite,
    LaneForestWalletTxnAtomicBoundaryV2::TemporaryFileSync,
    LaneForestWalletTxnAtomicBoundaryV2::TargetRename,
    LaneForestWalletTxnAtomicBoundaryV2::ParentDirectorySync,
];

fn drive_finalized_to_atomic_fault<A: LocalSpendAuthenticatorV1>(
    coordinator: &mut LaneForestWalletTxnCoordinatorV2,
    intent: LaneForestWalletTxnIntentV2,
    cipher: &NoteStoreCipherV1,
    authenticator: &A,
    write: LaneForestWalletTxnWriteV2,
    faults: &mut AtomicFaultOnce,
) -> Result<(), LaneForestWalletTxnErrorV2> {
    match write {
        LaneForestWalletTxnWriteV2::Prepared => coordinator
            .prepare_finalized_with_faults_v2(intent, cipher, authenticator, faults)
            .map(|_| ()),
        LaneForestWalletTxnWriteV2::StoresApplied => {
            coordinator.prepare_finalized_v2(intent, cipher, authenticator)?;
            coordinator
                .advance_recovery_with_faults_v2(faults)
                .map(|_| ())
        }
        LaneForestWalletTxnWriteV2::Committed => {
            coordinator.prepare_finalized_v2(intent, cipher, authenticator)?;
            coordinator.advance_recovery_v2()?;
            coordinator
                .advance_recovery_with_faults_v2(faults)
                .map(|_| ())
        }
        _ => unreachable!("finalized phase driver accepts only transaction writes"),
    }
}

#[test]
fn every_production_phase_atomic_boundary_recovers_to_pure_pre_or_post_state() {
    let writes = [
        LaneForestWalletTxnWriteV2::Prepared,
        LaneForestWalletTxnWriteV2::StoresApplied,
        LaneForestWalletTxnWriteV2::Committed,
    ];
    for (write_index, write) in writes.into_iter().enumerate() {
        for (boundary_index, boundary) in ATOMIC_BOUNDARIES.into_iter().enumerate() {
            let fixture =
                empty_activation_fixture(&format!("atomic-{write_index}-{boundary_index}"));
            let activation = fixture.activation();
            let path = fixture.transaction_path();
            let mut coordinator = LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
                &path,
                activation.clone(),
                &fixture.cipher,
            )
            .unwrap();
            let pre = project(coordinator.committed_state().unwrap());
            let (note, commitment) = note_for_lane(LaneIdV2::new(0).unwrap(), 1_000, 17, 2_000);
            let (_, intent) = finalized_deposit_intent(
                coordinator.committed_state().unwrap().lane_state(),
                &fixture.cipher,
                pre.head,
                event_id(101, 0x41, 0),
                &note,
                commitment,
                0x80,
                None,
            );
            let mut expected_post = PureExpected(pre.clone());
            expected_post.apply_intent(&intent, false);
            let target = LaneForestWalletTxnAtomicFaultPointV2 { write, boundary };
            let mut faults = AtomicFaultOnce {
                target,
                fired: false,
            };
            assert_eq!(
                drive_finalized_to_atomic_fault(
                    &mut coordinator,
                    intent,
                    &fixture.cipher,
                    &NeverAuthorizeSpend,
                    write,
                    &mut faults,
                ),
                Err(LaneForestWalletTxnErrorV2::InjectedAtomicFault(target))
            );
            assert!(faults.fired);
            assert!(coordinator.is_poisoned_v2());
            assert_eq!(
                coordinator.committed_state().err(),
                Some(LaneForestWalletTxnErrorV2::Poisoned)
            );
            drop(coordinator);

            let mut restarted = LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
                &path,
                activation,
                &fixture.cipher,
            )
            .unwrap();
            let pending = restarted.pending_phase_v2().unwrap();
            if pending.is_some() {
                assert!(matches!(
                    restarted.recover_to_committed_v2().unwrap(),
                    LaneForestWalletTxnRecoveryV2::Committed(_)
                ));
            }
            assert_eq!(
                restarted.recover_to_committed_v2().unwrap(),
                LaneForestWalletTxnRecoveryV2::NoPending
            );
            let expected = if write == LaneForestWalletTxnWriteV2::Prepared
                && matches!(
                    boundary,
                    LaneForestWalletTxnAtomicBoundaryV2::TemporaryWrite
                        | LaneForestWalletTxnAtomicBoundaryV2::TemporaryFileSync
                ) {
                &pre
            } else {
                &expected_post.0
            };
            assert_eq!(project(restarted.committed_state().unwrap()), *expected);
        }
    }
}

#[test]
fn rich_transfer_spend_notes_lane_and_checkpoint_recover_at_every_atomic_boundary() {
    let writes = [
        LaneForestWalletTxnWriteV2::Prepared,
        LaneForestWalletTxnWriteV2::StoresApplied,
        LaneForestWalletTxnWriteV2::Committed,
    ];
    for (write_index, write) in writes.into_iter().enumerate() {
        for (boundary_index, boundary) in ATOMIC_BOUNDARIES.into_iter().enumerate() {
            let fixture = empty_activation_fixture(&format!("rich-{write_index}-{boundary_index}"));
            let activation = fixture.activation();
            let path = fixture.transaction_path();
            let mut coordinator = LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
                &path,
                activation.clone(),
                &fixture.cipher,
            )
            .unwrap();
            let lane_zero = LaneIdV2::new(0).unwrap();
            let (input_note, input_commitment) = note_for_lane(lane_zero, 1_000, 31, 2_000);
            let input_id = event_id(101, 0x41, 0);
            let (_, deposit) = finalized_deposit_intent(
                coordinator.committed_state().unwrap().lane_state(),
                &fixture.cipher,
                coordinator.committed_state().unwrap().finalized_head(),
                input_id,
                &input_note,
                input_commitment,
                0x40,
                None,
            );
            coordinator
                .prepare_finalized_v2(deposit, &fixture.cipher, &NeverAuthorizeSpend)
                .unwrap();
            coordinator.recover_to_committed_v2().unwrap();

            let (recipient, recipient_commitment) =
                note_for_lane(LaneIdV2::new(2).unwrap(), 1_100, 11, 2_100);
            let (change, change_commitment) =
                note_for_lane(LaneIdV2::new(3).unwrap(), 1_200, 20, 2_200);
            let recipient_id = event_id(102, 0x51, 0);
            let change_id = event_id(102, 0x51, 1);
            let nullifier = encode_digest_canonical(&digest(1));
            let transfer_event = private_transfer_event(
                coordinator.committed_state().unwrap().lane_state(),
                recipient_id,
                change_id,
                nullifier,
                recipient_commitment,
                change_commitment,
            );
            let mut after_event = coordinator.committed_state().unwrap().lane_state().clone();
            after_event
                .ingest_finalized_append_v2(transfer_event.clone(), None)
                .unwrap();
            let checkpoint = checkpoint_binding(&after_event, transfer_event.point());
            let (_, recipient_binding) =
                sealed_note(&fixture.cipher, recipient_id, &recipient, 0x80);
            let (_, change_binding) = sealed_note(&fixture.cipher, change_id, &change, 0xa0);
            let spend = LaneForestWalletSpendBindingV2::from_authenticated_update_v2(
                AuthenticatedSpentNoteUpdateV1 {
                    input_event_id: input_id,
                    transition_output_id: recipient_id,
                    nullifier,
                },
            )
            .unwrap();
            let intent = LaneForestWalletTxnIntentV2::new_v2(
                finalized_block(
                    &transfer_event,
                    coordinator.committed_state().unwrap().finalized_head(),
                ),
                transfer_event,
                fixture.cipher.cipher_id(),
                vec![recipient_binding, change_binding],
                vec![spend],
                Some(checkpoint),
                None,
            )
            .unwrap();
            let authenticator = ExactSpendAuthenticator {
                input: input_id,
                nullifier,
            };
            let pre = project(coordinator.committed_state().unwrap());
            let mut expected_post = PureExpected(pre.clone());
            expected_post.apply_intent(&intent, true);
            let target = LaneForestWalletTxnAtomicFaultPointV2 { write, boundary };
            let mut faults = AtomicFaultOnce {
                target,
                fired: false,
            };
            assert_eq!(
                drive_finalized_to_atomic_fault(
                    &mut coordinator,
                    intent.clone(),
                    &fixture.cipher,
                    &authenticator,
                    write,
                    &mut faults,
                ),
                Err(LaneForestWalletTxnErrorV2::InjectedAtomicFault(target))
            );
            assert!(faults.fired && coordinator.is_poisoned_v2());
            drop(coordinator);

            let mut restarted = LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
                &path,
                activation,
                &fixture.cipher,
            )
            .unwrap();
            if restarted.pending_phase_v2().unwrap().is_some() {
                restarted.recover_to_committed_v2().unwrap();
            }
            restarted.recover_to_committed_v2().unwrap();
            let expected_after_recovery = if write == LaneForestWalletTxnWriteV2::Prepared
                && matches!(
                    boundary,
                    LaneForestWalletTxnAtomicBoundaryV2::TemporaryWrite
                        | LaneForestWalletTxnAtomicBoundaryV2::TemporaryFileSync
                ) {
                &pre
            } else {
                &expected_post.0
            };
            assert_eq!(
                project(restarted.committed_state().unwrap()),
                *expected_after_recovery
            );

            match restarted
                .prepare_finalized_v2(intent.clone(), &fixture.cipher, &authenticator)
                .unwrap()
            {
                LaneForestWalletTxnPrepareV2::Prepared(_) => {
                    restarted.recover_to_committed_v2().unwrap();
                }
                LaneForestWalletTxnPrepareV2::AlreadyPresent { .. } => {}
            }
            assert_eq!(
                project(restarted.committed_state().unwrap()),
                expected_post.0
            );
            assert_eq!(restarted.committed_state().unwrap().notes().len(), 3);
            assert_eq!(
                restarted
                    .committed_state()
                    .unwrap()
                    .spendable_unspent_notes_v2()
                    .count(),
                2
            );
            assert_eq!(
                restarted
                    .committed_state()
                    .unwrap()
                    .lane_state()
                    .checkpoint_count(),
                1
            );
        }
    }
}

#[test]
fn fixed_seed_production_crash_reopen_replay_sequences_match_pure_transition() {
    let writes = [
        LaneForestWalletTxnWriteV2::Prepared,
        LaneForestWalletTxnWriteV2::StoresApplied,
        LaneForestWalletTxnWriteV2::Committed,
    ];
    let lanes = [0u8, 1, 0, 2];
    for seed in 0..6_u64 {
        let fixture = empty_activation_fixture(&format!("sequence-{seed}"));
        let activation = fixture.activation();
        let path = fixture.transaction_path();
        let mut coordinator = LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
            &path,
            activation.clone(),
            &fixture.cipher,
        )
        .unwrap();
        let mut expected = PureExpected::from_committed(coordinator.committed_state().unwrap());
        let mut random = seed ^ 0x9e37_79b9_7f4a_7c15;
        for (step, lane_byte) in lanes.into_iter().enumerate() {
            random = random
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let write = writes[(random as usize) % writes.len()];
            let boundary = ATOMIC_BOUNDARIES[((random >> 16) as usize) % ATOMIC_BOUNDARIES.len()];
            let lane = LaneIdV2::new(lane_byte).unwrap();
            let (note, commitment) = note_for_lane(
                lane,
                2_000 + seed as u32 * 100 + step as u32,
                10 + step as u32,
                4_000 + seed as u32 * 1_000 + step as u32 * 10_000,
            );
            let id = event_id(
                101 + step as u64,
                0x31 + u8::try_from(step).unwrap() * 0x10,
                0,
            );
            let (event, intent) = finalized_deposit_intent(
                coordinator.committed_state().unwrap().lane_state(),
                &fixture.cipher,
                expected.0.head,
                id,
                &note,
                commitment,
                0x20 + u8::try_from(step).unwrap() * 0x20,
                None,
            );
            coordinator
                .observe_tentative_v2(
                    event,
                    LaneForestWalletTentativeCommitmentV2::Confirmed,
                    [0xe0 + u8::try_from(step).unwrap(); 32],
                )
                .unwrap();
            let pre = expected.0.clone();
            let mut post = expected.clone();
            post.apply_intent(&intent, false);
            let target = LaneForestWalletTxnAtomicFaultPointV2 { write, boundary };
            let mut faults = AtomicFaultOnce {
                target,
                fired: false,
            };
            assert_eq!(
                drive_finalized_to_atomic_fault(
                    &mut coordinator,
                    intent.clone(),
                    &fixture.cipher,
                    &NeverAuthorizeSpend,
                    write,
                    &mut faults,
                ),
                Err(LaneForestWalletTxnErrorV2::InjectedAtomicFault(target)),
                "seed {seed}, step {step}"
            );
            drop(coordinator);

            coordinator = LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
                &path,
                activation.clone(),
                &fixture.cipher,
            )
            .unwrap();
            if coordinator.pending_phase_v2().unwrap().is_some() {
                coordinator.recover_to_committed_v2().unwrap();
            }
            coordinator.recover_to_committed_v2().unwrap();
            let expected_after_recovery = if write == LaneForestWalletTxnWriteV2::Prepared
                && matches!(
                    boundary,
                    LaneForestWalletTxnAtomicBoundaryV2::TemporaryWrite
                        | LaneForestWalletTxnAtomicBoundaryV2::TemporaryFileSync
                ) {
                &pre
            } else {
                &post.0
            };
            assert_eq!(
                project(coordinator.committed_state().unwrap()),
                *expected_after_recovery,
                "seed {seed}, step {step}, recovery"
            );

            match coordinator
                .prepare_finalized_v2(intent.clone(), &fixture.cipher, &NeverAuthorizeSpend)
                .unwrap()
            {
                LaneForestWalletTxnPrepareV2::Prepared(_) => {
                    coordinator.recover_to_committed_v2().unwrap();
                }
                LaneForestWalletTxnPrepareV2::AlreadyPresent { .. } => {}
            }
            assert!(matches!(
                coordinator
                    .prepare_finalized_v2(intent, &fixture.cipher, &NeverAuthorizeSpend)
                    .unwrap(),
                LaneForestWalletTxnPrepareV2::AlreadyPresent {
                    phase: LaneForestWalletTxnPhaseV2::Committed,
                    ..
                }
            ));
            assert!(coordinator.tentative_observations().unwrap().is_empty());
            assert_eq!(
                project(coordinator.committed_state().unwrap()),
                post.0,
                "seed {seed}, step {step}, replay"
            );
            expected = post;
        }
    }
}

fn drive_finalized_to_logical_fault(
    coordinator: &mut LaneForestWalletTxnCoordinatorV2,
    intent: LaneForestWalletTxnIntentV2,
    cipher: &NoteStoreCipherV1,
    target: LaneForestWalletTxnFaultPointV2,
    faults: &mut LogicalFaultOnce,
) -> Result<(), LaneForestWalletTxnErrorV2> {
    match target {
        LaneForestWalletTxnFaultPointV2::BeforePreparedReplace
        | LaneForestWalletTxnFaultPointV2::AfterPreparedReplace => coordinator
            .prepare_finalized_with_faults_v2(intent, cipher, &NeverAuthorizeSpend, faults)
            .map(|_| ()),
        LaneForestWalletTxnFaultPointV2::BeforeStoresAppliedReplace
        | LaneForestWalletTxnFaultPointV2::AfterStoresAppliedReplace => {
            coordinator.prepare_finalized_v2(intent, cipher, &NeverAuthorizeSpend)?;
            coordinator
                .advance_recovery_with_faults_v2(faults)
                .map(|_| ())
        }
        LaneForestWalletTxnFaultPointV2::BeforeCommittedReplace
        | LaneForestWalletTxnFaultPointV2::AfterCommittedReplace => {
            coordinator.prepare_finalized_v2(intent, cipher, &NeverAuthorizeSpend)?;
            coordinator.advance_recovery_v2()?;
            coordinator
                .advance_recovery_with_faults_v2(faults)
                .map(|_| ())
        }
    }
}

#[test]
fn before_and_after_each_journal_phase_recover_deterministically_and_idempotently() {
    let targets = [
        LaneForestWalletTxnFaultPointV2::BeforePreparedReplace,
        LaneForestWalletTxnFaultPointV2::AfterPreparedReplace,
        LaneForestWalletTxnFaultPointV2::BeforeStoresAppliedReplace,
        LaneForestWalletTxnFaultPointV2::AfterStoresAppliedReplace,
        LaneForestWalletTxnFaultPointV2::BeforeCommittedReplace,
        LaneForestWalletTxnFaultPointV2::AfterCommittedReplace,
    ];
    for (index, target) in targets.into_iter().enumerate() {
        let fixture = empty_activation_fixture(&format!("logical-{index}"));
        let activation = fixture.activation();
        let path = fixture.transaction_path();
        let mut coordinator = LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
            &path,
            activation.clone(),
            &fixture.cipher,
        )
        .unwrap();
        let pre = project(coordinator.committed_state().unwrap());
        let (note, commitment) = note_for_lane(LaneIdV2::new(0).unwrap(), 1_000, 17, 2_000);
        let (_, intent) = finalized_deposit_intent(
            coordinator.committed_state().unwrap().lane_state(),
            &fixture.cipher,
            pre.head,
            event_id(101, 0x41, 0),
            &note,
            commitment,
            0x80,
            None,
        );
        let mut post = PureExpected(pre.clone());
        post.apply_intent(&intent, false);
        let mut faults = LogicalFaultOnce {
            target,
            fired: false,
        };
        assert_eq!(
            drive_finalized_to_logical_fault(
                &mut coordinator,
                intent,
                &fixture.cipher,
                target,
                &mut faults,
            ),
            Err(LaneForestWalletTxnErrorV2::InjectedFault(target))
        );
        assert!(faults.fired && coordinator.is_poisoned_v2());
        drop(coordinator);

        let mut restarted =
            LaneForestWalletTxnCoordinatorV2::open_or_create_v2(&path, activation, &fixture.cipher)
                .unwrap();
        if restarted.pending_phase_v2().unwrap().is_some() {
            restarted.recover_to_committed_v2().unwrap();
        }
        restarted.recover_to_committed_v2().unwrap();
        let expected = if target == LaneForestWalletTxnFaultPointV2::BeforePreparedReplace {
            &pre
        } else {
            &post.0
        };
        assert_eq!(project(restarted.committed_state().unwrap()), *expected);
    }
}

#[test]
fn activation_and_tentative_ledger_atomic_boundaries_never_expose_mixed_state() {
    for (index, boundary) in ATOMIC_BOUNDARIES.into_iter().enumerate() {
        let fixture = empty_activation_fixture(&format!("activation-boundary-{index}"));
        let activation = fixture.activation();
        let path = fixture.transaction_path();
        let target = LaneForestWalletTxnAtomicFaultPointV2 {
            write: LaneForestWalletTxnWriteV2::Activation,
            boundary,
        };
        let mut faults = AtomicFaultOnce {
            target,
            fired: false,
        };
        let opened = LaneForestWalletTxnCoordinatorV2::open_or_create_with_faults_v2(
            &path,
            activation.clone(),
            &fixture.cipher,
            &mut faults,
        );
        assert_eq!(
            opened.err(),
            Some(LaneForestWalletTxnErrorV2::InjectedAtomicFault(target))
        );
        assert!(faults.fired);
        let restarted =
            LaneForestWalletTxnCoordinatorV2::open_or_create_v2(&path, activation, &fixture.cipher)
                .unwrap();
        assert_eq!(restarted.records().unwrap().len(), 0);
        assert_eq!(restarted.tentative_observations().unwrap().len(), 0);
        assert_eq!(
            restarted.committed_state().unwrap().finalized_head(),
            fixture.wallet.scan_state().anchor()
        );
    }

    for (index, boundary) in ATOMIC_BOUNDARIES.into_iter().enumerate() {
        let fixture = empty_activation_fixture(&format!("tentative-boundary-{index}"));
        let activation = fixture.activation();
        let path = fixture.transaction_path();
        let mut coordinator = LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
            &path,
            activation.clone(),
            &fixture.cipher,
        )
        .unwrap();
        let (_, commitment) = note_for_lane(LaneIdV2::new(0).unwrap(), 1_000, 17, 2_000);
        let event = deposit_event(
            coordinator.committed_state().unwrap().lane_state(),
            event_id(101, 0x41, 0),
            commitment,
        );
        let target = LaneForestWalletTxnAtomicFaultPointV2 {
            write: LaneForestWalletTxnWriteV2::TentativeObservation,
            boundary,
        };
        let mut faults = AtomicFaultOnce {
            target,
            fired: false,
        };
        assert_eq!(
            coordinator.observe_tentative_with_faults_v2(
                event,
                LaneForestWalletTentativeCommitmentV2::Confirmed,
                [0xe1; 32],
                &mut faults,
            ),
            Err(LaneForestWalletTxnErrorV2::InjectedAtomicFault(target))
        );
        assert!(coordinator.is_poisoned_v2());
        drop(coordinator);
        let restarted =
            LaneForestWalletTxnCoordinatorV2::open_or_create_v2(&path, activation, &fixture.cipher)
                .unwrap();
        let expected_count = usize::from(matches!(
            boundary,
            LaneForestWalletTxnAtomicBoundaryV2::TargetRename
                | LaneForestWalletTxnAtomicBoundaryV2::ParentDirectorySync
        ));
        assert_eq!(
            restarted.tentative_observations().unwrap().len(),
            expected_count
        );
        assert_eq!(restarted.records().unwrap().len(), 0);
        assert_eq!(
            restarted.committed_state().unwrap().finalized_head(),
            fixture.wallet.scan_state().anchor()
        );
    }
}

#[test]
fn checkpoint_images_and_finalized_order_are_validated_before_state_changes() {
    let fixture = empty_activation_fixture("checkpoint-order");
    let mut coordinator = LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
        fixture.transaction_path(),
        fixture.activation(),
        &fixture.cipher,
    )
    .unwrap();
    let before = project(coordinator.committed_state().unwrap());
    let (note, commitment) = note_for_lane(LaneIdV2::new(0).unwrap(), 1_000, 17, 2_000);
    let id = event_id(101, 0x41, 0);
    let event = deposit_event(
        coordinator.committed_state().unwrap().lane_state(),
        id,
        commitment,
    );
    let (_, note_binding) = sealed_note(&fixture.cipher, id, &note, 0x80);

    // This checkpoint authenticates the pre-event lanes and is stale for the
    // event's afterstate. Structural validation occurs on a clone.
    let stale_checkpoint = checkpoint_binding(
        coordinator.committed_state().unwrap().lane_state(),
        event.point(),
    );
    let stale = LaneForestWalletTxnIntentV2::new_v2(
        finalized_block(&event, before.head),
        event.clone(),
        fixture.cipher.cipher_id(),
        vec![note_binding.clone()],
        vec![],
        Some(stale_checkpoint),
        None,
    )
    .unwrap();
    assert!(matches!(
        coordinator.prepare_finalized_v2(stale, &fixture.cipher, &NeverAuthorizeSpend),
        Err(LaneForestWalletTxnErrorV2::Lane(_))
            | Err(LaneForestWalletTxnErrorV2::InvalidCheckpoint)
    ));
    assert_eq!(project(coordinator.committed_state().unwrap()), before);

    let mut event_afterstate = coordinator.committed_state().unwrap().lane_state().clone();
    event_afterstate
        .ingest_finalized_append_v2(event.clone(), None)
        .unwrap();
    let (master, master_image, lanes, mut unknown_address, checkpoint_image) =
        checkpoint_inputs(&event_afterstate);
    unknown_address[0] ^= 1;
    let unknown_checkpoint = LaneForestWalletCheckpointBindingV2::new_v2(
        event.point(),
        master,
        master_image,
        lanes,
        unknown_address,
        checkpoint_image,
    )
    .unwrap();
    let unknown = LaneForestWalletTxnIntentV2::new_v2(
        finalized_block(&event, before.head),
        event.clone(),
        fixture.cipher.cipher_id(),
        vec![note_binding.clone()],
        vec![],
        Some(unknown_checkpoint),
        None,
    )
    .unwrap();
    assert!(matches!(
        coordinator.prepare_finalized_v2(unknown, &fixture.cipher, &NeverAuthorizeSpend),
        Err(LaneForestWalletTxnErrorV2::Lane(_))
            | Err(LaneForestWalletTxnErrorV2::InvalidCheckpoint)
    ));
    assert_eq!(project(coordinator.committed_state().unwrap()), before);

    let valid_checkpoint = checkpoint_binding(&event_afterstate, event.point());
    let valid = LaneForestWalletTxnIntentV2::new_v2(
        finalized_block(&event, before.head),
        event.clone(),
        fixture.cipher.cipher_id(),
        vec![note_binding],
        vec![],
        Some(valid_checkpoint),
        None,
    )
    .unwrap();
    coordinator
        .prepare_finalized_v2(valid.clone(), &fixture.cipher, &NeverAuthorizeSpend)
        .unwrap();
    coordinator.recover_to_committed_v2().unwrap();
    let mut expected = PureExpected(before.clone());
    expected.apply_intent(&valid, true);
    assert_eq!(project(coordinator.committed_state().unwrap()), expected.0);

    // A lower canonical event identity in the same finalized block cannot be
    // inserted after the committed event.
    let lower_id = DepositEventIdV1::new(event.point(), [0x40; 64], 0, 0).unwrap();
    let (lower_note, lower_commitment) = note_for_lane(LaneIdV2::new(1).unwrap(), 1_100, 19, 2_100);
    let lower_event = deposit_event(
        coordinator.committed_state().unwrap().lane_state(),
        lower_id,
        lower_commitment,
    );
    let (_, lower_binding) = sealed_note(&fixture.cipher, lower_id, &lower_note, 0xa0);
    let lower = LaneForestWalletTxnIntentV2::new_v2(
        finalized_block(&lower_event, before.head),
        lower_event,
        fixture.cipher.cipher_id(),
        vec![lower_binding],
        vec![],
        None,
        None,
    )
    .unwrap();
    let committed = project(coordinator.committed_state().unwrap());
    assert_eq!(
        coordinator.prepare_finalized_v2(lower, &fixture.cipher, &NeverAuthorizeSpend),
        Err(LaneForestWalletTxnErrorV2::EventOutsideFinalizedOrder)
    );

    let (future_note, future_commitment) =
        note_for_lane(LaneIdV2::new(1).unwrap(), 1_200, 23, 2_200);
    let future_id = event_id(102, 0x51, 0);
    let future_event = deposit_event(
        coordinator.committed_state().unwrap().lane_state(),
        future_id,
        future_commitment,
    );
    let (_, future_binding) = sealed_note(&fixture.cipher, future_id, &future_note, 0xc0);
    let wrong_parent = point(99, 0x99);
    let discontinuous = LaneForestWalletTxnIntentV2::new_v2(
        finalized_block(&future_event, wrong_parent),
        future_event,
        fixture.cipher.cipher_id(),
        vec![future_binding],
        vec![],
        None,
        None,
    )
    .unwrap();
    assert_eq!(
        coordinator.prepare_finalized_v2(discontinuous, &fixture.cipher, &NeverAuthorizeSpend),
        Err(LaneForestWalletTxnErrorV2::FinalizedRollback)
    );
    assert_eq!(project(coordinator.committed_state().unwrap()), committed);
}

#[test]
fn cipher_event_nonce_lock_and_corrupt_image_fail_before_partial_mutation() {
    let fixture = empty_activation_fixture("cipher-corruption");
    let activation = fixture.activation();
    let path = fixture.transaction_path();
    let mut coordinator = LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
        &path,
        activation.clone(),
        &fixture.cipher,
    )
    .unwrap();
    let before = project(coordinator.committed_state().unwrap());
    let (note, commitment) = note_for_lane(LaneIdV2::new(0).unwrap(), 1_000, 17, 2_000);
    let id = event_id(101, 0x41, 0);
    let event = deposit_event(
        coordinator.committed_state().unwrap().lane_state(),
        id,
        commitment,
    );
    let (sealed, binding) = sealed_note(&fixture.cipher, id, &note, 0x80);

    let mut corrupt_sealed = sealed.clone();
    corrupt_sealed.sealed_note[64] ^= 1;
    let corrupt_binding =
        LaneForestWalletNoteBindingV2::from_sealed_recovered_note_v2(&corrupt_sealed).unwrap();
    let corrupt_intent = LaneForestWalletTxnIntentV2::new_v2(
        finalized_block(&event, before.head),
        event.clone(),
        fixture.cipher.cipher_id(),
        vec![corrupt_binding],
        vec![],
        None,
        None,
    )
    .unwrap();
    assert_eq!(
        coordinator.prepare_finalized_v2(corrupt_intent, &fixture.cipher, &NeverAuthorizeSpend),
        Err(LaneForestWalletTxnErrorV2::InvalidNote)
    );
    assert_eq!(project(coordinator.committed_state().unwrap()), before);

    let foreign_id = event_id(101, 0x42, 0);
    let (mut copied, _) = sealed_note(&fixture.cipher, foreign_id, &note, 0x90);
    copied.event_id = id;
    let copied_binding =
        LaneForestWalletNoteBindingV2::from_sealed_recovered_note_v2(&copied).unwrap();
    let copied_intent = LaneForestWalletTxnIntentV2::new_v2(
        finalized_block(&event, before.head),
        event.clone(),
        fixture.cipher.cipher_id(),
        vec![copied_binding],
        vec![],
        None,
        None,
    )
    .unwrap();
    assert_eq!(
        coordinator.prepare_finalized_v2(copied_intent, &fixture.cipher, &NeverAuthorizeSpend),
        Err(LaneForestWalletTxnErrorV2::InvalidNote)
    );

    let wrong_cipher = NoteStoreCipherV1::from_key_bytes([0x72; 32]).unwrap();
    let (_, wrong_binding) = sealed_note(&wrong_cipher, id, &note, 0xa0);
    let wrong_key_intent = LaneForestWalletTxnIntentV2::new_v2(
        finalized_block(&event, before.head),
        event.clone(),
        wrong_cipher.cipher_id(),
        vec![wrong_binding],
        vec![],
        None,
        None,
    )
    .unwrap();
    assert_eq!(
        coordinator.prepare_finalized_v2(wrong_key_intent, &fixture.cipher, &NeverAuthorizeSpend),
        Err(LaneForestWalletTxnErrorV2::NoteCipherMismatch)
    );
    assert_eq!(project(coordinator.committed_state().unwrap()), before);

    let valid = LaneForestWalletTxnIntentV2::new_v2(
        finalized_block(&event, before.head),
        event,
        fixture.cipher.cipher_id(),
        vec![binding],
        vec![],
        None,
        None,
    )
    .unwrap();
    coordinator
        .prepare_finalized_v2(valid, &fixture.cipher, &NeverAuthorizeSpend)
        .unwrap();
    coordinator.recover_to_committed_v2().unwrap();

    let (next_note, next_commitment) = note_for_lane(LaneIdV2::new(1).unwrap(), 1_100, 19, 2_100);
    let next_id = event_id(102, 0x51, 0);
    let next_event = deposit_event(
        coordinator.committed_state().unwrap().lane_state(),
        next_id,
        next_commitment,
    );
    let (_, colliding_binding) = sealed_note(&fixture.cipher, next_id, &next_note, 0x80);
    let collision = LaneForestWalletTxnIntentV2::new_v2(
        finalized_block(
            &next_event,
            coordinator.committed_state().unwrap().finalized_head(),
        ),
        next_event,
        fixture.cipher.cipher_id(),
        vec![colliding_binding],
        vec![],
        None,
        None,
    )
    .unwrap();
    let committed = project(coordinator.committed_state().unwrap());
    assert_eq!(
        coordinator.prepare_finalized_v2(collision, &fixture.cipher, &NeverAuthorizeSpend),
        Err(LaneForestWalletTxnErrorV2::DuplicateNonce)
    );
    assert_eq!(project(coordinator.committed_state().unwrap()), committed);

    let contender = LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
        &path,
        activation.clone(),
        &fixture.cipher,
    );
    assert!(contender.is_err());
    drop(coordinator);
    assert_eq!(
        LaneForestWalletTxnCoordinatorV2::open_or_create_v2(
            &path,
            activation.clone(),
            &wrong_cipher,
        )
        .err(),
        Some(LaneForestWalletTxnErrorV2::NoteCipherMismatch)
    );

    let mut image = fs::read(&path).unwrap();
    image[24] ^= 1;
    fs::write(&path, image).unwrap();
    assert_eq!(
        LaneForestWalletTxnCoordinatorV2::open_or_create_v2(&path, activation, &fixture.cipher,)
            .err(),
        Some(LaneForestWalletTxnErrorV2::ChecksumMismatch)
    );
}

struct DenyTopology;

impl LaneForestWalletActivationPolicyV2 for DenyTopology {
    fn approves_topology_transition_v2(
        &self,
        _: &[u8; 32],
        _: &[u8; 32],
        _: &[u8; 32],
        _: &[u8; 32],
        _: &[u8; 32],
    ) -> bool {
        false
    }
}

#[test]
fn activation_remains_default_off_and_rejects_denied_or_nonempty_v1_state() {
    let fixture = empty_activation_fixture("activation-denials");
    assert_eq!(
        EmptyV1LaneForestWalletActivationV2::from_empty_v1(
            &fixture.wallet,
            &fixture.witness,
            &fixture.relayer_admission,
            &fixture.relayer,
            &fixture.lane_state,
            &DenyTopology,
        )
        .err(),
        Some(LaneForestWalletTxnErrorV2::InvalidActivation)
    );

    let empty_witness = WalletWitnessStateV1::empty();
    let anchor = point(100, 0xa0);
    let mut nonempty_scan = ScanStateV1::new(
        scan_identity(),
        anchor,
        0,
        encode_digest_canonical(&empty_witness.tree().root),
    )
    .unwrap();
    nonempty_scan
        .advance_finalized_block_v1(FinalizedBlockV1::new(point(101, 0xa1), anchor).unwrap())
        .unwrap();
    let nonempty_wallet = DurableWalletStateV1::open_or_create_v1(
        fixture.directory.path("nonempty-wallet-v1.state"),
        nonempty_scan,
        fixture.cipher.cipher_id(),
    )
    .unwrap();
    assert_eq!(
        EmptyV1LaneForestWalletActivationV2::from_empty_v1(
            &nonempty_wallet,
            &fixture.witness,
            &fixture.relayer_admission,
            &fixture.relayer,
            &fixture.lane_state,
            &ApproveFixtureTopology,
        )
        .err(),
        Some(LaneForestWalletTxnErrorV2::LegacyStateNotEmpty)
    );
}

#[test]
fn empty_v1_activation_fixture_is_mechanically_valid_and_key_bound() {
    let fixture = empty_activation_fixture("activation-fixture");
    let activation = fixture.activation();
    assert_eq!(activation.note_cipher_id(), &fixture.cipher.cipher_id());
    assert_eq!(activation.anchor(), fixture.wallet.scan_state().anchor());
    assert_ne!(activation.activation_id(), &[0; 32]);

    let lane = LaneIdV2::new(0).unwrap();
    let (note, commitment) = note_for_lane(lane, 1_000, 17, 2_000);
    let id = event_id(101, 0x41, 0);
    let event = deposit_event(&fixture.lane_state, id, commitment);
    let (sealed, binding) = sealed_note(&fixture.cipher, id, &note, 0x80);
    assert_eq!(event.point(), point(101, 0x42));
    assert_eq!(binding.event_id(), id);
    assert!(binding.sealed_note() == sealed.sealed_note.as_slice());

    let (recipient, recipient_commitment) = note_for_lane(lane, 1_100, 19, 2_100);
    let (change, change_commitment) = note_for_lane(lane, 1_200, 23, 2_200);
    let transfer = private_transfer_event(
        &fixture.lane_state,
        event_id(102, 0x51, 0),
        event_id(102, 0x51, 1),
        encode_digest_canonical(&digest(77)),
        recipient_commitment,
        change_commitment,
    );
    let _ = sealed_note(&fixture.cipher, event_id(102, 0x51, 0), &recipient, 0xa0);
    let _ = sealed_note(&fixture.cipher, event_id(102, 0x51, 1), &change, 0xc0);
    assert!(matches!(
        transfer.kind,
        ForestFinalizedAppendKindV2::PrivateTransfer { .. }
    ));
}
