//! Default-off, crash-consistent V2 wallet/lane transaction envelope.
//!
//! This module deliberately does **not** mirror or mutate the active V1 wallet,
//! witness, relayer, or lane files. Activation accepts either an empty,
//! mutually consistent V1 snapshot or a fully validated populated migration
//! genesis. From that point the one checksummed file is the authoritative
//! logical wallet image: committed note/spend metadata,
//! canonical lane/witness/checkpoint state, finalized event history, and
//! finalized relayer correlation live under one `AtomicStateFileV1` lock.
//!
//! A transaction advances through `Prepared -> StoresApplied -> Committed` in
//! three independent atomic replacements. `StoresApplied` means that every
//! logical component afterstate is staged and checksum-verified inside this
//! envelope; it never means that separate V1 files were partially rewritten.
//! Readers see only `committed_state()`. Recovery is deterministic roll-forward
//! and never exposes or rolls back a staged finalized spend.
//!
//! Fault hooks cover both logical phase boundaries and every real
//! `AtomicStateFileV1` temporary-write, temporary-file-sync, target-rename,
//! and parent-directory-sync boundary. Any replace error poisons the live
//! handle because the durable target may already contain the new image.
//!
//! Deliberate default-off boundaries remain. Canonical authenticated empty
//! finalized blocks advance the same exact-parent cursor as eventful blocks.
//! A populated migration archives a quiescent ASRJ image and uses the separate
//! ownership journal for physical one-way handoff. Tentative reorg evidence is
//! supplied by the external quorum/finality capability; ASL2 validates exact
//! event/provider binding but does not itself query RPC.

use std::{collections::HashSet, io, path::Path};

use aspis_statement::pool_v1::IncrementalMerkleTreeV1;
use aspis_statement::{decode_digest_canonical, encode_digest_canonical};
use bincode::Options as _;
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};
use subtle::ConstantTimeEq;

use crate::{
    durable_state::{
        AtomicReplaceBoundaryV1, AtomicStateFileV1, AuthenticatedSpentNoteUpdateV1,
        DurableRelayerStateV1, DurableStateErrorV1, DurableWalletStateV1,
        LocalSpendAuthenticatorV1, SealedNoteAccessV1, SealedRecoveredNoteV1, SpentNoteMarkerV1,
    },
    durable_witness_state::DurableWalletWitnessStateV1,
    lane_forest_durable_v2::{
        decode_forest_finalized_append_event_v2, decode_lane_forest_durable_state_v2,
        encode_forest_finalized_append_event_v2, encode_lane_forest_durable_state_v2,
        ForestFinalizedAppendEventV2, ForestFinalizedAppendKindV2, LaneForestDurableErrorV2,
        LaneForestDurableStateV2,
    },
    lane_forest_v2::LaneIdV2,
    note_store_crypto::{
        open_note_opening_v1, NoteStoreCipherV1, POOL_V1_NOTE_STORE_ALGORITHM_XCHACHA20_POLY1305,
        POOL_V1_NOTE_STORE_FLAGS, POOL_V1_NOTE_STORE_HEADER_BYTES, POOL_V1_NOTE_STORE_MAGIC,
        POOL_V1_NOTE_STORE_NONCE_BYTES, POOL_V1_NOTE_STORE_SEALED_BYTES,
        POOL_V1_NOTE_STORE_VERSION,
    },
    recompute_note_commitment_v1,
    relayer_execution_journal::{
        validate_relayer_execution_archive_v1, DurableRelayerExecutionJournalV1,
        RelayerExecutionOutcomeV1,
    },
    scan_state::{
        DepositEventIdV1, DepositScanIdentityV1, FinalizedBlockV1, FinalizedChainPointV1,
    },
    wallet_monotonic_v2::{
        WalletMonotonicAdvanceV2, WalletMonotonicCommitmentV2, WalletMonotonicStoreErrorV2,
        WalletMonotonicStoreQualificationV2, WalletMonotonicStoreV2,
    },
    wallet_populated_migration_v2::PopulatedWalletMigrationV2,
};

pub const LANE_FOREST_WALLET_TXN_MAGIC_V2: [u8; 4] = *b"ASL2";
/// Frozen event-only ASL2 image version. The decoder remains available so
/// default-off research images can be opened and rewritten canonically.
pub const LANE_FOREST_WALLET_TXN_VERSION_V2: u8 = 2;
/// Current ASL2 image version. Version 3 adds a first-class empty-finalized-
/// block journal operation; it does not alias an empty block to a lane event.
pub const LANE_FOREST_WALLET_TXN_VERSION_V3: u8 = 3;
pub const LANE_FOREST_WALLET_TXN_HEADER_BYTES_V2: usize = 64;

const TXN_CHECKSUM_OFFSET_V2: usize = 24;
const TXN_CHECKSUM_DOMAIN_V2: &[u8] = b"aspis:pool-v1:lane-forest-wallet-authoritative:sha256:v2";
const ACTIVATION_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:lane-forest-wallet-empty-v1-activation:sha256:v2";
const CONTENT_DOMAIN_V2: &[u8] = b"aspis:pool-v1:lane-forest-wallet-content:sha256:v2";
const EMPTY_BLOCK_CONTENT_DOMAIN_V3: &[u8] =
    b"aspis:pool-v1:lane-forest-wallet-empty-block-content:sha256:v3";
const EMPTY_EVENT_SET_DOMAIN_V3: &[u8] =
    b"aspis:pool-v1:lane-forest-wallet-empty-event-set:sha256:v3";
const TRANSACTION_DOMAIN_V2: &[u8] = b"aspis:pool-v1:lane-forest-wallet-transaction:sha256:v2";
const STATE_DOMAIN_V2: &[u8] = b"aspis:pool-v1:lane-forest-wallet-state:sha256:v2";
const MAX_TXN_IMAGE_BYTES_V2: usize = 64 * 1024 * 1024;
const MAX_TXN_RECORDS_V2: usize = 100_000;
const MAX_LOGICAL_NOTES_V2: usize = 1_000_000;
const MAX_EVENT_NOTES_V2: usize = 2;
const MAX_EVENT_SPENDS_V2: usize = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LaneForestWalletTxnFaultPointV2 {
    BeforePreparedReplace,
    AfterPreparedReplace,
    BeforeStoresAppliedReplace,
    AfterStoresAppliedReplace,
    BeforeCommittedReplace,
    AfterCommittedReplace,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LaneForestWalletTxnAtomicBoundaryV2 {
    TemporaryWrite,
    TemporaryFileSync,
    TargetRename,
    ParentDirectorySync,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LaneForestWalletTxnWriteV2 {
    Activation,
    TentativeObservation,
    Prepared,
    StoresApplied,
    Committed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LaneForestWalletTxnAtomicFaultPointV2 {
    pub write: LaneForestWalletTxnWriteV2,
    pub boundary: LaneForestWalletTxnAtomicBoundaryV2,
}

pub trait LaneForestWalletTxnFaultInjectorV2 {
    fn interrupt_v2(&mut self, point: LaneForestWalletTxnFaultPointV2) -> bool;

    /// Called immediately after each real `AtomicStateFileV1` replacement
    /// sub-boundary. An error is ambiguous at the API boundary (the target may
    /// already contain the replacement), so the coordinator poisons itself.
    fn interrupt_atomic_v2(&mut self, _: LaneForestWalletTxnAtomicFaultPointV2) -> bool {
        false
    }
}

#[derive(Default)]
pub struct NoLaneForestWalletTxnFaultsV2;

impl LaneForestWalletTxnFaultInjectorV2 for NoLaneForestWalletTxnFaultsV2 {
    fn interrupt_v2(&mut self, _: LaneForestWalletTxnFaultPointV2) -> bool {
        false
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum LaneForestWalletTxnPhaseV2 {
    Prepared = 1,
    StoresApplied = 2,
    Committed = 3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LaneForestWalletTxnPrepareV2 {
    Prepared([u8; 32]),
    AlreadyPresent {
        transaction_id: [u8; 32],
        phase: LaneForestWalletTxnPhaseV2,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LaneForestWalletTxnRecoveryV2 {
    NoPending,
    StoresApplied([u8; 32]),
    Committed([u8; 32]),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LaneForestWalletTxnErrorV2 {
    Durable(DurableStateErrorV1),
    Lane(LaneForestDurableErrorV2),
    Io(io::ErrorKind),
    WrongLength,
    WrongMagic,
    WrongVersion,
    MigrationRequired,
    NonZeroReserved,
    ChecksumMismatch,
    NonCanonicalEncoding,
    CountOverflow,
    InvalidActivation,
    LegacyStateNotEmpty,
    ActivationMismatch,
    InvalidPhase,
    PendingTransaction,
    InvalidEvent,
    EventConflict,
    EventOutsideFinalizedOrder,
    FinalizedRollback,
    InvalidNoteCipher,
    NoteCipherMismatch,
    InvalidNote,
    DuplicateNonce,
    InvalidSpend,
    AlreadySpent,
    SpendNotAuthorized,
    InvalidCheckpoint,
    InvalidRelayerObservation,
    TransactionMismatch,
    StateMismatch,
    Poisoned,
    MonotonicRequired,
    MonotonicRollback,
    Monotonic(WalletMonotonicStoreErrorV2),
    InjectedFault(LaneForestWalletTxnFaultPointV2),
    InjectedAtomicFault(LaneForestWalletTxnAtomicFaultPointV2),
}

impl From<WalletMonotonicStoreErrorV2> for LaneForestWalletTxnErrorV2 {
    fn from(error: WalletMonotonicStoreErrorV2) -> Self {
        Self::Monotonic(error)
    }
}

impl From<DurableStateErrorV1> for LaneForestWalletTxnErrorV2 {
    fn from(error: DurableStateErrorV1) -> Self {
        Self::Durable(error)
    }
}

impl From<LaneForestDurableErrorV2> for LaneForestWalletTxnErrorV2 {
    fn from(error: LaneForestDurableErrorV2) -> Self {
        Self::Lane(error)
    }
}

impl From<io::Error> for LaneForestWalletTxnErrorV2 {
    fn from(error: io::Error) -> Self {
        Self::Io(error.kind())
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct EmptyV1LaneForestWalletActivationV2 {
    activation_id: [u8; 32],
    wallet_identity_sha256: [u8; 32],
    note_cipher_id: [u8; 32],
    anchor: FinalizedChainPointV1,
    initial_lane_state: LaneForestDurableStateV2,
    initial_notes: Vec<LaneForestWalletStoredNoteV2>,
    migration_genesis: Option<LaneForestWalletMigrationGenesisV2>,
}

impl core::fmt::Debug for EmptyV1LaneForestWalletActivationV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("EmptyV1LaneForestWalletActivationV2")
            .field("anchor", &self.anchor)
            .field("note_count", &self.initial_notes.len())
            .field("populated_migration", &self.migration_genesis.is_some())
            .field("private_state_and_digests", &"[REDACTED]")
            .finish()
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct LaneForestWalletMigrationGenesisV2 {
    migration_id: [u8; 32],
    source_manifest_sha256: [u8; 32],
    relayer_execution_archive: Vec<u8>,
}

impl core::fmt::Debug for LaneForestWalletMigrationGenesisV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("LaneForestWalletMigrationGenesisV2")
            .field("private_digests_and_relayer_archive", &"[REDACTED]")
            .finish()
    }
}

impl LaneForestWalletMigrationGenesisV2 {
    pub fn migration_id(&self) -> &[u8; 32] {
        &self.migration_id
    }

    pub fn source_manifest_sha256(&self) -> &[u8; 32] {
        &self.source_manifest_sha256
    }

    pub fn relayer_execution_archive(&self) -> &[u8] {
        &self.relayer_execution_archive
    }
}

/// Explicit operator policy for the topology change from the legacy single
/// pool/vault cursor to a pair-forest master. The shared asset fields are
/// checked mechanically; this capability must separately approve the distinct
/// legacy pool/vault and forest master/pool/token-program addresses.
pub trait LaneForestWalletActivationPolicyV2 {
    fn approves_topology_transition_v2(
        &self,
        legacy_pool: &[u8; 32],
        legacy_vault_token_account: &[u8; 32],
        forest_master: &[u8; 32],
        forest_identity_pool: &[u8; 32],
        forest_token_program: &[u8; 32],
    ) -> bool;
}

impl EmptyV1LaneForestWalletActivationV2 {
    pub fn from_empty_v1(
        wallet: &DurableWalletStateV1,
        witness: &DurableWalletWitnessStateV1,
        relayer_admission: &DurableRelayerStateV1,
        relayer: &DurableRelayerExecutionJournalV1,
        lane_state: &LaneForestDurableStateV2,
        activation_policy: &impl LaneForestWalletActivationPolicyV2,
    ) -> Result<Self, LaneForestWalletTxnErrorV2> {
        if wallet.scan_state().retained_block_count() != 0
            || wallet.scan_state().retained_event_count() != 0
            || wallet.scan_state().next_leaf_index() != 0
            || !wallet.notes().is_empty()
            || !wallet.active_prepared_plans().is_empty()
            || wallet.has_prepared_plan_history_v1()
            || witness.retained_block_count() != 0
            || witness.anchor_point() != wallet.scan_state().anchor()
            || witness.current_state().tree() != &IncrementalMerkleTreeV1::empty()
            || !witness.current_state().tracked().is_empty()
            || encode_digest_canonical(&witness.current_state().tree().root)
                != *wallet.scan_state().root()
            || !relayer_admission.entries().is_empty()
            || relayer_admission.rate_window() != (0, 0)
            || !relayer.records().is_empty()
            || lane_state.finalized_head_v2().is_some()
            || lane_state.checkpoint_count() != 0
            || lane_state.retained_event_count_v2() != 0
            || (0u8..8).any(|lane| {
                let lane_id = LaneIdV2::new(lane).expect("lane index is bounded by construction");
                lane_state.lane(lane_id).0.value.tree.next_leaf_index != 0
                    || !lane_state.tracked_outputs(lane_id).is_empty()
            })
        {
            return Err(LaneForestWalletTxnErrorV2::LegacyStateNotEmpty);
        }
        let scan_identity = wallet.scan_state().identity();
        let lane_identity = lane_state.master().value.identity;
        if *scan_identity.asset_mint() != lane_identity.asset_mint
            || *scan_identity.deployment_domain() != lane_identity.deployment_domain
            || scan_identity.asset_id() != lane_identity.asset_id.0
        {
            return Err(LaneForestWalletTxnErrorV2::InvalidActivation);
        }
        if !activation_policy.approves_topology_transition_v2(
            scan_identity.pool(),
            scan_identity.vault_token_account(),
            &lane_state.master().address,
            &lane_identity.pool,
            &lane_identity.token_program,
        ) {
            return Err(LaneForestWalletTxnErrorV2::InvalidActivation);
        }
        let note_cipher_id = *wallet.note_cipher_id();
        if note_cipher_id == [0u8; 32] {
            return Err(LaneForestWalletTxnErrorV2::InvalidNoteCipher);
        }
        let wallet_identity_sha256 = wallet_identity_sha256_v2(wallet.scan_state().identity());
        let anchor = wallet.scan_state().anchor();
        let lane_image = encode_lane_forest_durable_state_v2(lane_state)?;
        let activation_id =
            activation_id_v2(wallet_identity_sha256, note_cipher_id, anchor, &lane_image)?;
        Ok(Self {
            activation_id,
            wallet_identity_sha256,
            note_cipher_id,
            anchor,
            initial_lane_state: lane_state.clone(),
            initial_notes: Vec::new(),
            migration_genesis: None,
        })
    }

    /// Construct a populated, migration-bound ASL2 genesis only from the
    /// private-field snapshot returned by the locked cross-store validator.
    /// No legacy bytes are reinterpreted here.
    pub fn from_populated_migration_v2(
        migration: &PopulatedWalletMigrationV2,
    ) -> Result<Self, LaneForestWalletTxnErrorV2> {
        let mut initial_notes = Vec::with_capacity(migration.notes().len());
        for note in migration.notes() {
            validate_note_envelope_v2(&note.sealed_note)?;
            let nonce = note.sealed_note[8..POOL_V1_NOTE_STORE_HEADER_BYTES]
                .try_into()
                .map_err(|_| LaneForestWalletTxnErrorV2::InvalidNote)?;
            initial_notes.push(LaneForestWalletStoredNoteV2 {
                event_id: note.event_id,
                access: note.access,
                sealed_note: note.sealed_note.clone(),
                nonce,
                spent: note.spent,
            });
        }
        initial_notes.sort_by_key(|note| encode_event_id_v2(note.event_id));
        let migration_genesis = LaneForestWalletMigrationGenesisV2 {
            migration_id: *migration.migration_id(),
            source_manifest_sha256: *migration.source_manifest_sha256(),
            relayer_execution_archive: migration.relayer_execution_archive().to_vec(),
        };
        validate_relayer_execution_archive_v1(&migration_genesis.relayer_execution_archive)
            .map_err(|_| LaneForestWalletTxnErrorV2::InvalidRelayerObservation)?;
        let lane_image = encode_lane_forest_durable_state_v2(migration.lane_state())?;
        let activation_id = populated_activation_id_v3(
            *migration.wallet_identity_sha256(),
            *migration.note_cipher_id(),
            migration.finalized_head(),
            &lane_image,
            &initial_notes,
            &migration_genesis,
        )?;
        Ok(Self {
            activation_id,
            wallet_identity_sha256: *migration.wallet_identity_sha256(),
            note_cipher_id: *migration.note_cipher_id(),
            anchor: migration.finalized_head(),
            initial_lane_state: migration.lane_state().clone(),
            initial_notes,
            migration_genesis: Some(migration_genesis),
        })
    }

    pub fn activation_id(&self) -> &[u8; 32] {
        &self.activation_id
    }

    pub fn note_cipher_id(&self) -> &[u8; 32] {
        &self.note_cipher_id
    }

    pub fn anchor(&self) -> FinalizedChainPointV1 {
        self.anchor
    }

    pub fn wallet_identity_sha256(&self) -> &[u8; 32] {
        &self.wallet_identity_sha256
    }

    pub fn migration_genesis(&self) -> Option<&LaneForestWalletMigrationGenesisV2> {
        self.migration_genesis.as_ref()
    }

    pub fn requires_monotonic_protection_v2(&self) -> bool {
        self.migration_genesis.is_some()
    }
}

fn wallet_identity_sha256_v2(identity: &DepositScanIdentityV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"aspis:pool-v1:lane-forest-wallet-scan-identity:sha256:v2");
    hasher.update(identity.pool());
    hasher.update(identity.deployment_domain());
    hasher.update(identity.asset_mint());
    hasher.update(identity.vault_token_account());
    hasher.update(identity.asset_id().to_le_bytes());
    hasher.finalize().into()
}

fn activation_id_v2(
    wallet_identity_sha256: [u8; 32],
    note_cipher_id: [u8; 32],
    anchor: FinalizedChainPointV1,
    lane_image: &[u8],
) -> Result<[u8; 32], LaneForestWalletTxnErrorV2> {
    let lane_length =
        u64::try_from(lane_image.len()).map_err(|_| LaneForestWalletTxnErrorV2::CountOverflow)?;
    let mut hasher = Sha256::new();
    hasher.update(ACTIVATION_DOMAIN_V2);
    hasher.update(wallet_identity_sha256);
    hasher.update(note_cipher_id);
    hash_point_v2(&mut hasher, anchor);
    hasher.update(lane_length.to_le_bytes());
    hasher.update(Sha256::digest(lane_image));
    Ok(hasher.finalize().into())
}

fn populated_activation_id_v3(
    wallet_identity_sha256: [u8; 32],
    note_cipher_id: [u8; 32],
    finalized_head: FinalizedChainPointV1,
    lane_image: &[u8],
    notes: &[LaneForestWalletStoredNoteV2],
    migration: &LaneForestWalletMigrationGenesisV2,
) -> Result<[u8; 32], LaneForestWalletTxnErrorV2> {
    let lane_length =
        u64::try_from(lane_image.len()).map_err(|_| LaneForestWalletTxnErrorV2::CountOverflow)?;
    let archive_length = u64::try_from(migration.relayer_execution_archive.len())
        .map_err(|_| LaneForestWalletTxnErrorV2::CountOverflow)?;
    let mut hasher = Sha256::new();
    hasher.update(b"aspis:pool-v1:lane-forest-wallet-populated-activation:sha256:v3");
    hasher.update(wallet_identity_sha256);
    hasher.update(note_cipher_id);
    hash_point_v2(&mut hasher, finalized_head);
    hasher.update(lane_length.to_le_bytes());
    hasher.update(Sha256::digest(lane_image));
    hasher.update((notes.len() as u64).to_le_bytes());
    for note in notes {
        hasher.update(encode_event_id_v2(note.event_id));
        hasher.update([match note.access {
            SealedNoteAccessV1::ViewOnly => 1,
            SealedNoteAccessV1::Spendable => 2,
        }]);
        hasher.update(note.nonce);
        hasher.update(Sha256::digest(&note.sealed_note));
        match note.spent {
            None => hasher.update([0]),
            Some(spent) => {
                hasher.update([1]);
                hasher.update(encode_event_id_v2(spent.transition_output_id));
                hasher.update(spent.nullifier);
            }
        }
    }
    hasher.update(migration.migration_id);
    hasher.update(migration.source_manifest_sha256);
    hasher.update(archive_length.to_le_bytes());
    hasher.update(Sha256::digest(&migration.relayer_execution_archive));
    Ok(hasher.finalize().into())
}

fn hash_point_v2(hasher: &mut Sha256, point: FinalizedChainPointV1) {
    hasher.update(point.slot().to_le_bytes());
    hasher.update(point.block_hash());
}

fn encode_point_v2(point: FinalizedChainPointV1) -> [u8; 40] {
    let mut output = [0u8; 40];
    output[..8].copy_from_slice(&point.slot().to_le_bytes());
    output[8..].copy_from_slice(point.block_hash());
    output
}

fn decode_point_v2(bytes: &[u8]) -> Result<FinalizedChainPointV1, LaneForestWalletTxnErrorV2> {
    if bytes.len() != 40 {
        return Err(LaneForestWalletTxnErrorV2::InvalidEvent);
    }
    let mut slot = [0u8; 8];
    slot.copy_from_slice(&bytes[..8]);
    let mut hash = [0u8; 32];
    hash.copy_from_slice(&bytes[8..]);
    FinalizedChainPointV1::new(u64::from_le_bytes(slot), hash)
        .map_err(|_| LaneForestWalletTxnErrorV2::InvalidEvent)
}

fn encode_event_id_v2(event_id: DepositEventIdV1) -> [u8; 108] {
    let mut output = [0u8; 108];
    output[..40].copy_from_slice(&encode_point_v2(event_id.point()));
    output[40..104].copy_from_slice(event_id.transaction_signature());
    output[104..106].copy_from_slice(&event_id.instruction_index().to_le_bytes());
    output[106..108].copy_from_slice(&event_id.event_index().to_le_bytes());
    output
}

fn decode_event_id_v2(bytes: &[u8]) -> Result<DepositEventIdV1, LaneForestWalletTxnErrorV2> {
    if bytes.len() != 108 {
        return Err(LaneForestWalletTxnErrorV2::InvalidEvent);
    }
    let point = decode_point_v2(&bytes[..40])?;
    let mut signature = [0u8; 64];
    signature.copy_from_slice(&bytes[40..104]);
    let mut instruction = [0u8; 2];
    instruction.copy_from_slice(&bytes[104..106]);
    let mut event = [0u8; 2];
    event.copy_from_slice(&bytes[106..108]);
    DepositEventIdV1::new(
        point,
        signature,
        u16::from_le_bytes(instruction),
        u16::from_le_bytes(event),
    )
    .map_err(|_| LaneForestWalletTxnErrorV2::InvalidEvent)
}

fn canonical_digest_v2(bytes: [u8; 32]) -> Result<[u8; 32], LaneForestWalletTxnErrorV2> {
    let digest =
        decode_digest_canonical(&bytes).map_err(|_| LaneForestWalletTxnErrorV2::InvalidSpend)?;
    Ok(encode_digest_canonical(&digest))
}

#[derive(Clone, PartialEq, Eq)]
pub struct LaneForestWalletNoteBindingV2 {
    event_id: DepositEventIdV1,
    access: SealedNoteAccessV1,
    sealed_note: Vec<u8>,
    nonce: [u8; POOL_V1_NOTE_STORE_NONCE_BYTES],
    sealed_sha256: [u8; 32],
}

impl core::fmt::Debug for LaneForestWalletNoteBindingV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("LaneForestWalletNoteBindingV2")
            .field("event_id", &self.event_id)
            .field("access", &self.access)
            .field("sealed_note", &"[REDACTED]")
            .finish()
    }
}

impl LaneForestWalletNoteBindingV2 {
    pub fn from_sealed_recovered_note_v2(
        note: &SealedRecoveredNoteV1,
    ) -> Result<Self, LaneForestWalletTxnErrorV2> {
        validate_note_envelope_v2(&note.sealed_note)?;
        let mut nonce = [0u8; POOL_V1_NOTE_STORE_NONCE_BYTES];
        nonce.copy_from_slice(&note.sealed_note[8..POOL_V1_NOTE_STORE_HEADER_BYTES]);
        Ok(Self {
            event_id: note.event_id,
            access: note.access,
            sealed_sha256: Sha256::digest(&note.sealed_note).into(),
            sealed_note: note.sealed_note.clone(),
            nonce,
        })
    }

    pub fn event_id(&self) -> DepositEventIdV1 {
        self.event_id
    }

    pub fn access(&self) -> SealedNoteAccessV1 {
        self.access
    }

    pub fn sealed_note(&self) -> &[u8] {
        &self.sealed_note
    }
}

fn validate_note_envelope_v2(bytes: &[u8]) -> Result<(), LaneForestWalletTxnErrorV2> {
    if bytes.len() != POOL_V1_NOTE_STORE_SEALED_BYTES
        || bytes[..4] != POOL_V1_NOTE_STORE_MAGIC
        || bytes[4] != POOL_V1_NOTE_STORE_VERSION
        || bytes[5] != POOL_V1_NOTE_STORE_FLAGS
        || bytes[6] != POOL_V1_NOTE_STORE_ALGORITHM_XCHACHA20_POLY1305
        || bytes[7] != 0
        || bytes[8..POOL_V1_NOTE_STORE_HEADER_BYTES]
            .iter()
            .all(|byte| *byte == 0)
    {
        return Err(LaneForestWalletTxnErrorV2::InvalidNote);
    }
    Ok(())
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct LaneForestWalletSpendBindingV2 {
    input_event_id: DepositEventIdV1,
    transition_output_id: DepositEventIdV1,
    nullifier: [u8; 32],
}

impl core::fmt::Debug for LaneForestWalletSpendBindingV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("LaneForestWalletSpendBindingV2")
            .field("input_event_id", &self.input_event_id)
            .field("transition_output_id", &self.transition_output_id)
            .field("nullifier", &"[REDACTED]")
            .finish()
    }
}

impl LaneForestWalletSpendBindingV2 {
    pub fn from_authenticated_update_v2(
        update: AuthenticatedSpentNoteUpdateV1,
    ) -> Result<Self, LaneForestWalletTxnErrorV2> {
        Ok(Self {
            input_event_id: update.input_event_id,
            transition_output_id: update.transition_output_id,
            nullifier: canonical_digest_v2(update.nullifier)?,
        })
    }

    pub fn input_event_id(&self) -> DepositEventIdV1 {
        self.input_event_id
    }

    pub fn transition_output_id(&self) -> DepositEventIdV1 {
        self.transition_output_id
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct LaneForestWalletCheckpointBindingV2 {
    point: FinalizedChainPointV1,
    next_master_address: [u8; 32],
    next_master_image: Vec<u8>,
    lane_accounts: Vec<([u8; 32], Vec<u8>)>,
    checkpoint_address: [u8; 32],
    checkpoint_image: Vec<u8>,
}

impl core::fmt::Debug for LaneForestWalletCheckpointBindingV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("LaneForestWalletCheckpointBindingV2")
            .field("point", &self.point)
            .field("lane_account_count", &self.lane_accounts.len())
            .field("authenticated_images", &"[REDACTED]")
            .finish()
    }
}

impl LaneForestWalletCheckpointBindingV2 {
    pub fn new_v2(
        point: FinalizedChainPointV1,
        next_master_address: [u8; 32],
        next_master_image: Vec<u8>,
        lane_accounts: Vec<([u8; 32], Vec<u8>)>,
        checkpoint_address: [u8; 32],
        checkpoint_image: Vec<u8>,
    ) -> Result<Self, LaneForestWalletTxnErrorV2> {
        if next_master_address == [0u8; 32]
            || checkpoint_address == [0u8; 32]
            || next_master_image.is_empty()
            || checkpoint_image.is_empty()
            || lane_accounts.is_empty()
            || lane_accounts
                .iter()
                .any(|(address, image)| *address == [0u8; 32] || image.is_empty())
        {
            return Err(LaneForestWalletTxnErrorV2::InvalidCheckpoint);
        }
        Ok(Self {
            point,
            next_master_address,
            next_master_image,
            lane_accounts,
            checkpoint_address,
            checkpoint_image,
        })
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct LaneForestWalletRelayerObservationV2 {
    request_id: [u8; 32],
    transaction_signature: [u8; 64],
    point: FinalizedChainPointV1,
    fee_lamports: u64,
    compute_units_consumed: u64,
    execution_result_sha256: [u8; 32],
    poststate_sha256: [u8; 32],
    provider_set_digest: [u8; 32],
}

impl core::fmt::Debug for LaneForestWalletRelayerObservationV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("LaneForestWalletRelayerObservationV2")
            .field("point", &self.point)
            .field("finalized_evidence", &"[REDACTED]")
            .finish()
    }
}

impl LaneForestWalletRelayerObservationV2 {
    /// The only public constructor accepts the journal's finalized-success
    /// capability. Confirmed, pending, and terminal-failure observations cannot
    /// be promoted into this type.
    pub fn from_finalized_journal_v2(
        journal: &DurableRelayerExecutionJournalV1,
        request_id: [u8; 32],
    ) -> Result<Self, LaneForestWalletTxnErrorV2> {
        let record = journal
            .record_v1(request_id)
            .ok_or(LaneForestWalletTxnErrorV2::InvalidRelayerObservation)?;
        let signed = record
            .signed
            .as_ref()
            .ok_or(LaneForestWalletTxnErrorV2::InvalidRelayerObservation)?;
        if record.request_id == [0u8; 32]
            || signed.transaction_signature == [0u8; 64]
            || signed.signed_wire.is_empty()
        {
            return Err(LaneForestWalletTxnErrorV2::InvalidRelayerObservation);
        }
        let evidence = match record.outcome {
            Some(RelayerExecutionOutcomeV1::Finalized(evidence)) => evidence,
            _ => return Err(LaneForestWalletTxnErrorV2::InvalidRelayerObservation),
        };
        let observation = Self {
            request_id: record.request_id,
            transaction_signature: signed.transaction_signature,
            point: evidence.point(),
            fee_lamports: evidence.fee_lamports(),
            compute_units_consumed: evidence.compute_units_consumed(),
            execution_result_sha256: *evidence.execution_result_sha256(),
            poststate_sha256: *evidence.poststate_sha256(),
            provider_set_digest: *evidence.provider_set_digest(),
        };
        observation.validate_v2()?;
        Ok(observation)
    }

    fn validate_v2(&self) -> Result<(), LaneForestWalletTxnErrorV2> {
        if self.request_id == [0u8; 32]
            || self.transaction_signature == [0u8; 64]
            || self.execution_result_sha256 == [0u8; 32]
            || self.poststate_sha256 == [0u8; 32]
            || self.provider_set_digest == [0u8; 32]
        {
            return Err(LaneForestWalletTxnErrorV2::InvalidRelayerObservation);
        }
        Ok(())
    }

    pub fn request_id(&self) -> &[u8; 32] {
        &self.request_id
    }

    pub fn transaction_signature(&self) -> &[u8; 64] {
        &self.transaction_signature
    }

    pub fn point(&self) -> FinalizedChainPointV1 {
        self.point
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct LaneForestWalletTxnIntentV2 {
    finalized_parent: FinalizedChainPointV1,
    event: ForestFinalizedAppendEventV2,
    event_wire: Vec<u8>,
    note_cipher_id: [u8; 32],
    notes: Vec<LaneForestWalletNoteBindingV2>,
    spends: Vec<LaneForestWalletSpendBindingV2>,
    checkpoint: Option<LaneForestWalletCheckpointBindingV2>,
    relayer: Option<LaneForestWalletRelayerObservationV2>,
}

impl core::fmt::Debug for LaneForestWalletTxnIntentV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("LaneForestWalletTxnIntentV2")
            .field("point", &self.event.point())
            .field("note_count", &self.notes.len())
            .field("spend_count", &self.spends.len())
            .field("has_checkpoint", &self.checkpoint.is_some())
            .field("has_finalized_relayer_observation", &self.relayer.is_some())
            .field("private_metadata", &"[REDACTED]")
            .finish()
    }
}

impl LaneForestWalletTxnIntentV2 {
    pub fn new_v2(
        finalized_block: FinalizedBlockV1,
        event: ForestFinalizedAppendEventV2,
        note_cipher_id: [u8; 32],
        mut notes: Vec<LaneForestWalletNoteBindingV2>,
        mut spends: Vec<LaneForestWalletSpendBindingV2>,
        checkpoint: Option<LaneForestWalletCheckpointBindingV2>,
        relayer: Option<LaneForestWalletRelayerObservationV2>,
    ) -> Result<Self, LaneForestWalletTxnErrorV2> {
        if finalized_block.point() != event.point() {
            return Err(LaneForestWalletTxnErrorV2::InvalidEvent);
        }
        if note_cipher_id == [0u8; 32] {
            return Err(LaneForestWalletTxnErrorV2::InvalidNoteCipher);
        }
        if notes.len() > MAX_EVENT_NOTES_V2 || spends.len() > MAX_EVENT_SPENDS_V2 {
            return Err(LaneForestWalletTxnErrorV2::CountOverflow);
        }
        let event_wire = encode_forest_finalized_append_event_v2(&event)?;
        let event = decode_forest_finalized_append_event_v2(&event_wire)?;
        notes.sort_by_key(|note| encode_event_id_v2(note.event_id));
        spends.sort_by_key(|spend| encode_event_id_v2(spend.input_event_id));
        let output_ids = output_event_ids_v2(&event);
        let mut note_ids = HashSet::new();
        for note in &notes {
            validate_note_envelope_v2(&note.sealed_note)?;
            let sealed_sha256: [u8; 32] = Sha256::digest(&note.sealed_note).into();
            if sealed_sha256 != note.sealed_sha256
                || note.sealed_note[8..POOL_V1_NOTE_STORE_HEADER_BYTES] != note.nonce
                || !output_ids.contains(&note.event_id)
                || !note_ids.insert(note.event_id)
            {
                return Err(LaneForestWalletTxnErrorV2::InvalidNote);
            }
        }
        let mut spend_ids = HashSet::new();
        for spend in &spends {
            let (transition_output_id, nullifier) =
                event_spend_v2(&event).ok_or(LaneForestWalletTxnErrorV2::InvalidSpend)?;
            if spend.transition_output_id != transition_output_id
                || spend.nullifier != nullifier
                || output_ids.contains(&spend.input_event_id)
                || !spend_ids.insert(spend.input_event_id)
            {
                return Err(LaneForestWalletTxnErrorV2::InvalidSpend);
            }
        }
        if checkpoint
            .as_ref()
            .is_some_and(|checkpoint| checkpoint.point != event.point())
        {
            return Err(LaneForestWalletTxnErrorV2::InvalidCheckpoint);
        }
        if let Some(relayer) = &relayer {
            relayer.validate_v2()?;
            if relayer.point != event.point()
                || relayer.transaction_signature
                    != *primary_event_id_v2(&event).transaction_signature()
            {
                return Err(LaneForestWalletTxnErrorV2::InvalidRelayerObservation);
            }
        }
        Ok(Self {
            finalized_parent: finalized_block.parent(),
            event,
            event_wire,
            note_cipher_id,
            notes,
            spends,
            checkpoint,
            relayer,
        })
    }

    pub fn event(&self) -> &ForestFinalizedAppendEventV2 {
        &self.event
    }

    pub fn finalized_parent(&self) -> FinalizedChainPointV1 {
        self.finalized_parent
    }

    pub fn note_cipher_id(&self) -> &[u8; 32] {
        &self.note_cipher_id
    }

    pub fn notes(&self) -> &[LaneForestWalletNoteBindingV2] {
        &self.notes
    }

    pub fn spends(&self) -> &[LaneForestWalletSpendBindingV2] {
        &self.spends
    }

    pub fn finalized_relayer_observation(&self) -> Option<&LaneForestWalletRelayerObservationV2> {
        self.relayer.as_ref()
    }

    pub fn content_digest_v2(&self) -> Result<[u8; 32], LaneForestWalletTxnErrorV2> {
        content_digest_v2(self)
    }
}

/// Authenticated evidence that one externally-finalized block contains no
/// relevant pair-forest event. The evidence digests are deliberately public
/// metadata, not cryptographic proof material: production callers must obtain
/// them from the startup-pinned finalized provider/account-snapshot path.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct LaneForestWalletEmptyFinalizedBlockV2 {
    block: FinalizedBlockV1,
    empty_event_set_sha256: [u8; 32],
    account_snapshot_sha256: [u8; 32],
    startup_receipt_sha256: [u8; 32],
    provider_set_sha256: [u8; 32],
}

impl core::fmt::Debug for LaneForestWalletEmptyFinalizedBlockV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("LaneForestWalletEmptyFinalizedBlockV2")
            .field("point", &self.block.point())
            .field("parent", &self.block.parent())
            .field("authenticated_evidence", &"[REDACTED]")
            .finish()
    }
}

impl LaneForestWalletEmptyFinalizedBlockV2 {
    pub fn new_v2(
        block: FinalizedBlockV1,
        account_snapshot_sha256: [u8; 32],
        startup_receipt_sha256: [u8; 32],
        provider_set_sha256: [u8; 32],
    ) -> Result<Self, LaneForestWalletTxnErrorV2> {
        if account_snapshot_sha256 == [0u8; 32]
            || startup_receipt_sha256 == [0u8; 32]
            || provider_set_sha256 == [0u8; 32]
        {
            return Err(LaneForestWalletTxnErrorV2::InvalidRelayerObservation);
        }
        Ok(Self {
            block,
            empty_event_set_sha256: canonical_empty_event_set_sha256_v3(),
            account_snapshot_sha256,
            startup_receipt_sha256,
            provider_set_sha256,
        })
    }

    pub fn block(&self) -> FinalizedBlockV1 {
        self.block
    }

    pub fn empty_event_set_sha256(&self) -> &[u8; 32] {
        &self.empty_event_set_sha256
    }

    pub fn account_snapshot_sha256(&self) -> &[u8; 32] {
        &self.account_snapshot_sha256
    }

    pub fn startup_receipt_sha256(&self) -> &[u8; 32] {
        &self.startup_receipt_sha256
    }

    pub fn provider_set_sha256(&self) -> &[u8; 32] {
        &self.provider_set_sha256
    }
}

fn canonical_empty_event_set_sha256_v3() -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(EMPTY_EVENT_SET_DOMAIN_V3);
    hasher.update(0u64.to_le_bytes());
    hasher.finalize().into()
}

// Boxing this public operation would be an avoidable API shape change. The
// durable bincode wire remains value-shaped and is size-bounded separately.
#[allow(clippy::large_enum_variant)]
#[derive(Clone, PartialEq, Eq)]
pub enum LaneForestWalletTxnOperationV2 {
    Event(LaneForestWalletTxnIntentV2),
    EmptyFinalizedBlock(LaneForestWalletEmptyFinalizedBlockV2),
}

impl core::fmt::Debug for LaneForestWalletTxnOperationV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Event(intent) => formatter.debug_tuple("Event").field(intent).finish(),
            Self::EmptyFinalizedBlock(empty) => formatter
                .debug_tuple("EmptyFinalizedBlock")
                .field(empty)
                .finish(),
        }
    }
}

impl LaneForestWalletTxnOperationV2 {
    fn point_v2(&self) -> FinalizedChainPointV1 {
        match self {
            Self::Event(intent) => intent.event.point(),
            Self::EmptyFinalizedBlock(empty) => empty.block.point(),
        }
    }
}

fn primary_event_id_v2(event: &ForestFinalizedAppendEventV2) -> DepositEventIdV1 {
    match event.kind {
        ForestFinalizedAppendKindV2::Deposit { event_id, .. }
        | ForestFinalizedAppendKindV2::Withdrawal { event_id, .. } => event_id,
        ForestFinalizedAppendKindV2::PrivateTransfer {
            recipient_event_id, ..
        } => recipient_event_id,
    }
}

fn output_event_ids_v2(event: &ForestFinalizedAppendEventV2) -> Vec<DepositEventIdV1> {
    match event.kind {
        ForestFinalizedAppendKindV2::Deposit { event_id, .. }
        | ForestFinalizedAppendKindV2::Withdrawal { event_id, .. } => vec![event_id],
        ForestFinalizedAppendKindV2::PrivateTransfer {
            recipient_event_id,
            change_event_id,
            ..
        } => vec![recipient_event_id, change_event_id],
    }
}

fn event_spend_v2(event: &ForestFinalizedAppendEventV2) -> Option<(DepositEventIdV1, [u8; 32])> {
    match event.kind {
        ForestFinalizedAppendKindV2::Deposit { .. } => None,
        ForestFinalizedAppendKindV2::PrivateTransfer {
            recipient_event_id,
            nullifier,
            ..
        }
        | ForestFinalizedAppendKindV2::Withdrawal {
            event_id: recipient_event_id,
            nullifier,
            ..
        } => Some((recipient_event_id, nullifier)),
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct LaneForestWalletStoredNoteV2 {
    event_id: DepositEventIdV1,
    access: SealedNoteAccessV1,
    sealed_note: Vec<u8>,
    nonce: [u8; POOL_V1_NOTE_STORE_NONCE_BYTES],
    spent: Option<SpentNoteMarkerV1>,
}

impl core::fmt::Debug for LaneForestWalletStoredNoteV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("LaneForestWalletStoredNoteV2")
            .field("event_id", &self.event_id)
            .field("access", &self.access)
            .field("sealed_note", &"[REDACTED]")
            .field("spent", &self.spent.is_some())
            .finish()
    }
}

impl LaneForestWalletStoredNoteV2 {
    pub fn event_id(&self) -> DepositEventIdV1 {
        self.event_id
    }

    pub fn access(&self) -> SealedNoteAccessV1 {
        self.access
    }

    pub fn sealed_note(&self) -> &[u8] {
        &self.sealed_note
    }

    pub fn is_spent(&self) -> bool {
        self.spent.is_some()
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct LaneForestWalletCommittedStateV2 {
    finalized_head: FinalizedChainPointV1,
    note_cipher_id: [u8; 32],
    notes: Vec<LaneForestWalletStoredNoteV2>,
    lane_state: LaneForestDurableStateV2,
}

impl core::fmt::Debug for LaneForestWalletCommittedStateV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("LaneForestWalletCommittedStateV2")
            .field("finalized_head", &self.finalized_head)
            .field("note_count", &self.notes.len())
            .field("lane_checkpoint_count", &self.lane_state.checkpoint_count())
            .field("private_metadata", &"[REDACTED]")
            .finish()
    }
}

impl LaneForestWalletCommittedStateV2 {
    pub fn finalized_head(&self) -> FinalizedChainPointV1 {
        self.finalized_head
    }

    pub fn note_cipher_id(&self) -> &[u8; 32] {
        &self.note_cipher_id
    }

    pub fn notes(&self) -> &[LaneForestWalletStoredNoteV2] {
        &self.notes
    }

    pub fn spendable_unspent_notes_v2(
        &self,
    ) -> impl Iterator<Item = &LaneForestWalletStoredNoteV2> {
        self.notes
            .iter()
            .filter(|note| note.access == SealedNoteAccessV1::Spendable && note.spent.is_none())
    }

    pub fn lane_state(&self) -> &LaneForestDurableStateV2 {
        &self.lane_state
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum LaneForestWalletTentativeCommitmentV2 {
    Unfinalized = 1,
    Confirmed = 2,
}

#[derive(Clone, PartialEq, Eq)]
pub struct LaneForestWalletTentativeObservationV2 {
    event: ForestFinalizedAppendEventV2,
    event_wire: Vec<u8>,
    event_content_sha256: [u8; 32],
    commitment: LaneForestWalletTentativeCommitmentV2,
    provider_set_digest: [u8; 32],
}

impl core::fmt::Debug for LaneForestWalletTentativeObservationV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("LaneForestWalletTentativeObservationV2")
            .field("point", &self.event.point())
            .field("commitment", &self.commitment)
            .field("provider_evidence", &"[REDACTED]")
            .finish()
    }
}

impl LaneForestWalletTentativeObservationV2 {
    fn new_v2(
        event: ForestFinalizedAppendEventV2,
        commitment: LaneForestWalletTentativeCommitmentV2,
        provider_set_digest: [u8; 32],
    ) -> Result<Self, LaneForestWalletTxnErrorV2> {
        if provider_set_digest == [0u8; 32] {
            return Err(LaneForestWalletTxnErrorV2::InvalidRelayerObservation);
        }
        let event_wire = encode_forest_finalized_append_event_v2(&event)?;
        let event = decode_forest_finalized_append_event_v2(&event_wire)?;
        let event_content_sha256 = Sha256::digest(&event_wire).into();
        Ok(Self {
            event,
            event_wire,
            event_content_sha256,
            commitment,
            provider_set_digest,
        })
    }

    pub fn event(&self) -> &ForestFinalizedAppendEventV2 {
        &self.event
    }

    pub fn commitment(&self) -> LaneForestWalletTentativeCommitmentV2 {
        self.commitment
    }

    pub fn provider_set_digest(&self) -> &[u8; 32] {
        &self.provider_set_digest
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct LaneForestWalletTxnRecordV2 {
    sequence: u64,
    parent_transaction_id: [u8; 32],
    transaction_id: [u8; 32],
    content_digest: [u8; 32],
    before_state_digest: [u8; 32],
    after_state_digest: [u8; 32],
    tentative_before_digest: [u8; 32],
    before_tentatives: Vec<LaneForestWalletTentativeObservationV2>,
    after_tentatives: Vec<LaneForestWalletTentativeObservationV2>,
    phase: LaneForestWalletTxnPhaseV2,
    operation: LaneForestWalletTxnOperationV2,
}

impl core::fmt::Debug for LaneForestWalletTxnRecordV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("LaneForestWalletTxnRecordV2")
            .field("sequence", &self.sequence)
            .field("phase", &self.phase)
            .field("point", &self.operation.point_v2())
            .field("private_metadata", &"[REDACTED]")
            .finish()
    }
}

impl LaneForestWalletTxnRecordV2 {
    pub fn sequence(&self) -> u64 {
        self.sequence
    }

    pub fn transaction_id(&self) -> &[u8; 32] {
        &self.transaction_id
    }

    pub fn phase(&self) -> LaneForestWalletTxnPhaseV2 {
        self.phase
    }

    pub fn operation(&self) -> &LaneForestWalletTxnOperationV2 {
        &self.operation
    }

    pub fn intent(&self) -> Option<&LaneForestWalletTxnIntentV2> {
        match &self.operation {
            LaneForestWalletTxnOperationV2::Event(intent) => Some(intent),
            LaneForestWalletTxnOperationV2::EmptyFinalizedBlock(_) => None,
        }
    }

    pub fn empty_finalized_block(&self) -> Option<&LaneForestWalletEmptyFinalizedBlockV2> {
        match &self.operation {
            LaneForestWalletTxnOperationV2::Event(_) => None,
            LaneForestWalletTxnOperationV2::EmptyFinalizedBlock(empty) => Some(empty),
        }
    }
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
struct ActivationWireV2 {
    activation_id: Vec<u8>,
    wallet_identity_sha256: Vec<u8>,
    note_cipher_id: Vec<u8>,
    anchor: Vec<u8>,
    initial_lane_state: Vec<u8>,
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
struct StoredNoteWireV3 {
    event_id: Vec<u8>,
    access: u8,
    sealed_note: Vec<u8>,
    nonce: Vec<u8>,
    spent_transition_output_id: Option<Vec<u8>>,
    spent_nullifier: Option<Vec<u8>>,
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
struct MigrationGenesisWireV3 {
    migration_id: Vec<u8>,
    source_manifest_sha256: Vec<u8>,
    relayer_execution_archive: Vec<u8>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LaneForestWalletMonotonicMetadataV3 {
    protection_id: [u8; 32],
    generation: u64,
    predecessor_commitment: [u8; 32],
}

type PreparedMonotonicImageV3 = (
    Vec<u8>,
    Option<LaneForestWalletMonotonicMetadataV3>,
    Option<(WalletMonotonicCommitmentV2, WalletMonotonicCommitmentV2)>,
);

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
struct MonotonicMetadataWireV3 {
    protection_id: Vec<u8>,
    generation: u64,
    predecessor_commitment: Vec<u8>,
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
struct ActivationWireV3 {
    base: ActivationWireV2,
    initial_notes: Vec<StoredNoteWireV3>,
    migration_genesis: Option<MigrationGenesisWireV3>,
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
struct NoteWireV2 {
    event_id: Vec<u8>,
    access: u8,
    sealed_note: Vec<u8>,
    nonce: Vec<u8>,
    sealed_sha256: Vec<u8>,
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
struct SpendWireV2 {
    input_event_id: Vec<u8>,
    transition_output_id: Vec<u8>,
    nullifier: Vec<u8>,
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
struct CheckpointWireV2 {
    point: Vec<u8>,
    next_master_address: Vec<u8>,
    next_master_image: Vec<u8>,
    lane_accounts: Vec<(Vec<u8>, Vec<u8>)>,
    checkpoint_address: Vec<u8>,
    checkpoint_image: Vec<u8>,
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
struct RelayerWireV2 {
    request_id: Vec<u8>,
    transaction_signature: Vec<u8>,
    point: Vec<u8>,
    fee_lamports: u64,
    compute_units_consumed: u64,
    execution_result_sha256: Vec<u8>,
    poststate_sha256: Vec<u8>,
    provider_set_digest: Vec<u8>,
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
struct TentativeWireV2 {
    event_wire: Vec<u8>,
    event_content_sha256: Vec<u8>,
    commitment: u8,
    provider_set_digest: Vec<u8>,
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
struct IntentWireV2 {
    finalized_parent: Vec<u8>,
    event_wire: Vec<u8>,
    note_cipher_id: Vec<u8>,
    notes: Vec<NoteWireV2>,
    spends: Vec<SpendWireV2>,
    checkpoint: Option<CheckpointWireV2>,
    relayer: Option<RelayerWireV2>,
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
struct RecordWireV2 {
    sequence: u64,
    parent_transaction_id: Vec<u8>,
    transaction_id: Vec<u8>,
    content_digest: Vec<u8>,
    before_state_digest: Vec<u8>,
    after_state_digest: Vec<u8>,
    tentative_before_digest: Vec<u8>,
    before_tentatives: Vec<TentativeWireV2>,
    after_tentatives: Vec<TentativeWireV2>,
    phase: u8,
    intent: IntentWireV2,
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
struct AuthoritativeImageWireV2 {
    activation: ActivationWireV2,
    records: Vec<RecordWireV2>,
    tentative_observations: Vec<TentativeWireV2>,
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
struct EmptyFinalizedBlockWireV3 {
    point: Vec<u8>,
    parent: Vec<u8>,
    empty_event_set_sha256: Vec<u8>,
    account_snapshot_sha256: Vec<u8>,
    startup_receipt_sha256: Vec<u8>,
    provider_set_sha256: Vec<u8>,
}

// Preserve the already-frozen local durable encoding rather than introducing
// indirection solely to equalize in-memory enum variants.
#[allow(clippy::large_enum_variant)]
#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
enum OperationWireV3 {
    Event(IntentWireV2),
    EmptyFinalizedBlock(EmptyFinalizedBlockWireV3),
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
struct RecordWireV3 {
    sequence: u64,
    parent_transaction_id: Vec<u8>,
    transaction_id: Vec<u8>,
    content_digest: Vec<u8>,
    before_state_digest: Vec<u8>,
    after_state_digest: Vec<u8>,
    tentative_before_digest: Vec<u8>,
    before_tentatives: Vec<TentativeWireV2>,
    after_tentatives: Vec<TentativeWireV2>,
    phase: u8,
    operation: OperationWireV3,
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
struct AuthoritativeImageWireV3 {
    activation: ActivationWireV3,
    records: Vec<RecordWireV3>,
    tentative_observations: Vec<TentativeWireV2>,
    monotonic: Option<MonotonicMetadataWireV3>,
}

fn activation_to_wire_v2(
    activation: &EmptyV1LaneForestWalletActivationV2,
) -> Result<ActivationWireV2, LaneForestWalletTxnErrorV2> {
    Ok(ActivationWireV2 {
        activation_id: activation.activation_id.to_vec(),
        wallet_identity_sha256: activation.wallet_identity_sha256.to_vec(),
        note_cipher_id: activation.note_cipher_id.to_vec(),
        anchor: encode_point_v2(activation.anchor).to_vec(),
        initial_lane_state: encode_lane_forest_durable_state_v2(&activation.initial_lane_state)?,
    })
}

fn activation_from_wire_v2(
    wire: ActivationWireV2,
) -> Result<EmptyV1LaneForestWalletActivationV2, LaneForestWalletTxnErrorV2> {
    let activation_id = exact_array_v2(&wire.activation_id)?;
    let wallet_identity_sha256 = exact_array_v2(&wire.wallet_identity_sha256)?;
    let note_cipher_id = exact_array_v2(&wire.note_cipher_id)?;
    if note_cipher_id == [0u8; 32] {
        return Err(LaneForestWalletTxnErrorV2::InvalidActivation);
    }
    let anchor = decode_point_v2(&wire.anchor)?;
    let initial_lane_state = decode_lane_forest_durable_state_v2(&wire.initial_lane_state)?;
    if initial_lane_state.finalized_head_v2().is_some()
        || initial_lane_state.checkpoint_count() != 0
        || initial_lane_state.retained_event_count_v2() != 0
        || (0u8..8).any(|lane| {
            let lane_id = LaneIdV2::new(lane).expect("lane index is bounded by construction");
            initial_lane_state
                .lane(lane_id)
                .0
                .value
                .tree
                .next_leaf_index
                != 0
                || !initial_lane_state.tracked_outputs(lane_id).is_empty()
        })
    {
        return Err(LaneForestWalletTxnErrorV2::InvalidActivation);
    }
    let expected = activation_id_v2(
        wallet_identity_sha256,
        note_cipher_id,
        anchor,
        &wire.initial_lane_state,
    )?;
    if !bool::from(activation_id.ct_eq(&expected)) {
        return Err(LaneForestWalletTxnErrorV2::InvalidActivation);
    }
    Ok(EmptyV1LaneForestWalletActivationV2 {
        activation_id,
        wallet_identity_sha256,
        note_cipher_id,
        anchor,
        initial_lane_state,
        initial_notes: Vec::new(),
        migration_genesis: None,
    })
}

fn stored_note_to_wire_v3(note: &LaneForestWalletStoredNoteV2) -> StoredNoteWireV3 {
    StoredNoteWireV3 {
        event_id: encode_event_id_v2(note.event_id).to_vec(),
        access: match note.access {
            SealedNoteAccessV1::ViewOnly => 1,
            SealedNoteAccessV1::Spendable => 2,
        },
        sealed_note: note.sealed_note.clone(),
        nonce: note.nonce.to_vec(),
        spent_transition_output_id: note
            .spent
            .map(|spent| encode_event_id_v2(spent.transition_output_id).to_vec()),
        spent_nullifier: note.spent.map(|spent| spent.nullifier.to_vec()),
    }
}

fn activation_to_wire_v3(
    activation: &EmptyV1LaneForestWalletActivationV2,
) -> Result<ActivationWireV3, LaneForestWalletTxnErrorV2> {
    Ok(ActivationWireV3 {
        base: activation_to_wire_v2(activation)?,
        initial_notes: activation
            .initial_notes
            .iter()
            .map(stored_note_to_wire_v3)
            .collect(),
        migration_genesis: activation.migration_genesis.as_ref().map(|migration| {
            MigrationGenesisWireV3 {
                migration_id: migration.migration_id.to_vec(),
                source_manifest_sha256: migration.source_manifest_sha256.to_vec(),
                relayer_execution_archive: migration.relayer_execution_archive.clone(),
            }
        }),
    })
}

fn activation_from_wire_v3(
    wire: ActivationWireV3,
) -> Result<EmptyV1LaneForestWalletActivationV2, LaneForestWalletTxnErrorV2> {
    if wire.migration_genesis.is_none() {
        if !wire.initial_notes.is_empty() {
            return Err(LaneForestWalletTxnErrorV2::InvalidActivation);
        }
        return activation_from_wire_v2(wire.base);
    }
    let activation_id = exact_array_v2(&wire.base.activation_id)?;
    let wallet_identity_sha256 = exact_array_v2(&wire.base.wallet_identity_sha256)?;
    let note_cipher_id = exact_array_v2(&wire.base.note_cipher_id)?;
    if note_cipher_id == [0u8; 32] {
        return Err(LaneForestWalletTxnErrorV2::InvalidActivation);
    }
    let anchor = decode_point_v2(&wire.base.anchor)?;
    let initial_lane_state = decode_lane_forest_durable_state_v2(&wire.base.initial_lane_state)?;
    if initial_lane_state.finalized_head_v2() != Some(anchor) {
        return Err(LaneForestWalletTxnErrorV2::InvalidActivation);
    }
    initial_lane_state.validate_migration_tracking_v2()?;
    let migration_wire = wire
        .migration_genesis
        .ok_or(LaneForestWalletTxnErrorV2::InvalidActivation)?;
    let migration_genesis = LaneForestWalletMigrationGenesisV2 {
        migration_id: exact_array_v2(&migration_wire.migration_id)?,
        source_manifest_sha256: exact_array_v2(&migration_wire.source_manifest_sha256)?,
        relayer_execution_archive: migration_wire.relayer_execution_archive,
    };
    if migration_genesis.migration_id == [0u8; 32]
        || migration_genesis.source_manifest_sha256 == [0u8; 32]
    {
        return Err(LaneForestWalletTxnErrorV2::InvalidActivation);
    }
    validate_relayer_execution_archive_v1(&migration_genesis.relayer_execution_archive)
        .map_err(|_| LaneForestWalletTxnErrorV2::InvalidRelayerObservation)?;
    let mut initial_notes = Vec::with_capacity(wire.initial_notes.len());
    let mut previous = None;
    let mut nonces = HashSet::new();
    let mut nullifiers = HashSet::new();
    for note in wire.initial_notes {
        let event_id = decode_event_id_v2(&note.event_id)?;
        let encoded_id = encode_event_id_v2(event_id);
        if previous.is_some_and(|previous| previous >= encoded_id) {
            return Err(LaneForestWalletTxnErrorV2::NonCanonicalEncoding);
        }
        previous = Some(encoded_id);
        validate_note_envelope_v2(&note.sealed_note)?;
        let nonce = exact_array_v2(&note.nonce)?;
        if note.sealed_note[8..POOL_V1_NOTE_STORE_HEADER_BYTES] != nonce || !nonces.insert(nonce) {
            return Err(LaneForestWalletTxnErrorV2::DuplicateNonce);
        }
        let access = match note.access {
            1 => SealedNoteAccessV1::ViewOnly,
            2 => SealedNoteAccessV1::Spendable,
            _ => return Err(LaneForestWalletTxnErrorV2::InvalidNote),
        };
        let spent = match (note.spent_transition_output_id, note.spent_nullifier) {
            (None, None) => None,
            (Some(transition), Some(nullifier)) if access == SealedNoteAccessV1::Spendable => {
                let nullifier = canonical_digest_v2(exact_array_v2(&nullifier)?)?;
                if !nullifiers.insert(nullifier) {
                    return Err(LaneForestWalletTxnErrorV2::InvalidSpend);
                }
                Some(SpentNoteMarkerV1 {
                    transition_output_id: decode_event_id_v2(&transition)?,
                    nullifier,
                })
            }
            _ => return Err(LaneForestWalletTxnErrorV2::InvalidSpend),
        };
        let tracked = initial_lane_state
            .migration_tracked_output_v2(event_id)
            .ok_or(LaneForestWalletTxnErrorV2::InvalidNote)?;
        let event = initial_lane_state
            .retained_event_v2(event_id)
            .ok_or(LaneForestWalletTxnErrorV2::InvalidNote)?;
        if output_commitment_v2(event, event_id) != Some(tracked.commitment) {
            return Err(LaneForestWalletTxnErrorV2::InvalidNote);
        }
        if let Some(spent) = spent {
            let transition = initial_lane_state
                .retained_event_v2(spent.transition_output_id)
                .ok_or(LaneForestWalletTxnErrorV2::InvalidSpend)?;
            let expected =
                event_spend_v2(transition).ok_or(LaneForestWalletTxnErrorV2::InvalidSpend)?;
            if expected != (spent.transition_output_id, spent.nullifier) {
                return Err(LaneForestWalletTxnErrorV2::InvalidSpend);
            }
        }
        initial_notes.push(LaneForestWalletStoredNoteV2 {
            event_id,
            access,
            sealed_note: note.sealed_note,
            nonce,
            spent,
        });
    }
    if initial_notes.len() > MAX_LOGICAL_NOTES_V2
        || initial_lane_state.migration_tracked_outputs_v2().count() != initial_notes.len()
    {
        return Err(LaneForestWalletTxnErrorV2::StateMismatch);
    }
    let expected = populated_activation_id_v3(
        wallet_identity_sha256,
        note_cipher_id,
        anchor,
        &wire.base.initial_lane_state,
        &initial_notes,
        &migration_genesis,
    )?;
    if !bool::from(activation_id.ct_eq(&expected)) {
        return Err(LaneForestWalletTxnErrorV2::InvalidActivation);
    }
    Ok(EmptyV1LaneForestWalletActivationV2 {
        activation_id,
        wallet_identity_sha256,
        note_cipher_id,
        anchor,
        initial_lane_state,
        initial_notes,
        migration_genesis: Some(migration_genesis),
    })
}

fn intent_to_wire_v2(intent: &LaneForestWalletTxnIntentV2) -> IntentWireV2 {
    IntentWireV2 {
        finalized_parent: encode_point_v2(intent.finalized_parent).to_vec(),
        event_wire: intent.event_wire.clone(),
        note_cipher_id: intent.note_cipher_id.to_vec(),
        notes: intent
            .notes
            .iter()
            .map(|note| NoteWireV2 {
                event_id: encode_event_id_v2(note.event_id).to_vec(),
                access: match note.access {
                    SealedNoteAccessV1::ViewOnly => 1,
                    SealedNoteAccessV1::Spendable => 2,
                },
                sealed_note: note.sealed_note.clone(),
                nonce: note.nonce.to_vec(),
                sealed_sha256: note.sealed_sha256.to_vec(),
            })
            .collect(),
        spends: intent
            .spends
            .iter()
            .map(|spend| SpendWireV2 {
                input_event_id: encode_event_id_v2(spend.input_event_id).to_vec(),
                transition_output_id: encode_event_id_v2(spend.transition_output_id).to_vec(),
                nullifier: spend.nullifier.to_vec(),
            })
            .collect(),
        checkpoint: intent
            .checkpoint
            .as_ref()
            .map(|checkpoint| CheckpointWireV2 {
                point: encode_point_v2(checkpoint.point).to_vec(),
                next_master_address: checkpoint.next_master_address.to_vec(),
                next_master_image: checkpoint.next_master_image.clone(),
                lane_accounts: checkpoint
                    .lane_accounts
                    .iter()
                    .map(|(address, image)| (address.to_vec(), image.clone()))
                    .collect(),
                checkpoint_address: checkpoint.checkpoint_address.to_vec(),
                checkpoint_image: checkpoint.checkpoint_image.clone(),
            }),
        relayer: intent.relayer.as_ref().map(|relayer| RelayerWireV2 {
            request_id: relayer.request_id.to_vec(),
            transaction_signature: relayer.transaction_signature.to_vec(),
            point: encode_point_v2(relayer.point).to_vec(),
            fee_lamports: relayer.fee_lamports,
            compute_units_consumed: relayer.compute_units_consumed,
            execution_result_sha256: relayer.execution_result_sha256.to_vec(),
            poststate_sha256: relayer.poststate_sha256.to_vec(),
            provider_set_digest: relayer.provider_set_digest.to_vec(),
        }),
    }
}

fn intent_from_wire_v2(
    wire: IntentWireV2,
) -> Result<LaneForestWalletTxnIntentV2, LaneForestWalletTxnErrorV2> {
    validate_intent_wire_order_v2(&wire)?;
    let original = wire.clone();
    let event = decode_forest_finalized_append_event_v2(&wire.event_wire)?;
    if encode_forest_finalized_append_event_v2(&event)? != wire.event_wire {
        return Err(LaneForestWalletTxnErrorV2::NonCanonicalEncoding);
    }
    let note_cipher_id = exact_array_v2(&wire.note_cipher_id)?;
    let finalized_parent = decode_point_v2(&wire.finalized_parent)?;
    let finalized_block = FinalizedBlockV1::new(event.point(), finalized_parent)
        .map_err(|_| LaneForestWalletTxnErrorV2::InvalidEvent)?;
    let mut notes = Vec::with_capacity(wire.notes.len());
    for note in wire.notes {
        let recovered = SealedRecoveredNoteV1 {
            event_id: decode_event_id_v2(&note.event_id)?,
            access: match note.access {
                1 => SealedNoteAccessV1::ViewOnly,
                2 => SealedNoteAccessV1::Spendable,
                _ => return Err(LaneForestWalletTxnErrorV2::InvalidNote),
            },
            sealed_note: note.sealed_note,
        };
        let binding = LaneForestWalletNoteBindingV2::from_sealed_recovered_note_v2(&recovered)?;
        if binding.nonce != exact_array_v2(&note.nonce)?
            || binding.sealed_sha256 != exact_array_v2(&note.sealed_sha256)?
        {
            return Err(LaneForestWalletTxnErrorV2::InvalidNote);
        }
        notes.push(binding);
    }
    let mut spends = Vec::with_capacity(wire.spends.len());
    for spend in wire.spends {
        spends.push(
            LaneForestWalletSpendBindingV2::from_authenticated_update_v2(
                AuthenticatedSpentNoteUpdateV1 {
                    input_event_id: decode_event_id_v2(&spend.input_event_id)?,
                    transition_output_id: decode_event_id_v2(&spend.transition_output_id)?,
                    nullifier: exact_array_v2(&spend.nullifier)?,
                },
            )?,
        );
    }
    let checkpoint = wire
        .checkpoint
        .map(|checkpoint| {
            LaneForestWalletCheckpointBindingV2::new_v2(
                decode_point_v2(&checkpoint.point)?,
                exact_array_v2(&checkpoint.next_master_address)?,
                checkpoint.next_master_image,
                checkpoint
                    .lane_accounts
                    .into_iter()
                    .map(|(address, image)| Ok((exact_array_v2(&address)?, image)))
                    .collect::<Result<Vec<_>, LaneForestWalletTxnErrorV2>>()?,
                exact_array_v2(&checkpoint.checkpoint_address)?,
                checkpoint.checkpoint_image,
            )
        })
        .transpose()?;
    let relayer = wire
        .relayer
        .map(|relayer| {
            let observation = LaneForestWalletRelayerObservationV2 {
                request_id: exact_array_v2(&relayer.request_id)?,
                transaction_signature: exact_array_v2(&relayer.transaction_signature)?,
                point: decode_point_v2(&relayer.point)?,
                fee_lamports: relayer.fee_lamports,
                compute_units_consumed: relayer.compute_units_consumed,
                execution_result_sha256: exact_array_v2(&relayer.execution_result_sha256)?,
                poststate_sha256: exact_array_v2(&relayer.poststate_sha256)?,
                provider_set_digest: exact_array_v2(&relayer.provider_set_digest)?,
            };
            observation.validate_v2()?;
            Ok::<LaneForestWalletRelayerObservationV2, LaneForestWalletTxnErrorV2>(observation)
        })
        .transpose()?;
    let intent = LaneForestWalletTxnIntentV2::new_v2(
        finalized_block,
        event,
        note_cipher_id,
        notes,
        spends,
        checkpoint,
        relayer,
    )?;
    if intent_to_wire_v2(&intent) != original {
        return Err(LaneForestWalletTxnErrorV2::NonCanonicalEncoding);
    }
    Ok(intent)
}

fn validate_intent_wire_order_v2(wire: &IntentWireV2) -> Result<(), LaneForestWalletTxnErrorV2> {
    if wire
        .notes
        .windows(2)
        .any(|pair| pair[0].event_id >= pair[1].event_id)
        || wire
            .spends
            .windows(2)
            .any(|pair| pair[0].input_event_id >= pair[1].input_event_id)
    {
        return Err(LaneForestWalletTxnErrorV2::NonCanonicalEncoding);
    }
    Ok(())
}

fn tentative_to_wire_v2(observation: &LaneForestWalletTentativeObservationV2) -> TentativeWireV2 {
    TentativeWireV2 {
        event_wire: observation.event_wire.clone(),
        event_content_sha256: observation.event_content_sha256.to_vec(),
        commitment: observation.commitment as u8,
        provider_set_digest: observation.provider_set_digest.to_vec(),
    }
}

fn tentative_from_wire_v2(
    wire: TentativeWireV2,
) -> Result<LaneForestWalletTentativeObservationV2, LaneForestWalletTxnErrorV2> {
    let event = decode_forest_finalized_append_event_v2(&wire.event_wire)?;
    if encode_forest_finalized_append_event_v2(&event)? != wire.event_wire {
        return Err(LaneForestWalletTxnErrorV2::NonCanonicalEncoding);
    }
    let commitment = match wire.commitment {
        1 => LaneForestWalletTentativeCommitmentV2::Unfinalized,
        2 => LaneForestWalletTentativeCommitmentV2::Confirmed,
        _ => return Err(LaneForestWalletTxnErrorV2::InvalidRelayerObservation),
    };
    let observation = LaneForestWalletTentativeObservationV2::new_v2(
        event,
        commitment,
        exact_array_v2(&wire.provider_set_digest)?,
    )?;
    if observation.event_content_sha256 != exact_array_v2(&wire.event_content_sha256)? {
        return Err(LaneForestWalletTxnErrorV2::InvalidRelayerObservation);
    }
    Ok(observation)
}

fn record_from_wire_v2(
    wire: RecordWireV2,
) -> Result<LaneForestWalletTxnRecordV2, LaneForestWalletTxnErrorV2> {
    Ok(LaneForestWalletTxnRecordV2 {
        sequence: wire.sequence,
        parent_transaction_id: exact_array_v2(&wire.parent_transaction_id)?,
        transaction_id: exact_array_v2(&wire.transaction_id)?,
        content_digest: exact_array_v2(&wire.content_digest)?,
        before_state_digest: exact_array_v2(&wire.before_state_digest)?,
        after_state_digest: exact_array_v2(&wire.after_state_digest)?,
        tentative_before_digest: exact_array_v2(&wire.tentative_before_digest)?,
        before_tentatives: wire
            .before_tentatives
            .into_iter()
            .map(tentative_from_wire_v2)
            .collect::<Result<Vec<_>, _>>()?,
        after_tentatives: wire
            .after_tentatives
            .into_iter()
            .map(tentative_from_wire_v2)
            .collect::<Result<Vec<_>, _>>()?,
        phase: match wire.phase {
            1 => LaneForestWalletTxnPhaseV2::Prepared,
            2 => LaneForestWalletTxnPhaseV2::StoresApplied,
            3 => LaneForestWalletTxnPhaseV2::Committed,
            _ => return Err(LaneForestWalletTxnErrorV2::InvalidPhase),
        },
        operation: LaneForestWalletTxnOperationV2::Event(intent_from_wire_v2(wire.intent)?),
    })
}

fn empty_block_to_wire_v3(
    empty: &LaneForestWalletEmptyFinalizedBlockV2,
) -> EmptyFinalizedBlockWireV3 {
    EmptyFinalizedBlockWireV3 {
        point: encode_point_v2(empty.block.point()).to_vec(),
        parent: encode_point_v2(empty.block.parent()).to_vec(),
        empty_event_set_sha256: empty.empty_event_set_sha256.to_vec(),
        account_snapshot_sha256: empty.account_snapshot_sha256.to_vec(),
        startup_receipt_sha256: empty.startup_receipt_sha256.to_vec(),
        provider_set_sha256: empty.provider_set_sha256.to_vec(),
    }
}

fn empty_block_from_wire_v3(
    wire: EmptyFinalizedBlockWireV3,
) -> Result<LaneForestWalletEmptyFinalizedBlockV2, LaneForestWalletTxnErrorV2> {
    let original = wire.clone();
    let block = FinalizedBlockV1::new(
        decode_point_v2(&wire.point)?,
        decode_point_v2(&wire.parent)?,
    )
    .map_err(|_| LaneForestWalletTxnErrorV2::InvalidEvent)?;
    let empty = LaneForestWalletEmptyFinalizedBlockV2::new_v2(
        block,
        exact_array_v2(&wire.account_snapshot_sha256)?,
        exact_array_v2(&wire.startup_receipt_sha256)?,
        exact_array_v2(&wire.provider_set_sha256)?,
    )?;
    if empty.empty_event_set_sha256 != exact_array_v2(&wire.empty_event_set_sha256)?
        || empty_block_to_wire_v3(&empty) != original
    {
        return Err(LaneForestWalletTxnErrorV2::NonCanonicalEncoding);
    }
    Ok(empty)
}

fn record_to_wire_v3(record: &LaneForestWalletTxnRecordV2) -> RecordWireV3 {
    RecordWireV3 {
        sequence: record.sequence,
        parent_transaction_id: record.parent_transaction_id.to_vec(),
        transaction_id: record.transaction_id.to_vec(),
        content_digest: record.content_digest.to_vec(),
        before_state_digest: record.before_state_digest.to_vec(),
        after_state_digest: record.after_state_digest.to_vec(),
        tentative_before_digest: record.tentative_before_digest.to_vec(),
        before_tentatives: record
            .before_tentatives
            .iter()
            .map(tentative_to_wire_v2)
            .collect(),
        after_tentatives: record
            .after_tentatives
            .iter()
            .map(tentative_to_wire_v2)
            .collect(),
        phase: record.phase as u8,
        operation: match &record.operation {
            LaneForestWalletTxnOperationV2::Event(intent) => {
                OperationWireV3::Event(intent_to_wire_v2(intent))
            }
            LaneForestWalletTxnOperationV2::EmptyFinalizedBlock(empty) => {
                OperationWireV3::EmptyFinalizedBlock(empty_block_to_wire_v3(empty))
            }
        },
    }
}

fn record_from_wire_v3(
    wire: RecordWireV3,
) -> Result<LaneForestWalletTxnRecordV2, LaneForestWalletTxnErrorV2> {
    Ok(LaneForestWalletTxnRecordV2 {
        sequence: wire.sequence,
        parent_transaction_id: exact_array_v2(&wire.parent_transaction_id)?,
        transaction_id: exact_array_v2(&wire.transaction_id)?,
        content_digest: exact_array_v2(&wire.content_digest)?,
        before_state_digest: exact_array_v2(&wire.before_state_digest)?,
        after_state_digest: exact_array_v2(&wire.after_state_digest)?,
        tentative_before_digest: exact_array_v2(&wire.tentative_before_digest)?,
        before_tentatives: wire
            .before_tentatives
            .into_iter()
            .map(tentative_from_wire_v2)
            .collect::<Result<Vec<_>, _>>()?,
        after_tentatives: wire
            .after_tentatives
            .into_iter()
            .map(tentative_from_wire_v2)
            .collect::<Result<Vec<_>, _>>()?,
        phase: match wire.phase {
            1 => LaneForestWalletTxnPhaseV2::Prepared,
            2 => LaneForestWalletTxnPhaseV2::StoresApplied,
            3 => LaneForestWalletTxnPhaseV2::Committed,
            _ => return Err(LaneForestWalletTxnErrorV2::InvalidPhase),
        },
        operation: match wire.operation {
            OperationWireV3::Event(intent) => {
                LaneForestWalletTxnOperationV2::Event(intent_from_wire_v2(intent)?)
            }
            OperationWireV3::EmptyFinalizedBlock(empty) => {
                LaneForestWalletTxnOperationV2::EmptyFinalizedBlock(empty_block_from_wire_v3(
                    empty,
                )?)
            }
        },
    })
}

fn exact_array_v2<const N: usize>(bytes: &[u8]) -> Result<[u8; N], LaneForestWalletTxnErrorV2> {
    bytes
        .try_into()
        .map_err(|_| LaneForestWalletTxnErrorV2::WrongLength)
}

fn canonical_serialize_v2<T: Serialize>(value: &T) -> Result<Vec<u8>, LaneForestWalletTxnErrorV2> {
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_little_endian()
        .serialize(value)
        .map_err(|_| LaneForestWalletTxnErrorV2::NonCanonicalEncoding)
}

fn content_digest_v2(
    intent: &LaneForestWalletTxnIntentV2,
) -> Result<[u8; 32], LaneForestWalletTxnErrorV2> {
    let wire = canonical_serialize_v2(&intent_to_wire_v2(intent))?;
    let mut hasher = Sha256::new();
    hasher.update(CONTENT_DOMAIN_V2);
    hasher.update((wire.len() as u64).to_le_bytes());
    hasher.update(wire);
    Ok(hasher.finalize().into())
}

fn empty_block_content_digest_v3(
    empty: &LaneForestWalletEmptyFinalizedBlockV2,
) -> Result<[u8; 32], LaneForestWalletTxnErrorV2> {
    let wire = canonical_serialize_v2(&empty_block_to_wire_v3(empty))?;
    let mut hasher = Sha256::new();
    hasher.update(EMPTY_BLOCK_CONTENT_DOMAIN_V3);
    hasher.update((wire.len() as u64).to_le_bytes());
    hasher.update(wire);
    Ok(hasher.finalize().into())
}

fn operation_content_digest_v2(
    operation: &LaneForestWalletTxnOperationV2,
) -> Result<[u8; 32], LaneForestWalletTxnErrorV2> {
    match operation {
        LaneForestWalletTxnOperationV2::Event(intent) => content_digest_v2(intent),
        LaneForestWalletTxnOperationV2::EmptyFinalizedBlock(empty) => {
            empty_block_content_digest_v3(empty)
        }
    }
}

fn output_commitment_v2(
    event: &ForestFinalizedAppendEventV2,
    event_id: DepositEventIdV1,
) -> Option<[u8; 32]> {
    match event.kind {
        ForestFinalizedAppendKindV2::Deposit {
            event_id: output_id,
            commitment,
            ..
        } if output_id == event_id => Some(commitment),
        ForestFinalizedAppendKindV2::PrivateTransfer {
            recipient_event_id,
            change_event_id,
            recipient_commitment,
            change_commitment,
            ..
        } if recipient_event_id == event_id => Some(recipient_commitment),
        ForestFinalizedAppendKindV2::PrivateTransfer {
            change_event_id,
            change_commitment,
            ..
        } if change_event_id == event_id => Some(change_commitment),
        ForestFinalizedAppendKindV2::Withdrawal {
            event_id: output_id,
            change_commitment,
            ..
        } if output_id == event_id => Some(change_commitment),
        _ => None,
    }
}

fn validate_secret_bindings_v2(
    state: &LaneForestWalletCommittedStateV2,
    intent: &LaneForestWalletTxnIntentV2,
    cipher: &NoteStoreCipherV1,
    authenticator: &dyn LocalSpendAuthenticatorV1,
) -> Result<(), LaneForestWalletTxnErrorV2> {
    if cipher.cipher_id() != intent.note_cipher_id || cipher.cipher_id() != state.note_cipher_id {
        return Err(LaneForestWalletTxnErrorV2::NoteCipherMismatch);
    }
    for note in &intent.notes {
        let opening = open_note_opening_v1(cipher, note.event_id, note.access, &note.sealed_note)
            .map_err(|_| LaneForestWalletTxnErrorV2::InvalidNote)?;
        let commitment = recompute_note_commitment_v1(&opening)
            .map_err(|_| LaneForestWalletTxnErrorV2::InvalidNote)?;
        if output_commitment_v2(&intent.event, note.event_id) != Some(commitment) {
            return Err(LaneForestWalletTxnErrorV2::InvalidNote);
        }
    }
    for spend in &intent.spends {
        let note = state
            .notes
            .iter()
            .find(|note| note.event_id == spend.input_event_id)
            .ok_or(LaneForestWalletTxnErrorV2::InvalidSpend)?;
        if note.access != SealedNoteAccessV1::Spendable
            || note.spent.is_some()
            || !authenticator.authenticates_spend_v1(
                note.event_id,
                &note.sealed_note,
                &spend.nullifier,
            )
        {
            return Err(if note.spent.is_some() {
                LaneForestWalletTxnErrorV2::AlreadySpent
            } else {
                LaneForestWalletTxnErrorV2::SpendNotAuthorized
            });
        }
    }
    Ok(())
}

fn verify_retained_note_openings_v2(
    state: &LaneForestWalletCommittedStateV2,
    records: &[LaneForestWalletTxnRecordV2],
    cipher: &NoteStoreCipherV1,
) -> Result<(), LaneForestWalletTxnErrorV2> {
    if cipher.cipher_id() != state.note_cipher_id {
        return Err(LaneForestWalletTxnErrorV2::NoteCipherMismatch);
    }
    for note in &state.notes {
        let retained_event = records
            .iter()
            .find_map(|record| {
                matches!(
                    &record.operation,
                    LaneForestWalletTxnOperationV2::Event(intent)
                        if output_event_ids_v2(&intent.event).contains(&note.event_id)
                )
                .then(|| match &record.operation {
                    LaneForestWalletTxnOperationV2::Event(intent) => &intent.event,
                    LaneForestWalletTxnOperationV2::EmptyFinalizedBlock(_) => unreachable!(),
                })
            })
            .or_else(|| state.lane_state.retained_event_v2(note.event_id))
            .ok_or(LaneForestWalletTxnErrorV2::StateMismatch)?;
        let opening = open_note_opening_v1(cipher, note.event_id, note.access, &note.sealed_note)
            .map_err(|_| LaneForestWalletTxnErrorV2::InvalidNote)?;
        let commitment = recompute_note_commitment_v1(&opening)
            .map_err(|_| LaneForestWalletTxnErrorV2::InvalidNote)?;
        if output_commitment_v2(retained_event, note.event_id) != Some(commitment)
            || !(0u8..8).any(|lane| {
                let lane = LaneIdV2::new(lane).expect("lane index is bounded by construction");
                state
                    .lane_state
                    .tracked_outputs(lane)
                    .iter()
                    .any(|tracked| tracked.output_event_id == note.event_id)
            })
        {
            return Err(LaneForestWalletTxnErrorV2::StateMismatch);
        }
    }
    Ok(())
}

fn apply_intent_structural_v2(
    state: &LaneForestWalletCommittedStateV2,
    intent: &LaneForestWalletTxnIntentV2,
) -> Result<LaneForestWalletCommittedStateV2, LaneForestWalletTxnErrorV2> {
    if state.note_cipher_id != intent.note_cipher_id {
        return Err(LaneForestWalletTxnErrorV2::NoteCipherMismatch);
    }
    let mut candidate = state.clone();
    let mut nonces = candidate
        .notes
        .iter()
        .map(|note| note.nonce)
        .collect::<HashSet<_>>();
    for note in &intent.notes {
        if !nonces.insert(note.nonce) {
            return Err(LaneForestWalletTxnErrorV2::DuplicateNonce);
        }
        if candidate
            .notes
            .iter()
            .any(|existing| existing.event_id == note.event_id)
        {
            return Err(LaneForestWalletTxnErrorV2::EventConflict);
        }
    }
    let mut nullifiers = candidate
        .notes
        .iter()
        .filter_map(|note| note.spent.map(|spent| spent.nullifier))
        .collect::<HashSet<_>>();
    for spend in &intent.spends {
        if !nullifiers.insert(spend.nullifier) {
            return Err(LaneForestWalletTxnErrorV2::InvalidSpend);
        }
        let note = candidate
            .notes
            .iter_mut()
            .find(|note| note.event_id == spend.input_event_id)
            .ok_or(LaneForestWalletTxnErrorV2::InvalidSpend)?;
        if note.access != SealedNoteAccessV1::Spendable {
            return Err(LaneForestWalletTxnErrorV2::InvalidSpend);
        }
        if note.spent.is_some() {
            return Err(LaneForestWalletTxnErrorV2::AlreadySpent);
        }
        note.spent = Some(SpentNoteMarkerV1 {
            transition_output_id: spend.transition_output_id,
            nullifier: spend.nullifier,
        });
    }
    let selected_output_ids = intent
        .notes
        .iter()
        .map(|note| note.event_id)
        .collect::<Vec<_>>();
    candidate
        .lane_state
        .ingest_finalized_append_preselected_v2(intent.event.clone(), &selected_output_ids)?;
    if let Some(checkpoint) = &intent.checkpoint {
        candidate.lane_state.ingest_finalized_checkpoint_v2(
            checkpoint.point,
            checkpoint.next_master_address,
            &checkpoint.next_master_image,
            &checkpoint.lane_accounts,
            checkpoint.checkpoint_address,
            &checkpoint.checkpoint_image,
        )?;
    }
    candidate
        .lane_state
        .set_finalized_head_v2(intent.event.point());
    for note in &intent.notes {
        candidate.notes.push(LaneForestWalletStoredNoteV2 {
            event_id: note.event_id,
            access: note.access,
            sealed_note: note.sealed_note.clone(),
            nonce: note.nonce,
            spent: None,
        });
    }
    if candidate.notes.len() > MAX_LOGICAL_NOTES_V2 {
        return Err(LaneForestWalletTxnErrorV2::CountOverflow);
    }
    candidate
        .notes
        .sort_by_key(|note| encode_event_id_v2(note.event_id));
    candidate.finalized_head = intent.event.point();
    Ok(candidate)
}

fn apply_empty_finalized_block_structural_v2(
    state: &LaneForestWalletCommittedStateV2,
    empty: &LaneForestWalletEmptyFinalizedBlockV2,
) -> LaneForestWalletCommittedStateV2 {
    let mut candidate = state.clone();
    candidate.finalized_head = empty.block.point();
    candidate
        .lane_state
        .set_finalized_head_v2(empty.block.point());
    candidate
}

fn apply_operation_structural_v2(
    state: &LaneForestWalletCommittedStateV2,
    operation: &LaneForestWalletTxnOperationV2,
) -> Result<LaneForestWalletCommittedStateV2, LaneForestWalletTxnErrorV2> {
    match operation {
        LaneForestWalletTxnOperationV2::Event(intent) => apply_intent_structural_v2(state, intent),
        LaneForestWalletTxnOperationV2::EmptyFinalizedBlock(empty) => {
            Ok(apply_empty_finalized_block_structural_v2(state, empty))
        }
    }
}

fn tentative_digest_v2(
    observations: &[LaneForestWalletTentativeObservationV2],
) -> Result<[u8; 32], LaneForestWalletTxnErrorV2> {
    let wire = observations
        .iter()
        .map(tentative_to_wire_v2)
        .collect::<Vec<_>>();
    let encoded = canonical_serialize_v2(&wire)?;
    let mut hasher = Sha256::new();
    hasher.update(b"aspis:pool-v1:lane-forest-wallet-tentative:sha256:v2");
    hasher.update((encoded.len() as u64).to_le_bytes());
    hasher.update(encoded);
    Ok(hasher.finalize().into())
}

fn logical_state_digest_v2(
    state: &LaneForestWalletCommittedStateV2,
    observations: &[LaneForestWalletTentativeObservationV2],
) -> Result<[u8; 32], LaneForestWalletTxnErrorV2> {
    let lane_image = encode_lane_forest_durable_state_v2(&state.lane_state)?;
    let mut hasher = Sha256::new();
    hasher.update(STATE_DOMAIN_V2);
    hash_point_v2(&mut hasher, state.finalized_head);
    hasher.update(state.note_cipher_id);
    hasher.update((lane_image.len() as u64).to_le_bytes());
    hasher.update(Sha256::digest(&lane_image));
    hasher.update((state.notes.len() as u64).to_le_bytes());
    for note in &state.notes {
        hasher.update(encode_event_id_v2(note.event_id));
        hasher.update([match note.access {
            SealedNoteAccessV1::ViewOnly => 1,
            SealedNoteAccessV1::Spendable => 2,
        }]);
        hasher.update(note.nonce);
        hasher.update((note.sealed_note.len() as u64).to_le_bytes());
        hasher.update(Sha256::digest(&note.sealed_note));
        match note.spent {
            None => hasher.update([0]),
            Some(spent) => {
                hasher.update([1]);
                hasher.update(encode_event_id_v2(spent.transition_output_id));
                hasher.update(spent.nullifier);
            }
        }
    }
    hasher.update(tentative_digest_v2(observations)?);
    Ok(hasher.finalize().into())
}

fn transaction_id_v2(
    sequence: u64,
    parent_transaction_id: [u8; 32],
    content_digest: [u8; 32],
    before_state_digest: [u8; 32],
    after_state_digest: [u8; 32],
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(TRANSACTION_DOMAIN_V2);
    hasher.update(sequence.to_le_bytes());
    hasher.update(parent_transaction_id);
    hasher.update(content_digest);
    hasher.update(before_state_digest);
    hasher.update(after_state_digest);
    hasher.finalize().into()
}

fn validate_finalized_order_v2(
    state: &LaneForestWalletCommittedStateV2,
    previous: Option<&LaneForestWalletTxnIntentV2>,
    next: &LaneForestWalletTxnIntentV2,
) -> Result<(), LaneForestWalletTxnErrorV2> {
    let point = next.event.point();
    let head = state.finalized_head;
    if point.slot() < head.slot()
        || (point.slot() == head.slot() && point.block_hash() != head.block_hash())
    {
        return Err(LaneForestWalletTxnErrorV2::FinalizedRollback);
    }
    if point == head {
        let previous = previous.ok_or(LaneForestWalletTxnErrorV2::EventOutsideFinalizedOrder)?;
        if previous.event.point() != point
            || previous.finalized_parent != next.finalized_parent
            || encode_event_id_v2(primary_event_id_v2(&next.event))
                <= encode_event_id_v2(primary_event_id_v2(&previous.event))
        {
            return Err(LaneForestWalletTxnErrorV2::EventOutsideFinalizedOrder);
        }
    } else if next.finalized_parent != head {
        return Err(LaneForestWalletTxnErrorV2::FinalizedRollback);
    }
    Ok(())
}

fn validate_empty_finalized_order_v2(
    state: &LaneForestWalletCommittedStateV2,
    empty: &LaneForestWalletEmptyFinalizedBlockV2,
) -> Result<(), LaneForestWalletTxnErrorV2> {
    let point = empty.block.point();
    let head = state.finalized_head;
    if point.slot() <= head.slot() {
        return Err(LaneForestWalletTxnErrorV2::FinalizedRollback);
    }
    if empty.block.parent() != head {
        return Err(LaneForestWalletTxnErrorV2::FinalizedRollback);
    }
    Ok(())
}

fn remove_matching_tentative_v2(
    observations: &[LaneForestWalletTentativeObservationV2],
    event: &ForestFinalizedAppendEventV2,
) -> Result<Vec<LaneForestWalletTentativeObservationV2>, LaneForestWalletTxnErrorV2> {
    let ids = output_event_ids_v2(event);
    let canonical = encode_forest_finalized_append_event_v2(event)?;
    let mut result = Vec::with_capacity(observations.len());
    for observation in observations {
        let overlaps = output_event_ids_v2(&observation.event)
            .iter()
            .any(|event_id| ids.contains(event_id));
        if overlaps {
            if observation.event_wire != canonical {
                return Err(LaneForestWalletTxnErrorV2::EventConflict);
            }
        } else {
            result.push(observation.clone());
        }
    }
    Ok(result)
}

fn validate_tentative_ledger_v2(
    observations: &[LaneForestWalletTentativeObservationV2],
) -> Result<(), LaneForestWalletTxnErrorV2> {
    if observations.len() > MAX_TXN_RECORDS_V2 {
        return Err(LaneForestWalletTxnErrorV2::CountOverflow);
    }
    let mut previous: Option<[u8; 108]> = None;
    let mut ids = HashSet::new();
    for observation in observations {
        let canonical = encode_forest_finalized_append_event_v2(&observation.event)?;
        let event_content_sha256: [u8; 32] = Sha256::digest(&canonical).into();
        if canonical != observation.event_wire
            || event_content_sha256 != observation.event_content_sha256
            || observation.provider_set_digest == [0u8; 32]
        {
            return Err(LaneForestWalletTxnErrorV2::InvalidRelayerObservation);
        }
        let primary = encode_event_id_v2(primary_event_id_v2(&observation.event));
        if previous.is_some_and(|previous| previous >= primary) {
            return Err(LaneForestWalletTxnErrorV2::NonCanonicalEncoding);
        }
        previous = Some(primary);
        for event_id in output_event_ids_v2(&observation.event) {
            if !ids.insert(event_id) {
                return Err(LaneForestWalletTxnErrorV2::EventConflict);
            }
        }
    }
    Ok(())
}

fn sort_tentative_ledger_v2(observations: &mut [LaneForestWalletTentativeObservationV2]) {
    observations
        .sort_by_key(|observation| encode_event_id_v2(primary_event_id_v2(&observation.event)));
}

struct ReplayedAuthoritativeImageV2 {
    committed: LaneForestWalletCommittedStateV2,
    pending_candidate: Option<LaneForestWalletCommittedStateV2>,
}

fn initial_committed_state_v2(
    activation: &EmptyV1LaneForestWalletActivationV2,
) -> LaneForestWalletCommittedStateV2 {
    LaneForestWalletCommittedStateV2 {
        finalized_head: activation.anchor,
        note_cipher_id: activation.note_cipher_id,
        notes: activation.initial_notes.clone(),
        lane_state: activation.initial_lane_state.clone(),
    }
}

fn replay_authoritative_image_v2(
    activation: &EmptyV1LaneForestWalletActivationV2,
    records: &[LaneForestWalletTxnRecordV2],
    tentative_observations: &[LaneForestWalletTentativeObservationV2],
) -> Result<ReplayedAuthoritativeImageV2, LaneForestWalletTxnErrorV2> {
    if records.len() > MAX_TXN_RECORDS_V2 {
        return Err(LaneForestWalletTxnErrorV2::CountOverflow);
    }
    validate_tentative_ledger_v2(tentative_observations)?;
    let mut committed = initial_committed_state_v2(activation);
    let mut pending_candidate = None;
    let mut parent_transaction_id = [0u8; 32];
    let mut previous_intent: Option<&LaneForestWalletTxnIntentV2> = None;
    let mut all_event_ids = HashSet::new();
    let mut committed_event_ids = HashSet::new();
    for (index, record) in records.iter().enumerate() {
        if record.sequence != index as u64 + 1
            || record.parent_transaction_id != parent_transaction_id
            || record.content_digest != operation_content_digest_v2(&record.operation)?
        {
            return Err(LaneForestWalletTxnErrorV2::TransactionMismatch);
        }
        if let LaneForestWalletTxnOperationV2::Event(intent) = &record.operation {
            for event_id in output_event_ids_v2(&intent.event) {
                if !all_event_ids.insert(event_id) {
                    return Err(LaneForestWalletTxnErrorV2::EventConflict);
                }
            }
        }
        validate_tentative_ledger_v2(&record.before_tentatives)?;
        validate_tentative_ledger_v2(&record.after_tentatives)?;
        if tentative_digest_v2(&record.before_tentatives)? != record.tentative_before_digest {
            return Err(LaneForestWalletTxnErrorV2::StateMismatch);
        }
        match &record.operation {
            LaneForestWalletTxnOperationV2::Event(intent) => {
                if remove_matching_tentative_v2(&record.before_tentatives, &intent.event)?
                    != record.after_tentatives
                {
                    return Err(LaneForestWalletTxnErrorV2::StateMismatch);
                }
                validate_finalized_order_v2(&committed, previous_intent, intent)?;
            }
            LaneForestWalletTxnOperationV2::EmptyFinalizedBlock(empty) => {
                if record.before_tentatives != record.after_tentatives
                    || record
                        .before_tentatives
                        .iter()
                        .any(|observation| observation.event.point() == empty.block.point())
                {
                    return Err(LaneForestWalletTxnErrorV2::StateMismatch);
                }
                validate_empty_finalized_order_v2(&committed, empty)?;
            }
        }
        let before_state_digest = logical_state_digest_v2(&committed, &record.before_tentatives)?;
        let candidate = apply_operation_structural_v2(&committed, &record.operation)?;
        let after_state_digest = logical_state_digest_v2(&candidate, &record.after_tentatives)?;
        if record.before_state_digest != before_state_digest
            || record.after_state_digest != after_state_digest
            || record.transaction_id
                != transaction_id_v2(
                    record.sequence,
                    record.parent_transaction_id,
                    record.content_digest,
                    record.before_state_digest,
                    record.after_state_digest,
                )
        {
            return Err(LaneForestWalletTxnErrorV2::StateMismatch);
        }
        let is_last = index + 1 == records.len();
        match record.phase {
            LaneForestWalletTxnPhaseV2::Committed => {
                if pending_candidate.is_some() {
                    return Err(LaneForestWalletTxnErrorV2::InvalidPhase);
                }
                if let LaneForestWalletTxnOperationV2::Event(intent) = &record.operation {
                    committed_event_ids.extend(output_event_ids_v2(&intent.event));
                }
                committed = candidate;
            }
            LaneForestWalletTxnPhaseV2::Prepared | LaneForestWalletTxnPhaseV2::StoresApplied => {
                if !is_last
                    || pending_candidate.is_some()
                    || record.before_tentatives != tentative_observations
                {
                    return Err(LaneForestWalletTxnErrorV2::InvalidPhase);
                }
                pending_candidate = Some(candidate);
            }
        }
        parent_transaction_id = record.transaction_id;
        previous_intent = match &record.operation {
            LaneForestWalletTxnOperationV2::Event(intent) => Some(intent),
            LaneForestWalletTxnOperationV2::EmptyFinalizedBlock(_) => None,
        };
    }
    for observation in tentative_observations {
        if output_event_ids_v2(&observation.event)
            .iter()
            .any(|event_id| committed_event_ids.contains(event_id))
        {
            return Err(LaneForestWalletTxnErrorV2::FinalizedRollback);
        }
    }
    if records
        .iter()
        .any(|record| record.phase == LaneForestWalletTxnPhaseV2::Committed)
    {
        if committed.lane_state.finalized_head_v2() != Some(committed.finalized_head) {
            return Err(LaneForestWalletTxnErrorV2::StateMismatch);
        }
    } else if committed != initial_committed_state_v2(activation) {
        return Err(LaneForestWalletTxnErrorV2::StateMismatch);
    }
    if pending_candidate.as_ref().is_some_and(|candidate| {
        candidate.lane_state.finalized_head_v2() != Some(candidate.finalized_head)
    }) {
        return Err(LaneForestWalletTxnErrorV2::StateMismatch);
    }
    Ok(ReplayedAuthoritativeImageV2 {
        committed,
        pending_candidate,
    })
}

fn checksum_v2(bytes: &[u8]) -> Result<[u8; 32], LaneForestWalletTxnErrorV2> {
    if bytes.len() < LANE_FOREST_WALLET_TXN_HEADER_BYTES_V2 {
        return Err(LaneForestWalletTxnErrorV2::WrongLength);
    }
    let mut hasher = Sha256::new();
    hasher.update(TXN_CHECKSUM_DOMAIN_V2);
    hasher.update(&bytes[..TXN_CHECKSUM_OFFSET_V2]);
    hasher.update([0u8; 32]);
    hasher.update(&bytes[TXN_CHECKSUM_OFFSET_V2 + 32..]);
    Ok(hasher.finalize().into())
}

fn monotonic_to_wire_v3(metadata: LaneForestWalletMonotonicMetadataV3) -> MonotonicMetadataWireV3 {
    MonotonicMetadataWireV3 {
        protection_id: metadata.protection_id.to_vec(),
        generation: metadata.generation,
        predecessor_commitment: metadata.predecessor_commitment.to_vec(),
    }
}

fn monotonic_from_wire_v3(
    wire: MonotonicMetadataWireV3,
) -> Result<LaneForestWalletMonotonicMetadataV3, LaneForestWalletTxnErrorV2> {
    let metadata = LaneForestWalletMonotonicMetadataV3 {
        protection_id: exact_array_v2(&wire.protection_id)?,
        generation: wire.generation,
        predecessor_commitment: exact_array_v2(&wire.predecessor_commitment)?,
    };
    if metadata.protection_id == [0u8; 32]
        || (metadata.generation == 0 && metadata.predecessor_commitment != [0u8; 32])
        || (metadata.generation != 0 && metadata.predecessor_commitment == [0u8; 32])
    {
        return Err(LaneForestWalletTxnErrorV2::MonotonicRollback);
    }
    Ok(metadata)
}

fn authoritative_content_digest_v3(
    activation: &EmptyV1LaneForestWalletActivationV2,
    records: &[LaneForestWalletTxnRecordV2],
    tentative_observations: &[LaneForestWalletTentativeObservationV2],
) -> Result<[u8; 32], LaneForestWalletTxnErrorV2> {
    let wire = AuthoritativeImageWireV3 {
        activation: activation_to_wire_v3(activation)?,
        records: records.iter().map(record_to_wire_v3).collect(),
        tentative_observations: tentative_observations
            .iter()
            .map(tentative_to_wire_v2)
            .collect(),
        monotonic: None,
    };
    let bytes = canonical_serialize_v2(&wire)?;
    let mut hasher = Sha256::new();
    hasher.update(b"aspis:pool-v1:lane-forest-wallet-authoritative-content:sha256:v3");
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
    Ok(hasher.finalize().into())
}

fn monotonic_commitment_v3(
    metadata: LaneForestWalletMonotonicMetadataV3,
    finalized_point: FinalizedChainPointV1,
    state_digest: [u8; 32],
) -> Result<WalletMonotonicCommitmentV2, LaneForestWalletTxnErrorV2> {
    WalletMonotonicCommitmentV2::new_v2(
        metadata.generation,
        finalized_point,
        metadata.predecessor_commitment,
        state_digest,
    )
    .map_err(Into::into)
}

fn encode_authoritative_image_v2(
    activation: &EmptyV1LaneForestWalletActivationV2,
    records: &[LaneForestWalletTxnRecordV2],
    tentative_observations: &[LaneForestWalletTentativeObservationV2],
    monotonic: Option<LaneForestWalletMonotonicMetadataV3>,
) -> Result<Vec<u8>, LaneForestWalletTxnErrorV2> {
    replay_authoritative_image_v2(activation, records, tentative_observations)?;
    let wire = AuthoritativeImageWireV3 {
        activation: activation_to_wire_v3(activation)?,
        records: records.iter().map(record_to_wire_v3).collect(),
        tentative_observations: tentative_observations
            .iter()
            .map(tentative_to_wire_v2)
            .collect(),
        monotonic: monotonic.map(monotonic_to_wire_v3),
    };
    let payload = canonical_serialize_v2(&wire)?;
    let length = LANE_FOREST_WALLET_TXN_HEADER_BYTES_V2
        .checked_add(payload.len())
        .ok_or(LaneForestWalletTxnErrorV2::CountOverflow)?;
    if length > MAX_TXN_IMAGE_BYTES_V2 {
        return Err(LaneForestWalletTxnErrorV2::CountOverflow);
    }
    let mut output = vec![0u8; length];
    output[..4].copy_from_slice(&LANE_FOREST_WALLET_TXN_MAGIC_V2);
    output[4] = LANE_FOREST_WALLET_TXN_VERSION_V3;
    output[8..16].copy_from_slice(&(payload.len() as u64).to_le_bytes());
    output[16..24].copy_from_slice(&(records.len() as u64).to_le_bytes());
    output[LANE_FOREST_WALLET_TXN_HEADER_BYTES_V2..].copy_from_slice(&payload);
    let checksum = checksum_v2(&output)?;
    output[TXN_CHECKSUM_OFFSET_V2..TXN_CHECKSUM_OFFSET_V2 + 32].copy_from_slice(&checksum);
    Ok(output)
}

#[allow(clippy::type_complexity)]
fn decode_authoritative_image_v2(
    bytes: &[u8],
) -> Result<
    (
        EmptyV1LaneForestWalletActivationV2,
        Vec<LaneForestWalletTxnRecordV2>,
        Vec<LaneForestWalletTentativeObservationV2>,
        ReplayedAuthoritativeImageV2,
        Option<LaneForestWalletMonotonicMetadataV3>,
    ),
    LaneForestWalletTxnErrorV2,
> {
    if bytes.len() < LANE_FOREST_WALLET_TXN_HEADER_BYTES_V2 || bytes.len() > MAX_TXN_IMAGE_BYTES_V2
    {
        return Err(LaneForestWalletTxnErrorV2::WrongLength);
    }
    if bytes[..4] != LANE_FOREST_WALLET_TXN_MAGIC_V2 {
        let magic = &bytes[..4];
        return Err(
            if magic == b"ASDW" || magic == b"ASWJ" || magic == b"ASRJ" || magic == b"ASD8" {
                LaneForestWalletTxnErrorV2::MigrationRequired
            } else {
                LaneForestWalletTxnErrorV2::WrongMagic
            },
        );
    }
    if bytes[4] != LANE_FOREST_WALLET_TXN_VERSION_V2
        && bytes[4] != LANE_FOREST_WALLET_TXN_VERSION_V3
    {
        return Err(if bytes[4] < LANE_FOREST_WALLET_TXN_VERSION_V2 {
            LaneForestWalletTxnErrorV2::MigrationRequired
        } else {
            LaneForestWalletTxnErrorV2::WrongVersion
        });
    }
    if bytes[5..8] != [0u8; 3] || bytes[56..64] != [0u8; 8] {
        return Err(LaneForestWalletTxnErrorV2::NonZeroReserved);
    }
    let payload_length = usize::try_from(u64::from_le_bytes(
        bytes[8..16]
            .try_into()
            .map_err(|_| LaneForestWalletTxnErrorV2::WrongLength)?,
    ))
    .map_err(|_| LaneForestWalletTxnErrorV2::CountOverflow)?;
    let record_count = usize::try_from(u64::from_le_bytes(
        bytes[16..24]
            .try_into()
            .map_err(|_| LaneForestWalletTxnErrorV2::WrongLength)?,
    ))
    .map_err(|_| LaneForestWalletTxnErrorV2::CountOverflow)?;
    if payload_length != bytes.len() - LANE_FOREST_WALLET_TXN_HEADER_BYTES_V2
        || record_count > MAX_TXN_RECORDS_V2
    {
        return Err(LaneForestWalletTxnErrorV2::CountOverflow);
    }
    let encoded_checksum: [u8; 32] =
        exact_array_v2(&bytes[TXN_CHECKSUM_OFFSET_V2..TXN_CHECKSUM_OFFSET_V2 + 32])?;
    if !bool::from(encoded_checksum.ct_eq(&checksum_v2(bytes)?)) {
        return Err(LaneForestWalletTxnErrorV2::ChecksumMismatch);
    }
    let payload = &bytes[LANE_FOREST_WALLET_TXN_HEADER_BYTES_V2..];
    let (activation, records, tentative_observations, monotonic) =
        if bytes[4] == LANE_FOREST_WALLET_TXN_VERSION_V2 {
            let wire: AuthoritativeImageWireV2 = bincode::DefaultOptions::new()
                .with_fixint_encoding()
                .with_little_endian()
                .reject_trailing_bytes()
                .with_limit(MAX_TXN_IMAGE_BYTES_V2 as u64)
                .deserialize(payload)
                .map_err(|_| LaneForestWalletTxnErrorV2::NonCanonicalEncoding)?;
            if canonical_serialize_v2(&wire)? != payload || wire.records.len() != record_count {
                return Err(LaneForestWalletTxnErrorV2::NonCanonicalEncoding);
            }
            (
                activation_from_wire_v2(wire.activation)?,
                wire.records
                    .into_iter()
                    .map(record_from_wire_v2)
                    .collect::<Result<Vec<_>, _>>()?,
                wire.tentative_observations
                    .into_iter()
                    .map(tentative_from_wire_v2)
                    .collect::<Result<Vec<_>, _>>()?,
                None,
            )
        } else {
            let wire: AuthoritativeImageWireV3 = bincode::DefaultOptions::new()
                .with_fixint_encoding()
                .with_little_endian()
                .reject_trailing_bytes()
                .with_limit(MAX_TXN_IMAGE_BYTES_V2 as u64)
                .deserialize(payload)
                .map_err(|_| LaneForestWalletTxnErrorV2::NonCanonicalEncoding)?;
            if canonical_serialize_v2(&wire)? != payload || wire.records.len() != record_count {
                return Err(LaneForestWalletTxnErrorV2::NonCanonicalEncoding);
            }
            let monotonic = wire.monotonic.map(monotonic_from_wire_v3).transpose()?;
            (
                activation_from_wire_v3(wire.activation)?,
                wire.records
                    .into_iter()
                    .map(record_from_wire_v3)
                    .collect::<Result<Vec<_>, _>>()?,
                wire.tentative_observations
                    .into_iter()
                    .map(tentative_from_wire_v2)
                    .collect::<Result<Vec<_>, _>>()?,
                monotonic,
            )
        };
    let replayed = replay_authoritative_image_v2(&activation, &records, &tentative_observations)?;
    if activation.requires_monotonic_protection_v2() != monotonic.is_some() {
        return Err(LaneForestWalletTxnErrorV2::MonotonicRequired);
    }
    Ok((
        activation,
        records,
        tentative_observations,
        replayed,
        monotonic,
    ))
}

/// Build the exact initial protected ASL2 bytes embedded in the migration
/// journal's Prepared phase. The external monotonic store is intentionally not
/// advanced until these bytes have been durably installed.
pub fn prepare_protected_initial_image_v2(
    activation: &EmptyV1LaneForestWalletActivationV2,
    cipher: &NoteStoreCipherV1,
    protection_id: [u8; 32],
) -> Result<Vec<u8>, LaneForestWalletTxnErrorV2> {
    if !activation.requires_monotonic_protection_v2()
        || protection_id == [0u8; 32]
        || cipher.cipher_id() != activation.note_cipher_id
    {
        return Err(LaneForestWalletTxnErrorV2::MonotonicRequired);
    }
    let records = Vec::new();
    let tentative = Vec::new();
    let state = initial_committed_state_v2(activation);
    verify_retained_note_openings_v2(&state, &records, cipher)?;
    encode_authoritative_image_v2(
        activation,
        &records,
        &tentative,
        Some(LaneForestWalletMonotonicMetadataV3 {
            protection_id,
            generation: 0,
            predecessor_commitment: [0u8; 32],
        }),
    )
}

/// Recover the migration-bound activation capability embedded in a fully
/// validated protected ASL2 image. This exists for ASMG restart recovery:
/// after `Prepared`, legacy constructors are intentionally fenced and cannot
/// be reopened merely to reconstruct the activation object.
pub fn validated_protected_activation_from_image_v2(
    bytes: &[u8],
    cipher: &NoteStoreCipherV1,
) -> Result<EmptyV1LaneForestWalletActivationV2, LaneForestWalletTxnErrorV2> {
    let (activation, records, _tentative, replayed, monotonic) =
        decode_authoritative_image_v2(bytes)?;
    if !activation.requires_monotonic_protection_v2()
        || monotonic.is_none()
        || cipher.cipher_id() != activation.note_cipher_id
    {
        return Err(LaneForestWalletTxnErrorV2::MonotonicRequired);
    }
    verify_retained_note_openings_v2(&replayed.committed, &records, cipher)?;
    if let Some(candidate) = &replayed.pending_candidate {
        verify_retained_note_openings_v2(candidate, &records, cipher)?;
    }
    Ok(activation)
}

/// Reconcile an installed protected image with the trusted monotonic store.
/// This is the crash-recovery step between target installation and ownership
/// commit and is exact-replay idempotent.
pub fn reconcile_protected_image_monotonic_v2(
    bytes: &[u8],
    expected_activation: &EmptyV1LaneForestWalletActivationV2,
    cipher: &NoteStoreCipherV1,
    protection_id: [u8; 32],
    store: &mut dyn WalletMonotonicStoreV2,
) -> Result<WalletMonotonicCommitmentV2, LaneForestWalletTxnErrorV2> {
    let (activation, records, tentative, replayed, metadata) =
        decode_authoritative_image_v2(bytes)?;
    if activation.activation_id != expected_activation.activation_id
        || cipher.cipher_id() != activation.note_cipher_id
    {
        return Err(LaneForestWalletTxnErrorV2::ActivationMismatch);
    }
    verify_retained_note_openings_v2(&replayed.committed, &records, cipher)?;
    if let Some(candidate) = &replayed.pending_candidate {
        verify_retained_note_openings_v2(candidate, &records, cipher)?;
    }
    let metadata = metadata.ok_or(LaneForestWalletTxnErrorV2::MonotonicRequired)?;
    if metadata.protection_id != protection_id {
        return Err(LaneForestWalletTxnErrorV2::MonotonicRollback);
    }
    reconcile_monotonic_v3(
        &activation,
        &records,
        &tentative,
        &replayed,
        metadata,
        store,
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LaneForestWalletTentativeUpdateV2 {
    Observed,
    Promoted,
    AlreadyPresent,
    Removed,
    AlreadyAbsent,
}

fn reconcile_monotonic_v3(
    activation: &EmptyV1LaneForestWalletActivationV2,
    records: &[LaneForestWalletTxnRecordV2],
    tentative_observations: &[LaneForestWalletTentativeObservationV2],
    replayed: &ReplayedAuthoritativeImageV2,
    metadata: LaneForestWalletMonotonicMetadataV3,
    store: &mut dyn WalletMonotonicStoreV2,
) -> Result<WalletMonotonicCommitmentV2, LaneForestWalletTxnErrorV2> {
    let state_digest =
        authoritative_content_digest_v3(activation, records, tentative_observations)?;
    let finalized_point = replayed
        .pending_candidate
        .as_ref()
        .unwrap_or(&replayed.committed)
        .finalized_head;
    let candidate = monotonic_commitment_v3(metadata, finalized_point, state_digest)?;
    match store.current_commitment_v2()? {
        None if metadata.generation == 0 => {
            store.compare_and_advance_v2(None, candidate)?;
        }
        Some(current) if current == candidate => {}
        Some(current)
            if metadata.generation == current.generation().saturating_add(1)
                && metadata.predecessor_commitment == current.commitment_digest_v2() =>
        {
            store.compare_and_advance_v2(Some(current.commitment_digest_v2()), candidate)?;
        }
        _ => return Err(LaneForestWalletTxnErrorV2::MonotonicRollback),
    }
    Ok(candidate)
}

pub struct LaneForestWalletTxnCoordinatorV2 {
    file: AtomicStateFileV1,
    activation: EmptyV1LaneForestWalletActivationV2,
    records: Vec<LaneForestWalletTxnRecordV2>,
    tentative_observations: Vec<LaneForestWalletTentativeObservationV2>,
    committed: LaneForestWalletCommittedStateV2,
    pending_candidate: Option<LaneForestWalletCommittedStateV2>,
    monotonic_metadata: Option<LaneForestWalletMonotonicMetadataV3>,
    monotonic_store: Option<Box<dyn WalletMonotonicStoreV2>>,
    poisoned: bool,
}

impl LaneForestWalletTxnCoordinatorV2 {
    pub fn open_or_create_v2(
        path: impl AsRef<Path>,
        activation: EmptyV1LaneForestWalletActivationV2,
        cipher: &NoteStoreCipherV1,
    ) -> Result<Self, LaneForestWalletTxnErrorV2> {
        Self::open_or_create_with_faults_v2(
            path,
            activation,
            cipher,
            &mut NoLaneForestWalletTxnFaultsV2,
        )
    }

    pub fn open_or_create_with_faults_v2<F: LaneForestWalletTxnFaultInjectorV2>(
        path: impl AsRef<Path>,
        activation: EmptyV1LaneForestWalletActivationV2,
        cipher: &NoteStoreCipherV1,
        faults: &mut F,
    ) -> Result<Self, LaneForestWalletTxnErrorV2> {
        if activation.requires_monotonic_protection_v2() {
            return Err(LaneForestWalletTxnErrorV2::MonotonicRequired);
        }
        Self::open_or_create_inner_v2(path, activation, cipher, None, faults)
    }

    pub fn open_or_create_protected_v2(
        path: impl AsRef<Path>,
        activation: EmptyV1LaneForestWalletActivationV2,
        cipher: &NoteStoreCipherV1,
        protection_id: [u8; 32],
        monotonic_store: Box<dyn WalletMonotonicStoreV2>,
    ) -> Result<Self, LaneForestWalletTxnErrorV2> {
        Self::open_or_create_protected_with_faults_v2(
            path,
            activation,
            cipher,
            protection_id,
            monotonic_store,
            &mut NoLaneForestWalletTxnFaultsV2,
        )
    }

    pub fn open_or_create_protected_with_faults_v2<F: LaneForestWalletTxnFaultInjectorV2>(
        path: impl AsRef<Path>,
        activation: EmptyV1LaneForestWalletActivationV2,
        cipher: &NoteStoreCipherV1,
        protection_id: [u8; 32],
        monotonic_store: Box<dyn WalletMonotonicStoreV2>,
        faults: &mut F,
    ) -> Result<Self, LaneForestWalletTxnErrorV2> {
        if protection_id == [0u8; 32] {
            return Err(LaneForestWalletTxnErrorV2::MonotonicRequired);
        }
        Self::open_or_create_inner_v2(
            path,
            activation,
            cipher,
            Some((protection_id, monotonic_store)),
            faults,
        )
    }

    fn open_or_create_inner_v2<F: LaneForestWalletTxnFaultInjectorV2>(
        path: impl AsRef<Path>,
        activation: EmptyV1LaneForestWalletActivationV2,
        cipher: &NoteStoreCipherV1,
        mut monotonic: Option<([u8; 32], Box<dyn WalletMonotonicStoreV2>)>,
        faults: &mut F,
    ) -> Result<Self, LaneForestWalletTxnErrorV2> {
        if cipher.cipher_id() != activation.note_cipher_id {
            return Err(LaneForestWalletTxnErrorV2::NoteCipherMismatch);
        }
        if activation.requires_monotonic_protection_v2() != monotonic.is_some() {
            return Err(LaneForestWalletTxnErrorV2::MonotonicRequired);
        }
        let file = AtomicStateFileV1::acquire(path.as_ref())?;
        if let Some(bytes) = file.read_optional()? {
            let (stored_activation, records, tentative_observations, replayed, metadata) =
                decode_authoritative_image_v2(&bytes)?;
            if !bool::from(
                stored_activation
                    .activation_id
                    .ct_eq(&activation.activation_id),
            ) {
                return Err(LaneForestWalletTxnErrorV2::ActivationMismatch);
            }
            verify_retained_note_openings_v2(&replayed.committed, &records, cipher)?;
            if let Some(candidate) = &replayed.pending_candidate {
                verify_retained_note_openings_v2(candidate, &records, cipher)?;
            }
            if let Some((protection_id, store)) = monotonic.as_mut() {
                let metadata = metadata.ok_or(LaneForestWalletTxnErrorV2::MonotonicRequired)?;
                if metadata.protection_id != *protection_id {
                    return Err(LaneForestWalletTxnErrorV2::MonotonicRollback);
                }
                reconcile_monotonic_v3(
                    &stored_activation,
                    &records,
                    &tentative_observations,
                    &replayed,
                    metadata,
                    store.as_mut(),
                )?;
            }
            return Ok(Self {
                file,
                activation: stored_activation,
                records,
                tentative_observations,
                committed: replayed.committed,
                pending_candidate: replayed.pending_candidate,
                monotonic_metadata: metadata,
                monotonic_store: monotonic.map(|(_, store)| store),
                poisoned: false,
            });
        }
        let records = Vec::new();
        let tentative_observations = Vec::new();
        let monotonic_metadata =
            monotonic
                .as_ref()
                .map(|(protection_id, _)| LaneForestWalletMonotonicMetadataV3 {
                    protection_id: *protection_id,
                    generation: 0,
                    predecessor_commitment: [0u8; 32],
                });
        let bytes = encode_authoritative_image_v2(
            &activation,
            &records,
            &tentative_observations,
            monotonic_metadata,
        )?;
        let mut injected = None;
        if let Err(error) = file.replace_with_fault_v1(&bytes, |boundary| {
            let point = LaneForestWalletTxnAtomicFaultPointV2 {
                write: LaneForestWalletTxnWriteV2::Activation,
                boundary: public_atomic_boundary_v2(boundary),
            };
            if faults.interrupt_atomic_v2(point) {
                injected = Some(point);
                Err(DurableStateErrorV1::Io(io::ErrorKind::Interrupted))
            } else {
                Ok(())
            }
        }) {
            return Err(injected.map_or(
                LaneForestWalletTxnErrorV2::Durable(error),
                LaneForestWalletTxnErrorV2::InjectedAtomicFault,
            ));
        }
        if let Some((_, store)) = monotonic.as_mut() {
            let metadata =
                monotonic_metadata.ok_or(LaneForestWalletTxnErrorV2::MonotonicRequired)?;
            let state_digest =
                authoritative_content_digest_v3(&activation, &records, &tentative_observations)?;
            let commitment = monotonic_commitment_v3(metadata, activation.anchor, state_digest)?;
            match store.compare_and_advance_v2(None, commitment)? {
                WalletMonotonicAdvanceV2::Advanced | WalletMonotonicAdvanceV2::AlreadyCurrent => {}
            }
        }
        Ok(Self {
            file,
            committed: initial_committed_state_v2(&activation),
            activation,
            records,
            tentative_observations,
            pending_candidate: None,
            monotonic_metadata,
            monotonic_store: monotonic.map(|(_, store)| store),
            poisoned: false,
        })
    }

    pub fn committed_state(
        &self,
    ) -> Result<&LaneForestWalletCommittedStateV2, LaneForestWalletTxnErrorV2> {
        self.ensure_readable_v2()?;
        Ok(&self.committed)
    }

    pub fn activation_v2(
        &self,
    ) -> Result<&EmptyV1LaneForestWalletActivationV2, LaneForestWalletTxnErrorV2> {
        self.ensure_readable_v2()?;
        Ok(&self.activation)
    }

    pub(crate) fn authoritative_target_image_v2(
        &self,
    ) -> Result<(&Path, Vec<u8>), LaneForestWalletTxnErrorV2> {
        self.ensure_readable_v2()?;
        let bytes = self
            .file
            .read_optional()?
            .ok_or(LaneForestWalletTxnErrorV2::WrongLength)?;
        Ok((self.file.path_v1(), bytes))
    }

    pub fn records(&self) -> Result<&[LaneForestWalletTxnRecordV2], LaneForestWalletTxnErrorV2> {
        self.ensure_readable_v2()?;
        Ok(&self.records)
    }

    pub fn tentative_observations(
        &self,
    ) -> Result<&[LaneForestWalletTentativeObservationV2], LaneForestWalletTxnErrorV2> {
        self.ensure_readable_v2()?;
        Ok(&self.tentative_observations)
    }

    pub fn pending_phase_v2(
        &self,
    ) -> Result<Option<LaneForestWalletTxnPhaseV2>, LaneForestWalletTxnErrorV2> {
        self.ensure_live_v2()?;
        Ok(self.pending_phase_unchecked_v2())
    }

    fn pending_phase_unchecked_v2(&self) -> Option<LaneForestWalletTxnPhaseV2> {
        self.records.last().and_then(|record| {
            (record.phase != LaneForestWalletTxnPhaseV2::Committed).then_some(record.phase)
        })
    }

    pub fn is_poisoned_v2(&self) -> bool {
        self.poisoned
    }

    pub fn monotonic_protection_id_v2(&self) -> Option<&[u8; 32]> {
        self.monotonic_metadata
            .as_ref()
            .map(|metadata| &metadata.protection_id)
    }

    /// Return the injected backend's production qualification only when it is
    /// bound to this exact ASL2 protection identity. The deterministic
    /// in-memory store intentionally has no such qualification.
    pub fn production_monotonic_qualification_v2(
        &self,
    ) -> Result<WalletMonotonicStoreQualificationV2, LaneForestWalletTxnErrorV2> {
        self.ensure_readable_v2()?;
        let protection_id = self
            .monotonic_protection_id_v2()
            .ok_or(LaneForestWalletTxnErrorV2::MonotonicRequired)?;
        let qualification = self
            .monotonic_store
            .as_ref()
            .and_then(|store| store.production_qualification_v2())
            .ok_or(LaneForestWalletTxnErrorV2::MonotonicRequired)?;
        if qualification.protection_id() != protection_id {
            return Err(LaneForestWalletTxnErrorV2::MonotonicRollback);
        }
        Ok(qualification)
    }

    pub fn current_monotonic_commitment_v2(
        &self,
    ) -> Result<Option<WalletMonotonicCommitmentV2>, LaneForestWalletTxnErrorV2> {
        let Some(metadata) = self.monotonic_metadata else {
            return Ok(None);
        };
        let state_digest = authoritative_content_digest_v3(
            &self.activation,
            &self.records,
            &self.tentative_observations,
        )?;
        let finalized_point = self
            .pending_candidate
            .as_ref()
            .unwrap_or(&self.committed)
            .finalized_head;
        Ok(Some(monotonic_commitment_v3(
            metadata,
            finalized_point,
            state_digest,
        )?))
    }

    /// Return the current commitment only when the ASL2 image and the
    /// injected trusted monotonic backend agree exactly. Activation uses this
    /// stronger query rather than trusting image metadata alone.
    pub fn externally_anchored_monotonic_commitment_v2(
        &self,
    ) -> Result<WalletMonotonicCommitmentV2, LaneForestWalletTxnErrorV2> {
        self.ensure_readable_v2()?;
        let candidate = self
            .current_monotonic_commitment_v2()?
            .ok_or(LaneForestWalletTxnErrorV2::MonotonicRequired)?;
        let store = self
            .monotonic_store
            .as_ref()
            .ok_or(LaneForestWalletTxnErrorV2::MonotonicRequired)?;
        if store.current_commitment_v2()? != Some(candidate) {
            return Err(LaneForestWalletTxnErrorV2::MonotonicRollback);
        }
        Ok(candidate)
    }

    pub fn prepare_finalized_v2<A: LocalSpendAuthenticatorV1>(
        &mut self,
        intent: LaneForestWalletTxnIntentV2,
        cipher: &NoteStoreCipherV1,
        authenticator: &A,
    ) -> Result<LaneForestWalletTxnPrepareV2, LaneForestWalletTxnErrorV2> {
        self.prepare_finalized_with_faults_v2(
            intent,
            cipher,
            authenticator,
            &mut NoLaneForestWalletTxnFaultsV2,
        )
    }

    pub fn prepare_finalized_with_faults_v2<
        A: LocalSpendAuthenticatorV1,
        F: LaneForestWalletTxnFaultInjectorV2,
    >(
        &mut self,
        intent: LaneForestWalletTxnIntentV2,
        cipher: &NoteStoreCipherV1,
        authenticator: &A,
        faults: &mut F,
    ) -> Result<LaneForestWalletTxnPrepareV2, LaneForestWalletTxnErrorV2> {
        self.ensure_live_v2()?;
        if cipher.cipher_id() != self.committed.note_cipher_id {
            return Err(LaneForestWalletTxnErrorV2::NoteCipherMismatch);
        }
        if intent.note_cipher_id != self.committed.note_cipher_id {
            return Err(LaneForestWalletTxnErrorV2::NoteCipherMismatch);
        }
        let content_digest = content_digest_v2(&intent)?;
        let event_ids = output_event_ids_v2(&intent.event);
        for record in &self.records {
            match &record.operation {
                LaneForestWalletTxnOperationV2::Event(existing)
                    if output_event_ids_v2(&existing.event)
                        .iter()
                        .any(|event_id| event_ids.contains(event_id)) =>
                {
                    return if record.content_digest == content_digest {
                        Ok(LaneForestWalletTxnPrepareV2::AlreadyPresent {
                            transaction_id: record.transaction_id,
                            phase: record.phase,
                        })
                    } else {
                        Err(LaneForestWalletTxnErrorV2::EventConflict)
                    };
                }
                LaneForestWalletTxnOperationV2::EmptyFinalizedBlock(empty)
                    if empty.block.point() == intent.event.point() =>
                {
                    return Err(LaneForestWalletTxnErrorV2::EventConflict)
                }
                _ => {}
            }
        }
        if self.pending_candidate.is_some() {
            return Err(LaneForestWalletTxnErrorV2::PendingTransaction);
        }
        validate_finalized_order_v2(
            &self.committed,
            self.records.last().and_then(|record| record.intent()),
            &intent,
        )?;
        validate_secret_bindings_v2(&self.committed, &intent, cipher, authenticator)?;
        let candidate = apply_intent_structural_v2(&self.committed, &intent)?;
        let before_tentatives = self.tentative_observations.clone();
        let after_tentatives = remove_matching_tentative_v2(&before_tentatives, &intent.event)?;
        let before_state_digest = logical_state_digest_v2(&self.committed, &before_tentatives)?;
        let after_state_digest = logical_state_digest_v2(&candidate, &after_tentatives)?;
        let sequence = self.records.len() as u64 + 1;
        let parent_transaction_id = self
            .records
            .last()
            .map_or([0u8; 32], |record| record.transaction_id);
        let transaction_id = transaction_id_v2(
            sequence,
            parent_transaction_id,
            content_digest,
            before_state_digest,
            after_state_digest,
        );
        let record = LaneForestWalletTxnRecordV2 {
            sequence,
            parent_transaction_id,
            transaction_id,
            content_digest,
            before_state_digest,
            after_state_digest,
            tentative_before_digest: tentative_digest_v2(&before_tentatives)?,
            before_tentatives,
            after_tentatives,
            phase: LaneForestWalletTxnPhaseV2::Prepared,
            operation: LaneForestWalletTxnOperationV2::Event(intent),
        };
        let mut records = self.records.clone();
        records.push(record);
        self.persist_phase_v2(
            records,
            self.tentative_observations.clone(),
            self.committed.clone(),
            Some(candidate),
            LaneForestWalletTxnPhaseV2::Prepared,
            faults,
        )?;
        Ok(LaneForestWalletTxnPrepareV2::Prepared(transaction_id))
    }

    pub fn prepare_empty_finalized_block_v2(
        &mut self,
        empty: LaneForestWalletEmptyFinalizedBlockV2,
    ) -> Result<LaneForestWalletTxnPrepareV2, LaneForestWalletTxnErrorV2> {
        self.prepare_empty_finalized_block_with_faults_v2(empty, &mut NoLaneForestWalletTxnFaultsV2)
    }

    pub fn prepare_empty_finalized_block_with_faults_v2<F: LaneForestWalletTxnFaultInjectorV2>(
        &mut self,
        empty: LaneForestWalletEmptyFinalizedBlockV2,
        faults: &mut F,
    ) -> Result<LaneForestWalletTxnPrepareV2, LaneForestWalletTxnErrorV2> {
        self.ensure_live_v2()?;
        let operation = LaneForestWalletTxnOperationV2::EmptyFinalizedBlock(empty);
        let content_digest = operation_content_digest_v2(&operation)?;
        for record in &self.records {
            if record.operation.point_v2() == empty.block.point() {
                return if matches!(
                    record.operation,
                    LaneForestWalletTxnOperationV2::EmptyFinalizedBlock(_)
                ) && record.content_digest == content_digest
                {
                    Ok(LaneForestWalletTxnPrepareV2::AlreadyPresent {
                        transaction_id: record.transaction_id,
                        phase: record.phase,
                    })
                } else {
                    Err(LaneForestWalletTxnErrorV2::EventConflict)
                };
            }
        }
        if self.pending_candidate.is_some() {
            return Err(LaneForestWalletTxnErrorV2::PendingTransaction);
        }
        if self
            .tentative_observations
            .iter()
            .any(|observation| observation.event.point() == empty.block.point())
        {
            return Err(LaneForestWalletTxnErrorV2::InvalidRelayerObservation);
        }
        validate_empty_finalized_order_v2(&self.committed, &empty)?;
        let candidate = apply_empty_finalized_block_structural_v2(&self.committed, &empty);
        let before_tentatives = self.tentative_observations.clone();
        let after_tentatives = before_tentatives.clone();
        let before_state_digest = logical_state_digest_v2(&self.committed, &before_tentatives)?;
        let after_state_digest = logical_state_digest_v2(&candidate, &after_tentatives)?;
        let sequence = self.records.len() as u64 + 1;
        let parent_transaction_id = self
            .records
            .last()
            .map_or([0u8; 32], |record| record.transaction_id);
        let transaction_id = transaction_id_v2(
            sequence,
            parent_transaction_id,
            content_digest,
            before_state_digest,
            after_state_digest,
        );
        let record = LaneForestWalletTxnRecordV2 {
            sequence,
            parent_transaction_id,
            transaction_id,
            content_digest,
            before_state_digest,
            after_state_digest,
            tentative_before_digest: tentative_digest_v2(&before_tentatives)?,
            before_tentatives,
            after_tentatives,
            phase: LaneForestWalletTxnPhaseV2::Prepared,
            operation,
        };
        let mut records = self.records.clone();
        records.push(record);
        self.persist_phase_v2(
            records,
            self.tentative_observations.clone(),
            self.committed.clone(),
            Some(candidate),
            LaneForestWalletTxnPhaseV2::Prepared,
            faults,
        )?;
        Ok(LaneForestWalletTxnPrepareV2::Prepared(transaction_id))
    }

    pub fn advance_recovery_v2(
        &mut self,
    ) -> Result<LaneForestWalletTxnRecoveryV2, LaneForestWalletTxnErrorV2> {
        self.advance_recovery_with_faults_v2(&mut NoLaneForestWalletTxnFaultsV2)
    }

    pub fn advance_recovery_with_faults_v2<F: LaneForestWalletTxnFaultInjectorV2>(
        &mut self,
        faults: &mut F,
    ) -> Result<LaneForestWalletTxnRecoveryV2, LaneForestWalletTxnErrorV2> {
        self.ensure_live_v2()?;
        let Some(record) = self.records.last() else {
            return Ok(LaneForestWalletTxnRecoveryV2::NoPending);
        };
        let transaction_id = record.transaction_id;
        let target = match record.phase {
            LaneForestWalletTxnPhaseV2::Prepared => LaneForestWalletTxnPhaseV2::StoresApplied,
            LaneForestWalletTxnPhaseV2::StoresApplied => LaneForestWalletTxnPhaseV2::Committed,
            LaneForestWalletTxnPhaseV2::Committed => {
                return Ok(LaneForestWalletTxnRecoveryV2::NoPending)
            }
        };
        let candidate = self
            .pending_candidate
            .clone()
            .ok_or(LaneForestWalletTxnErrorV2::StateMismatch)?;
        let mut records = self.records.clone();
        records
            .last_mut()
            .ok_or(LaneForestWalletTxnErrorV2::StateMismatch)?
            .phase = target;
        let tentative_observations = if target == LaneForestWalletTxnPhaseV2::Committed {
            records
                .last()
                .ok_or(LaneForestWalletTxnErrorV2::StateMismatch)?
                .after_tentatives
                .clone()
        } else {
            self.tentative_observations.clone()
        };
        let committed = if target == LaneForestWalletTxnPhaseV2::Committed {
            candidate.clone()
        } else {
            self.committed.clone()
        };
        let pending_candidate =
            (target != LaneForestWalletTxnPhaseV2::Committed).then_some(candidate);
        self.persist_phase_v2(
            records,
            tentative_observations,
            committed,
            pending_candidate,
            target,
            faults,
        )?;
        Ok(match target {
            LaneForestWalletTxnPhaseV2::StoresApplied => {
                LaneForestWalletTxnRecoveryV2::StoresApplied(transaction_id)
            }
            LaneForestWalletTxnPhaseV2::Committed => {
                LaneForestWalletTxnRecoveryV2::Committed(transaction_id)
            }
            LaneForestWalletTxnPhaseV2::Prepared => unreachable!("recovery only advances"),
        })
    }

    pub fn recover_to_committed_v2(
        &mut self,
    ) -> Result<LaneForestWalletTxnRecoveryV2, LaneForestWalletTxnErrorV2> {
        self.recover_to_committed_with_faults_v2(&mut NoLaneForestWalletTxnFaultsV2)
    }

    pub fn recover_to_committed_with_faults_v2<F: LaneForestWalletTxnFaultInjectorV2>(
        &mut self,
        faults: &mut F,
    ) -> Result<LaneForestWalletTxnRecoveryV2, LaneForestWalletTxnErrorV2> {
        self.ensure_live_v2()?;
        let mut outcome = LaneForestWalletTxnRecoveryV2::NoPending;
        while self.pending_phase_unchecked_v2().is_some() {
            outcome = self.advance_recovery_with_faults_v2(faults)?;
        }
        Ok(outcome)
    }

    pub fn observe_tentative_v2(
        &mut self,
        event: ForestFinalizedAppendEventV2,
        commitment: LaneForestWalletTentativeCommitmentV2,
        provider_set_digest: [u8; 32],
    ) -> Result<LaneForestWalletTentativeUpdateV2, LaneForestWalletTxnErrorV2> {
        self.observe_tentative_with_faults_v2(
            event,
            commitment,
            provider_set_digest,
            &mut NoLaneForestWalletTxnFaultsV2,
        )
    }

    pub fn observe_tentative_with_faults_v2<F: LaneForestWalletTxnFaultInjectorV2>(
        &mut self,
        event: ForestFinalizedAppendEventV2,
        commitment: LaneForestWalletTentativeCommitmentV2,
        provider_set_digest: [u8; 32],
        faults: &mut F,
    ) -> Result<LaneForestWalletTentativeUpdateV2, LaneForestWalletTxnErrorV2> {
        self.ensure_live_v2()?;
        if self.pending_candidate.is_some() {
            return Err(LaneForestWalletTxnErrorV2::PendingTransaction);
        }
        let observation =
            LaneForestWalletTentativeObservationV2::new_v2(event, commitment, provider_set_digest)?;
        if observation.event.point().slot() <= self.committed.finalized_head.slot() {
            return Err(LaneForestWalletTxnErrorV2::FinalizedRollback);
        }
        let ids = output_event_ids_v2(&observation.event);
        if self.records.iter().any(|record| {
            matches!(
                &record.operation,
                LaneForestWalletTxnOperationV2::Event(intent)
                    if output_event_ids_v2(&intent.event)
                        .iter()
                        .any(|event_id| ids.contains(event_id))
            )
        }) {
            return Err(LaneForestWalletTxnErrorV2::FinalizedRollback);
        }
        let mut observations = self.tentative_observations.clone();
        let mut update = LaneForestWalletTentativeUpdateV2::Observed;
        if let Some(existing) = observations.iter_mut().find(|existing| {
            output_event_ids_v2(&existing.event)
                .iter()
                .any(|event_id| ids.contains(event_id))
        }) {
            if existing.event_wire != observation.event_wire
                || existing.provider_set_digest != observation.provider_set_digest
            {
                return Err(LaneForestWalletTxnErrorV2::EventConflict);
            }
            update = match (existing.commitment, observation.commitment) {
                (current, next) if current == next => {
                    return Ok(LaneForestWalletTentativeUpdateV2::AlreadyPresent)
                }
                (
                    LaneForestWalletTentativeCommitmentV2::Unfinalized,
                    LaneForestWalletTentativeCommitmentV2::Confirmed,
                ) => LaneForestWalletTentativeUpdateV2::Promoted,
                (
                    LaneForestWalletTentativeCommitmentV2::Confirmed,
                    LaneForestWalletTentativeCommitmentV2::Unfinalized,
                ) => return Err(LaneForestWalletTxnErrorV2::FinalizedRollback),
                _ => return Err(LaneForestWalletTxnErrorV2::InvalidRelayerObservation),
            };
            existing.commitment = observation.commitment;
        } else {
            observations.push(observation);
        }
        sort_tentative_ledger_v2(&mut observations);
        validate_tentative_ledger_v2(&observations)?;
        self.persist_tentative_v2(observations, faults)?;
        Ok(update)
    }

    pub fn reorg_tentative_v2(
        &mut self,
        event: &ForestFinalizedAppendEventV2,
        reorg_evidence_sha256: [u8; 32],
        provider_set_digest: [u8; 32],
    ) -> Result<LaneForestWalletTentativeUpdateV2, LaneForestWalletTxnErrorV2> {
        self.reorg_tentative_with_faults_v2(
            event,
            reorg_evidence_sha256,
            provider_set_digest,
            &mut NoLaneForestWalletTxnFaultsV2,
        )
    }

    pub fn reorg_tentative_with_faults_v2<F: LaneForestWalletTxnFaultInjectorV2>(
        &mut self,
        event: &ForestFinalizedAppendEventV2,
        reorg_evidence_sha256: [u8; 32],
        provider_set_digest: [u8; 32],
        faults: &mut F,
    ) -> Result<LaneForestWalletTentativeUpdateV2, LaneForestWalletTxnErrorV2> {
        self.ensure_live_v2()?;
        if reorg_evidence_sha256 == [0u8; 32] || provider_set_digest == [0u8; 32] {
            return Err(LaneForestWalletTxnErrorV2::InvalidRelayerObservation);
        }
        if self.pending_candidate.is_some() {
            return Err(LaneForestWalletTxnErrorV2::PendingTransaction);
        }
        let canonical = encode_forest_finalized_append_event_v2(event)?;
        let ids = output_event_ids_v2(event);
        if self.records.iter().any(|record| {
            matches!(
                &record.operation,
                LaneForestWalletTxnOperationV2::Event(intent)
                    if output_event_ids_v2(&intent.event)
                        .iter()
                        .any(|event_id| ids.contains(event_id))
            )
        }) {
            return Err(LaneForestWalletTxnErrorV2::FinalizedRollback);
        }
        let mut observations = self.tentative_observations.clone();
        let Some(index) = observations.iter().position(|observation| {
            output_event_ids_v2(&observation.event)
                .iter()
                .any(|event_id| ids.contains(event_id))
        }) else {
            return Ok(LaneForestWalletTentativeUpdateV2::AlreadyAbsent);
        };
        if observations[index].event_wire != canonical
            || observations[index].provider_set_digest != provider_set_digest
        {
            return Err(LaneForestWalletTxnErrorV2::EventConflict);
        }
        observations.remove(index);
        self.persist_tentative_v2(observations, faults)?;
        Ok(LaneForestWalletTentativeUpdateV2::Removed)
    }

    fn persist_tentative_v2<F: LaneForestWalletTxnFaultInjectorV2>(
        &mut self,
        observations: Vec<LaneForestWalletTentativeObservationV2>,
        faults: &mut F,
    ) -> Result<(), LaneForestWalletTxnErrorV2> {
        let (bytes, next_monotonic, monotonic_advance) = self.prepare_next_image_v2(
            &self.records,
            &observations,
            &self.committed,
            self.pending_candidate.as_ref(),
        )?;
        self.replace_with_faults_v2(
            &bytes,
            LaneForestWalletTxnWriteV2::TentativeObservation,
            faults,
        )?;
        self.advance_monotonic_after_replace_v2(monotonic_advance)?;
        self.tentative_observations = observations;
        self.monotonic_metadata = next_monotonic;
        Ok(())
    }

    fn persist_phase_v2<F: LaneForestWalletTxnFaultInjectorV2>(
        &mut self,
        records: Vec<LaneForestWalletTxnRecordV2>,
        tentative_observations: Vec<LaneForestWalletTentativeObservationV2>,
        committed: LaneForestWalletCommittedStateV2,
        pending_candidate: Option<LaneForestWalletCommittedStateV2>,
        phase: LaneForestWalletTxnPhaseV2,
        faults: &mut F,
    ) -> Result<(), LaneForestWalletTxnErrorV2> {
        let (before, after, write) = match phase {
            LaneForestWalletTxnPhaseV2::Prepared => (
                LaneForestWalletTxnFaultPointV2::BeforePreparedReplace,
                LaneForestWalletTxnFaultPointV2::AfterPreparedReplace,
                LaneForestWalletTxnWriteV2::Prepared,
            ),
            LaneForestWalletTxnPhaseV2::StoresApplied => (
                LaneForestWalletTxnFaultPointV2::BeforeStoresAppliedReplace,
                LaneForestWalletTxnFaultPointV2::AfterStoresAppliedReplace,
                LaneForestWalletTxnWriteV2::StoresApplied,
            ),
            LaneForestWalletTxnPhaseV2::Committed => (
                LaneForestWalletTxnFaultPointV2::BeforeCommittedReplace,
                LaneForestWalletTxnFaultPointV2::AfterCommittedReplace,
                LaneForestWalletTxnWriteV2::Committed,
            ),
        };
        if faults.interrupt_v2(before) {
            self.poisoned = true;
            return Err(LaneForestWalletTxnErrorV2::InjectedFault(before));
        }
        let (bytes, next_monotonic, monotonic_advance) = self.prepare_next_image_v2(
            &records,
            &tentative_observations,
            &committed,
            pending_candidate.as_ref(),
        )?;
        self.replace_with_faults_v2(&bytes, write, faults)?;
        self.advance_monotonic_after_replace_v2(monotonic_advance)?;
        self.records = records;
        self.tentative_observations = tentative_observations;
        self.committed = committed;
        self.pending_candidate = pending_candidate;
        self.monotonic_metadata = next_monotonic;
        if faults.interrupt_v2(after) {
            self.poisoned = true;
            return Err(LaneForestWalletTxnErrorV2::InjectedFault(after));
        }
        Ok(())
    }

    fn prepare_next_image_v2(
        &self,
        records: &[LaneForestWalletTxnRecordV2],
        tentative_observations: &[LaneForestWalletTentativeObservationV2],
        committed: &LaneForestWalletCommittedStateV2,
        pending_candidate: Option<&LaneForestWalletCommittedStateV2>,
    ) -> Result<PreparedMonotonicImageV3, LaneForestWalletTxnErrorV2> {
        let Some(current_metadata) = self.monotonic_metadata else {
            let bytes = encode_authoritative_image_v2(
                &self.activation,
                records,
                tentative_observations,
                None,
            )?;
            return Ok((bytes, None, None));
        };
        let current = self
            .current_monotonic_commitment_v2()?
            .ok_or(LaneForestWalletTxnErrorV2::MonotonicRequired)?;
        let generation = current_metadata
            .generation
            .checked_add(1)
            .ok_or(LaneForestWalletTxnErrorV2::CountOverflow)?;
        let next_metadata = LaneForestWalletMonotonicMetadataV3 {
            protection_id: current_metadata.protection_id,
            generation,
            predecessor_commitment: current.commitment_digest_v2(),
        };
        let state_digest =
            authoritative_content_digest_v3(&self.activation, records, tentative_observations)?;
        let finalized_point = pending_candidate.unwrap_or(committed).finalized_head;
        let next = monotonic_commitment_v3(next_metadata, finalized_point, state_digest)?;
        let bytes = encode_authoritative_image_v2(
            &self.activation,
            records,
            tentative_observations,
            Some(next_metadata),
        )?;
        Ok((bytes, Some(next_metadata), Some((current, next))))
    }

    fn advance_monotonic_after_replace_v2(
        &mut self,
        advance: Option<(WalletMonotonicCommitmentV2, WalletMonotonicCommitmentV2)>,
    ) -> Result<(), LaneForestWalletTxnErrorV2> {
        let Some((current, next)) = advance else {
            return Ok(());
        };
        let store = self
            .monotonic_store
            .as_mut()
            .ok_or(LaneForestWalletTxnErrorV2::MonotonicRequired)?;
        match store.compare_and_advance_v2(Some(current.commitment_digest_v2()), next) {
            Ok(WalletMonotonicAdvanceV2::Advanced)
            | Ok(WalletMonotonicAdvanceV2::AlreadyCurrent) => Ok(()),
            Err(error) => {
                self.poisoned = true;
                Err(error.into())
            }
        }
    }

    fn replace_with_faults_v2<F: LaneForestWalletTxnFaultInjectorV2>(
        &mut self,
        bytes: &[u8],
        write: LaneForestWalletTxnWriteV2,
        faults: &mut F,
    ) -> Result<(), LaneForestWalletTxnErrorV2> {
        let mut injected = None;
        let result = self.file.replace_with_fault_v1(bytes, |boundary| {
            let point = LaneForestWalletTxnAtomicFaultPointV2 {
                write,
                boundary: public_atomic_boundary_v2(boundary),
            };
            if faults.interrupt_atomic_v2(point) {
                injected = Some(point);
                Err(DurableStateErrorV1::Io(io::ErrorKind::Interrupted))
            } else {
                Ok(())
            }
        });
        if let Err(error) = result {
            self.poisoned = true;
            return Err(injected.map_or(
                LaneForestWalletTxnErrorV2::Durable(error),
                LaneForestWalletTxnErrorV2::InjectedAtomicFault,
            ));
        }
        Ok(())
    }

    fn ensure_live_v2(&self) -> Result<(), LaneForestWalletTxnErrorV2> {
        if self.poisoned {
            Err(LaneForestWalletTxnErrorV2::Poisoned)
        } else {
            Ok(())
        }
    }

    fn ensure_readable_v2(&self) -> Result<(), LaneForestWalletTxnErrorV2> {
        self.ensure_live_v2()?;
        if self.pending_candidate.is_some() {
            Err(LaneForestWalletTxnErrorV2::PendingTransaction)
        } else {
            Ok(())
        }
    }
}

fn public_atomic_boundary_v2(
    boundary: AtomicReplaceBoundaryV1,
) -> LaneForestWalletTxnAtomicBoundaryV2 {
    match boundary {
        AtomicReplaceBoundaryV1::TemporaryWrite => {
            LaneForestWalletTxnAtomicBoundaryV2::TemporaryWrite
        }
        AtomicReplaceBoundaryV1::TemporaryFileSync => {
            LaneForestWalletTxnAtomicBoundaryV2::TemporaryFileSync
        }
        AtomicReplaceBoundaryV1::TargetRename => LaneForestWalletTxnAtomicBoundaryV2::TargetRename,
        AtomicReplaceBoundaryV1::ParentDirectorySync => {
            LaneForestWalletTxnAtomicBoundaryV2::ParentDirectorySync
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::*;
    use crate::relayer_execution_journal::{
        InspectedSignedTransactionV1, RelayerExecutionJournalErrorV1,
        RelayerExecutionJournalUpdateV1, RelayerFinalizedEvidenceV1,
        RelayerFinalizedFailureEvidenceV1, RelayerSimulationEvidenceV1,
        RelayerTerminalFailureEvidenceV1, SignedTransactionInspectorV1,
    };

    static NEXT_RELAYER_JOURNAL_DIRECTORY_V2: AtomicU64 = AtomicU64::new(0);

    struct RelayerJournalTestDirectoryV2(std::path::PathBuf);

    impl RelayerJournalTestDirectoryV2 {
        fn new() -> Self {
            let serial = NEXT_RELAYER_JOURNAL_DIRECTORY_V2.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "aspis-lane-wallet-relayer-capability-{}-{}",
                std::process::id(),
                serial
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }
    }

    impl Drop for RelayerJournalTestDirectoryV2 {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    struct RelayerJournalInspectorV2;

    impl SignedTransactionInspectorV1 for RelayerJournalInspectorV2 {
        fn inspect_and_verify_signed_transaction_v1(
            &self,
            signed_wire: &[u8],
        ) -> Option<InspectedSignedTransactionV1> {
            (signed_wire == [1, 2, 3, 4]).then_some(InspectedSignedTransactionV1 {
                transaction_signature: [0x51; 64],
                fee_payer: [0x31; 32],
                unsigned_message_sha256: [0x41; 32],
            })
        }
    }

    fn relayer_simulation_v2() -> RelayerSimulationEvidenceV1 {
        RelayerSimulationEvidenceV1 {
            simulated_at_slot: 100,
            recent_blockhash: [0x21; 32],
            last_valid_block_height: 500,
            fee_payer: [0x31; 32],
            unsigned_message_sha256: [0x41; 32],
            simulation_result_sha256: [0x44; 32],
            simulation_accounts_sha256: [0x42; 32],
            startup_receipt_digest: [0x43; 32],
            compute_unit_limit: 1_400_000,
            compute_unit_price_micro_lamports: 1,
            compute_units_consumed: 1_200_000,
            estimated_fee_lamports: 10_000,
        }
    }

    fn record_signed_request_v2(
        journal: &mut DurableRelayerExecutionJournalV1,
        request_id: [u8; 32],
        policy_id: [u8; 32],
    ) {
        assert_eq!(
            journal
                .record_simulation_v1(request_id, policy_id, relayer_simulation_v2(), &[])
                .unwrap(),
            RelayerExecutionJournalUpdateV1::Inserted
        );
        assert_eq!(
            journal
                .record_signed_wire_v1(request_id, &[1, 2, 3, 4], &RelayerJournalInspectorV2,)
                .unwrap(),
            RelayerExecutionJournalUpdateV1::Inserted
        );
    }

    fn empty_wire_v2() -> IntentWireV2 {
        IntentWireV2 {
            finalized_parent: Vec::new(),
            event_wire: Vec::new(),
            note_cipher_id: Vec::new(),
            notes: Vec::new(),
            spends: Vec::new(),
            checkpoint: None,
            relayer: None,
        }
    }

    fn note_wire_v2(order: u8) -> NoteWireV2 {
        NoteWireV2 {
            event_id: vec![order; 108],
            access: 1,
            sealed_note: Vec::new(),
            nonce: Vec::new(),
            sealed_sha256: Vec::new(),
        }
    }

    fn spend_wire_v2(order: u8) -> SpendWireV2 {
        SpendWireV2 {
            input_event_id: vec![order; 108],
            transition_output_id: vec![order; 108],
            nullifier: Vec::new(),
        }
    }

    #[test]
    fn typed_intent_wire_order_aliases_are_rejected_before_semantic_decode() {
        let mut wire = empty_wire_v2();
        wire.notes = vec![note_wire_v2(2), note_wire_v2(1)];
        assert_eq!(
            validate_intent_wire_order_v2(&wire),
            Err(LaneForestWalletTxnErrorV2::NonCanonicalEncoding)
        );

        wire.notes.clear();
        wire.spends = vec![spend_wire_v2(2), spend_wire_v2(1)];
        assert_eq!(
            validate_intent_wire_order_v2(&wire),
            Err(LaneForestWalletTxnErrorV2::NonCanonicalEncoding)
        );
    }

    #[test]
    fn finalized_journal_capability_requires_exact_durable_finality_and_survives_restart() {
        let directory = RelayerJournalTestDirectoryV2::new();
        let path = directory.0.join("execution.state");
        let request_id = [0x11; 32];
        let finalized = RelayerFinalizedEvidenceV1 {
            point: FinalizedChainPointV1::new(102, [0x71; 32]).unwrap(),
            fee_lamports: 10_000,
            compute_units_consumed: 1_200_000,
            execution_result_sha256: [0x72; 32],
            poststate_sha256: [0x73; 32],
            provider_set_digest: [0x61; 32],
        };

        let mut journal = DurableRelayerExecutionJournalV1::open_or_create_v1(&path).unwrap();
        assert_eq!(
            LaneForestWalletRelayerObservationV2::from_finalized_journal_v2(&journal, request_id),
            Err(LaneForestWalletTxnErrorV2::InvalidRelayerObservation)
        );

        assert_eq!(
            journal
                .record_simulation_v1(request_id, [0x12; 32], relayer_simulation_v2(), &[],)
                .unwrap(),
            RelayerExecutionJournalUpdateV1::Inserted
        );
        assert_eq!(
            LaneForestWalletRelayerObservationV2::from_finalized_journal_v2(&journal, request_id),
            Err(LaneForestWalletTxnErrorV2::InvalidRelayerObservation)
        );

        assert_eq!(
            journal
                .record_signed_wire_v1(request_id, &[1, 2, 3, 4], &RelayerJournalInspectorV2,)
                .unwrap(),
            RelayerExecutionJournalUpdateV1::Inserted
        );
        assert!(journal.record_v1(request_id).unwrap().submission.is_none());
        assert_eq!(
            LaneForestWalletRelayerObservationV2::from_finalized_journal_v2(&journal, request_id),
            Err(LaneForestWalletTxnErrorV2::InvalidRelayerObservation)
        );

        assert_eq!(
            journal
                .record_finalized_v1(request_id, [0x51; 64], finalized)
                .unwrap(),
            RelayerExecutionJournalUpdateV1::Inserted
        );
        assert!(journal.record_v1(request_id).unwrap().submission.is_none());
        let accepted =
            LaneForestWalletRelayerObservationV2::from_finalized_journal_v2(&journal, request_id)
                .unwrap();
        assert_eq!(accepted.request_id(), &request_id);
        assert_eq!(accepted.transaction_signature(), &[0x51; 64]);
        assert_eq!(accepted.point(), finalized.point());
        assert_eq!(
            journal
                .record_finalized_v1(request_id, [0x51; 64], finalized)
                .unwrap(),
            RelayerExecutionJournalUpdateV1::AlreadyPresent
        );

        let mut conflicting = finalized;
        conflicting.poststate_sha256 = [0x74; 32];
        assert_eq!(
            journal.record_finalized_v1(request_id, [0x51; 64], conflicting),
            Err(RelayerExecutionJournalErrorV1::OutcomeMismatch)
        );
        assert_eq!(
            LaneForestWalletRelayerObservationV2::from_finalized_journal_v2(&journal, request_id)
                .unwrap(),
            accepted
        );
        drop(journal);

        let mut journal = DurableRelayerExecutionJournalV1::open_or_create_v1(&path).unwrap();
        assert!(journal.record_v1(request_id).unwrap().submission.is_none());
        assert_eq!(
            LaneForestWalletRelayerObservationV2::from_finalized_journal_v2(&journal, request_id)
                .unwrap(),
            accepted
        );
        assert_eq!(
            journal
                .record_finalized_v1(request_id, [0x51; 64], finalized)
                .unwrap(),
            RelayerExecutionJournalUpdateV1::AlreadyPresent
        );

        let terminal_request_id = [0x21; 32];
        record_signed_request_v2(&mut journal, terminal_request_id, [0x22; 32]);
        let terminal = RelayerTerminalFailureEvidenceV1 {
            observed_block_height: 501,
            failure_code: 1,
            evidence_sha256: [0x23; 32],
            provider_set_digest: [0x24; 32],
        };
        assert_eq!(
            journal
                .record_terminal_failure_v1(terminal_request_id, terminal)
                .unwrap(),
            RelayerExecutionJournalUpdateV1::Inserted
        );
        assert_eq!(
            LaneForestWalletRelayerObservationV2::from_finalized_journal_v2(
                &journal,
                terminal_request_id,
            ),
            Err(LaneForestWalletTxnErrorV2::InvalidRelayerObservation)
        );
        assert_eq!(
            journal.record_finalized_v1(terminal_request_id, [0x51; 64], finalized),
            Err(RelayerExecutionJournalErrorV1::OutcomeMismatch)
        );

        let failed_request_id = [0x31; 32];
        record_signed_request_v2(&mut journal, failed_request_id, [0x32; 32]);
        let failed = RelayerFinalizedFailureEvidenceV1 {
            point: FinalizedChainPointV1::new(103, [0x33; 32]).unwrap(),
            fee_lamports: 10_000,
            compute_units_consumed: 1_100_000,
            failure_evidence_sha256: [0x34; 32],
            provider_set_digest: [0x35; 32],
        };
        assert_eq!(
            journal
                .record_finalized_failure_v1(failed_request_id, [0x51; 64], failed)
                .unwrap(),
            RelayerExecutionJournalUpdateV1::Inserted
        );
        assert_eq!(
            LaneForestWalletRelayerObservationV2::from_finalized_journal_v2(
                &journal,
                failed_request_id,
            ),
            Err(LaneForestWalletTxnErrorV2::InvalidRelayerObservation)
        );
    }
}
