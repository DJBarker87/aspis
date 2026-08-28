//! Default-off permissionless checkpoint operator for the eight-lane forest.
//!
//! The live RPC and signer boundaries are traits. The operator authenticates
//! one coherent finalized master-plus-eight-lane snapshot, skips states with no
//! progress, simulates an exact legacy transaction before signing, journals the
//! signed wire before submission, and never rebuilds a submitted transaction.

use std::path::Path;

use aspis_pool::pool_v1_pair_forest_checkpoint_address;
use aspis_statement::pool_v1::{
    POOL_V1_PAIR_FOREST_ALL_LANES_MASK, POOL_V1_PAIR_FOREST_LANE_COUNT,
};
use bincode::Options as _;
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};
use solana_message::{legacy, VersionedMessage};
use solana_program::{hash::Hash, pubkey::Pubkey};
use solana_signature::Signature;
use solana_transaction::versioned::VersionedTransaction;

use crate::{
    durable_state::{AtomicStateFileV1, DurableStateErrorV1},
    finalized_indexer::SolanaRpcCommitmentV1,
    lane_forest_client_v2::{build_pair_forest_checkpoint_instruction_v2, PairForestClientErrorV2},
    lane_forest_durable_v2::{
        authenticate_forest_checkpoint_account_v2, authenticate_forest_lane_account_v2,
        authenticate_forest_master_account_v2, AuthenticatedForestLaneAccountV2,
        AuthenticatedForestMasterAccountV2, LaneForestDurableErrorV2,
    },
    lane_forest_rpc_v2::FinalizedForestAccountV2,
    scan_state::FinalizedChainPointV1,
};

const CHECKPOINT_JOURNAL_MAGIC_V2: [u8; 4] = *b"ASJ8";
const CHECKPOINT_JOURNAL_VERSION_V2: u8 = 2;
const CHECKPOINT_JOURNAL_HEADER_BYTES_V2: usize = 56;
const CHECKPOINT_JOURNAL_CHECKSUM_OFFSET_V2: usize = 24;
const CHECKPOINT_JOURNAL_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:eight-lane-checkpoint-journal:sha256:v2";
const MAX_CHECKPOINT_JOURNAL_BYTES_V2: usize = 16 * 1024 * 1024;
const MAX_CHECKPOINT_RECORDS_V2: usize = 100_000;
const MAX_CHECKPOINT_TRANSACTION_BYTES_V2: usize = 4_096;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PairForestCheckpointOperatorErrorV2 {
    NotFinalized,
    ContextTooOld,
    ProviderMismatch,
    InvalidSnapshot,
    LaneRegression,
    WrongPayer,
    BlockhashExpired,
    SimulationFailed,
    SignerFailed,
    InvalidSignature,
    RpcFailed,
    SubmissionMismatch,
    FinalizedExecutionFailed,
    FinalizedStateMismatch,
    InvalidJournal,
    JournalConflict,
    ImageTooLarge,
    SerializationFailed,
    Client(PairForestClientErrorV2),
    Forest(LaneForestDurableErrorV2),
    Durable(DurableStateErrorV1),
}

impl From<PairForestClientErrorV2> for PairForestCheckpointOperatorErrorV2 {
    fn from(error: PairForestClientErrorV2) -> Self {
        Self::Client(error)
    }
}

impl From<LaneForestDurableErrorV2> for PairForestCheckpointOperatorErrorV2 {
    fn from(error: LaneForestDurableErrorV2) -> Self {
        Self::Forest(error)
    }
}

impl From<DurableStateErrorV1> for PairForestCheckpointOperatorErrorV2 {
    fn from(error: DurableStateErrorV1) -> Self {
        Self::Durable(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedPairForestCheckpointSnapshotV2 {
    pub point: FinalizedChainPointV1,
    pub context_slot: u64,
    pub commitment: SolanaRpcCommitmentV1,
    pub provider_set_digest: [u8; 32],
    pub master: FinalizedForestAccountV2,
    /// Exact lane order, lane 0 through lane 7.
    pub lanes: Vec<FinalizedForestAccountV2>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedCheckpointBlockhashV2 {
    pub context_slot: u64,
    pub block_height: u64,
    pub last_valid_block_height: u64,
    pub blockhash: [u8; 32],
    pub commitment: SolanaRpcCommitmentV1,
    pub provider_set_digest: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckpointSimulationResultV2 {
    pub context_slot: u64,
    pub commitment: SolanaRpcCommitmentV1,
    pub provider_set_digest: [u8; 32],
    pub message_sha256: [u8; 32],
    pub success: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedCheckpointConfirmationV2 {
    pub point: FinalizedChainPointV1,
    pub context_slot: u64,
    pub commitment: SolanaRpcCommitmentV1,
    pub provider_set_digest: [u8; 32],
    pub transaction_signature: [u8; 64],
    pub success: bool,
    pub master: FinalizedForestAccountV2,
    pub checkpoint: FinalizedForestAccountV2,
}

pub trait PairForestCheckpointRpcV2 {
    fn fetch_finalized_checkpoint_snapshot_v2(
        &mut self,
        program_id: Pubkey,
        master: Pubkey,
    ) -> Result<FinalizedPairForestCheckpointSnapshotV2, PairForestCheckpointOperatorErrorV2>;

    fn fetch_finalized_blockhash_v2(
        &mut self,
    ) -> Result<FinalizedCheckpointBlockhashV2, PairForestCheckpointOperatorErrorV2>;

    fn simulate_checkpoint_transaction_v2(
        &mut self,
        unsigned_transaction_wire: &[u8],
    ) -> Result<CheckpointSimulationResultV2, PairForestCheckpointOperatorErrorV2>;

    fn submit_checkpoint_transaction_v2(
        &mut self,
        signed_transaction_wire: &[u8],
    ) -> Result<[u8; 64], PairForestCheckpointOperatorErrorV2>;

    fn confirm_checkpoint_finalized_v2(
        &mut self,
        transaction_signature: [u8; 64],
    ) -> Result<Option<FinalizedCheckpointConfirmationV2>, PairForestCheckpointOperatorErrorV2>;
}

pub trait PairForestCheckpointSignerV2 {
    fn fee_payer_v2(&self) -> Pubkey;

    /// Sign only the exact serialized Solana message supplied by the operator.
    fn sign_checkpoint_message_v2(
        &mut self,
        serialized_message: &[u8],
    ) -> Result<[u8; 64], PairForestCheckpointOperatorErrorV2>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[repr(u8)]
enum CheckpointJournalStageV2 {
    Signed = 1,
    Submitted = 2,
    Finalized = 3,
    Superseded = 4,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct CheckpointJournalRecordImageV2 {
    sequence: u64,
    snapshot_point: Vec<u8>,
    snapshot_provider_set_digest: Vec<u8>,
    lane_sequences: Vec<u64>,
    master_static_binding: Vec<u8>,
    instruction_sha256: Vec<u8>,
    message_sha256: Vec<u8>,
    recent_blockhash: Vec<u8>,
    last_valid_block_height: u64,
    transaction_signature: Vec<u8>,
    signed_wire: Vec<u8>,
    stage: CheckpointJournalStageV2,
    finalized_point: Option<Vec<u8>>,
    finalized_poststate_sha256: Option<Vec<u8>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct CheckpointJournalImageV2 {
    program_id: Vec<u8>,
    master: Vec<u8>,
    records: Vec<CheckpointJournalRecordImageV2>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CheckpointJournalRecordV2 {
    sequence: u64,
    snapshot_point: FinalizedChainPointV1,
    snapshot_provider_set_digest: [u8; 32],
    lane_sequences: [u64; POOL_V1_PAIR_FOREST_LANE_COUNT],
    master_static_binding: [u8; 32],
    instruction_sha256: [u8; 32],
    message_sha256: [u8; 32],
    recent_blockhash: [u8; 32],
    last_valid_block_height: u64,
    transaction_signature: [u8; 64],
    signed_wire: Vec<u8>,
    stage: CheckpointJournalStageV2,
    finalized_point: Option<FinalizedChainPointV1>,
    finalized_poststate_sha256: Option<[u8; 32]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CheckpointJournalStateV2 {
    program_id: [u8; 32],
    master: [u8; 32],
    records: Vec<CheckpointJournalRecordV2>,
}

pub struct DurablePairForestCheckpointJournalV2 {
    file: AtomicStateFileV1,
    state: CheckpointJournalStateV2,
}

fn exact_array_v2<const N: usize>(
    bytes: &[u8],
) -> Result<[u8; N], PairForestCheckpointOperatorErrorV2> {
    bytes
        .try_into()
        .map_err(|_| PairForestCheckpointOperatorErrorV2::InvalidJournal)
}

fn encode_point_v2(point: FinalizedChainPointV1) -> Vec<u8> {
    let mut output = Vec::with_capacity(40);
    output.extend_from_slice(&point.slot().to_le_bytes());
    output.extend_from_slice(point.block_hash());
    output
}

fn decode_point_v2(
    bytes: &[u8],
) -> Result<FinalizedChainPointV1, PairForestCheckpointOperatorErrorV2> {
    if bytes.len() != 40 {
        return Err(PairForestCheckpointOperatorErrorV2::InvalidJournal);
    }
    FinalizedChainPointV1::new(
        u64::from_le_bytes(bytes[..8].try_into().unwrap()),
        bytes[8..].try_into().unwrap(),
    )
    .map_err(|_| PairForestCheckpointOperatorErrorV2::InvalidJournal)
}

fn checkpoint_journal_checksum_v2(header: &[u8], payload: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(CHECKPOINT_JOURNAL_DOMAIN_V2);
    hasher.update(header);
    hasher.update(payload);
    hasher.finalize().into()
}

fn encode_checkpoint_journal_state_v2(
    state: &CheckpointJournalStateV2,
) -> Result<Vec<u8>, PairForestCheckpointOperatorErrorV2> {
    if state.program_id == [0u8; 32]
        || state.master == [0u8; 32]
        || state.records.len() > MAX_CHECKPOINT_RECORDS_V2
    {
        return Err(PairForestCheckpointOperatorErrorV2::InvalidJournal);
    }
    let mut previous = None;
    let records = state
        .records
        .iter()
        .map(|record| {
            if previous.is_some_and(|sequence| sequence >= record.sequence)
                || record.snapshot_provider_set_digest == [0u8; 32]
                || record.signed_wire.is_empty()
                || record.signed_wire.len() > MAX_CHECKPOINT_TRANSACTION_BYTES_V2
                || record.finalized_point.is_some()
                    != (record.stage == CheckpointJournalStageV2::Finalized)
                || record.finalized_poststate_sha256.is_some()
                    != (record.stage == CheckpointJournalStageV2::Finalized)
            {
                return Err(PairForestCheckpointOperatorErrorV2::InvalidJournal);
            }
            previous = Some(record.sequence);
            Ok(CheckpointJournalRecordImageV2 {
                sequence: record.sequence,
                snapshot_point: encode_point_v2(record.snapshot_point),
                snapshot_provider_set_digest: record.snapshot_provider_set_digest.to_vec(),
                lane_sequences: record.lane_sequences.to_vec(),
                master_static_binding: record.master_static_binding.to_vec(),
                instruction_sha256: record.instruction_sha256.to_vec(),
                message_sha256: record.message_sha256.to_vec(),
                recent_blockhash: record.recent_blockhash.to_vec(),
                last_valid_block_height: record.last_valid_block_height,
                transaction_signature: record.transaction_signature.to_vec(),
                signed_wire: record.signed_wire.clone(),
                stage: record.stage,
                finalized_point: record.finalized_point.map(encode_point_v2),
                finalized_poststate_sha256: record
                    .finalized_poststate_sha256
                    .map(|digest| digest.to_vec()),
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let image = CheckpointJournalImageV2 {
        program_id: state.program_id.to_vec(),
        master: state.master.to_vec(),
        records,
    };
    let payload = bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .reject_trailing_bytes()
        .serialize(&image)
        .map_err(|_| PairForestCheckpointOperatorErrorV2::SerializationFailed)?;
    let total = CHECKPOINT_JOURNAL_HEADER_BYTES_V2
        .checked_add(payload.len())
        .ok_or(PairForestCheckpointOperatorErrorV2::ImageTooLarge)?;
    if total > MAX_CHECKPOINT_JOURNAL_BYTES_V2 {
        return Err(PairForestCheckpointOperatorErrorV2::ImageTooLarge);
    }
    let mut header = [0u8; CHECKPOINT_JOURNAL_HEADER_BYTES_V2];
    header[..4].copy_from_slice(&CHECKPOINT_JOURNAL_MAGIC_V2);
    header[4] = CHECKPOINT_JOURNAL_VERSION_V2;
    header[8..16].copy_from_slice(&(payload.len() as u64).to_le_bytes());
    header[16..20].copy_from_slice(&(state.records.len() as u32).to_le_bytes());
    let checksum = checkpoint_journal_checksum_v2(&header, &payload);
    header[CHECKPOINT_JOURNAL_CHECKSUM_OFFSET_V2..].copy_from_slice(&checksum);
    let mut output = Vec::with_capacity(total);
    output.extend_from_slice(&header);
    output.extend_from_slice(&payload);
    Ok(output)
}

fn decode_checkpoint_journal_state_v2(
    bytes: &[u8],
) -> Result<CheckpointJournalStateV2, PairForestCheckpointOperatorErrorV2> {
    if bytes.len() < CHECKPOINT_JOURNAL_HEADER_BYTES_V2
        || bytes.len() > MAX_CHECKPOINT_JOURNAL_BYTES_V2
        || bytes[..4] != CHECKPOINT_JOURNAL_MAGIC_V2
        || bytes[4] != CHECKPOINT_JOURNAL_VERSION_V2
        || bytes[5..8] != [0u8; 3]
        || bytes[20..24] != [0u8; 4]
    {
        return Err(PairForestCheckpointOperatorErrorV2::InvalidJournal);
    }
    let payload_len = u64::from_le_bytes(bytes[8..16].try_into().unwrap()) as usize;
    if bytes.len() != CHECKPOINT_JOURNAL_HEADER_BYTES_V2 + payload_len {
        return Err(PairForestCheckpointOperatorErrorV2::InvalidJournal);
    }
    let stored: [u8; 32] = bytes[CHECKPOINT_JOURNAL_CHECKSUM_OFFSET_V2..56]
        .try_into()
        .unwrap();
    let mut header = bytes[..CHECKPOINT_JOURNAL_HEADER_BYTES_V2].to_vec();
    header[CHECKPOINT_JOURNAL_CHECKSUM_OFFSET_V2..].fill(0);
    let payload = &bytes[CHECKPOINT_JOURNAL_HEADER_BYTES_V2..];
    if checkpoint_journal_checksum_v2(&header, payload) != stored {
        return Err(PairForestCheckpointOperatorErrorV2::InvalidJournal);
    }
    let image: CheckpointJournalImageV2 = bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .reject_trailing_bytes()
        .deserialize(payload)
        .map_err(|_| PairForestCheckpointOperatorErrorV2::InvalidJournal)?;
    if image.records.len() != u32::from_le_bytes(bytes[16..20].try_into().unwrap()) as usize
        || image.records.len() > MAX_CHECKPOINT_RECORDS_V2
    {
        return Err(PairForestCheckpointOperatorErrorV2::InvalidJournal);
    }
    let mut records = Vec::with_capacity(image.records.len());
    for record in image.records {
        if record.lane_sequences.len() != POOL_V1_PAIR_FOREST_LANE_COUNT {
            return Err(PairForestCheckpointOperatorErrorV2::InvalidJournal);
        }
        records.push(CheckpointJournalRecordV2 {
            sequence: record.sequence,
            snapshot_point: decode_point_v2(&record.snapshot_point)?,
            snapshot_provider_set_digest: exact_array_v2(&record.snapshot_provider_set_digest)?,
            lane_sequences: record
                .lane_sequences
                .try_into()
                .map_err(|_| PairForestCheckpointOperatorErrorV2::InvalidJournal)?,
            master_static_binding: exact_array_v2(&record.master_static_binding)?,
            instruction_sha256: exact_array_v2(&record.instruction_sha256)?,
            message_sha256: exact_array_v2(&record.message_sha256)?,
            recent_blockhash: exact_array_v2(&record.recent_blockhash)?,
            last_valid_block_height: record.last_valid_block_height,
            transaction_signature: exact_array_v2(&record.transaction_signature)?,
            signed_wire: record.signed_wire,
            stage: record.stage,
            finalized_point: record
                .finalized_point
                .as_deref()
                .map(decode_point_v2)
                .transpose()?,
            finalized_poststate_sha256: record
                .finalized_poststate_sha256
                .as_deref()
                .map(exact_array_v2)
                .transpose()?,
        });
    }
    let state = CheckpointJournalStateV2 {
        program_id: exact_array_v2(&image.program_id)?,
        master: exact_array_v2(&image.master)?,
        records,
    };
    // Re-encoding validates record shape and canonical ordering.
    let _ = encode_checkpoint_journal_state_v2(&state)?;
    Ok(state)
}

impl DurablePairForestCheckpointJournalV2 {
    pub fn open_or_create_v2(
        path: impl AsRef<Path>,
        program_id: Pubkey,
        master: Pubkey,
    ) -> Result<Self, PairForestCheckpointOperatorErrorV2> {
        if program_id == Pubkey::default() || master == Pubkey::default() {
            return Err(PairForestCheckpointOperatorErrorV2::InvalidJournal);
        }
        let file = AtomicStateFileV1::acquire(path.as_ref())?;
        let state = match file.read_optional()? {
            Some(bytes) => {
                let state = decode_checkpoint_journal_state_v2(&bytes)?;
                if state.program_id != program_id.to_bytes() || state.master != master.to_bytes() {
                    return Err(PairForestCheckpointOperatorErrorV2::JournalConflict);
                }
                state
            }
            None => {
                let state = CheckpointJournalStateV2 {
                    program_id: program_id.to_bytes(),
                    master: master.to_bytes(),
                    records: Vec::new(),
                };
                file.replace(&encode_checkpoint_journal_state_v2(&state)?)?;
                state
            }
        };
        Ok(Self { file, state })
    }

    fn replace_state_v2(
        &mut self,
        candidate: CheckpointJournalStateV2,
    ) -> Result<(), PairForestCheckpointOperatorErrorV2> {
        self.file
            .replace(&encode_checkpoint_journal_state_v2(&candidate)?)?;
        self.state = candidate;
        Ok(())
    }

    fn pending_v2(&self) -> Option<&CheckpointJournalRecordV2> {
        self.state.records.last().filter(|record| {
            matches!(
                record.stage,
                CheckpointJournalStageV2::Signed | CheckpointJournalStageV2::Submitted
            )
        })
    }

    fn append_signed_v2(
        &mut self,
        record: CheckpointJournalRecordV2,
    ) -> Result<(), PairForestCheckpointOperatorErrorV2> {
        if record.stage != CheckpointJournalStageV2::Signed
            || self
                .state
                .records
                .last()
                .is_some_and(|last| last.sequence >= record.sequence)
        {
            return Err(PairForestCheckpointOperatorErrorV2::JournalConflict);
        }
        let mut candidate = self.state.clone();
        candidate.records.push(record);
        self.replace_state_v2(candidate)
    }

    fn transition_last_v2(
        &mut self,
        sequence: u64,
        expected: CheckpointJournalStageV2,
        next: CheckpointJournalStageV2,
        finalized: Option<(FinalizedChainPointV1, [u8; 32])>,
    ) -> Result<(), PairForestCheckpointOperatorErrorV2> {
        let mut candidate = self.state.clone();
        let record = candidate
            .records
            .last_mut()
            .ok_or(PairForestCheckpointOperatorErrorV2::JournalConflict)?;
        if record.sequence != sequence || record.stage != expected {
            return Err(PairForestCheckpointOperatorErrorV2::JournalConflict);
        }
        record.stage = next;
        if let Some((point, digest)) = finalized {
            record.finalized_point = Some(point);
            record.finalized_poststate_sha256 = Some(digest);
        }
        self.replace_state_v2(candidate)
    }

    pub fn record_count_v2(&self) -> usize {
        self.state.records.len()
    }
}

#[derive(Clone, Debug)]
struct ValidatedCheckpointSnapshotV2 {
    point: FinalizedChainPointV1,
    provider_set_digest: [u8; 32],
    master: AuthenticatedForestMasterAccountV2,
    lane_sequences: [u64; POOL_V1_PAIR_FOREST_LANE_COUNT],
}

fn require_finalized_context_v2(
    commitment: SolanaRpcCommitmentV1,
    context_slot: u64,
    point: FinalizedChainPointV1,
    provider_set_digest: [u8; 32],
) -> Result<(), PairForestCheckpointOperatorErrorV2> {
    if commitment != SolanaRpcCommitmentV1::Finalized {
        return Err(PairForestCheckpointOperatorErrorV2::NotFinalized);
    }
    if context_slot < point.slot() {
        return Err(PairForestCheckpointOperatorErrorV2::ContextTooOld);
    }
    if provider_set_digest == [0u8; 32] {
        return Err(PairForestCheckpointOperatorErrorV2::ProviderMismatch);
    }
    Ok(())
}

fn validate_checkpoint_snapshot_v2(
    program_id: Pubkey,
    expected_master: Pubkey,
    snapshot: &FinalizedPairForestCheckpointSnapshotV2,
) -> Result<ValidatedCheckpointSnapshotV2, PairForestCheckpointOperatorErrorV2> {
    require_finalized_context_v2(
        snapshot.commitment,
        snapshot.context_slot,
        snapshot.point,
        snapshot.provider_set_digest,
    )?;
    if snapshot.lanes.len() != POOL_V1_PAIR_FOREST_LANE_COUNT
        || snapshot.master.owner != program_id.to_bytes()
        || snapshot.master.executable
    {
        return Err(PairForestCheckpointOperatorErrorV2::InvalidSnapshot);
    }
    let master = authenticate_forest_master_account_v2(
        program_id.to_bytes(),
        snapshot.master.address,
        &snapshot.master.data,
    )?;
    if master.address != expected_master.to_bytes()
        || master.value.initialized_lane_mask != POOL_V1_PAIR_FOREST_ALL_LANES_MASK
    {
        return Err(PairForestCheckpointOperatorErrorV2::InvalidSnapshot);
    }
    let mut decoded = Vec::with_capacity(POOL_V1_PAIR_FOREST_LANE_COUNT);
    for (index, account) in snapshot.lanes.iter().enumerate() {
        if account.owner != program_id.to_bytes() || account.executable {
            return Err(PairForestCheckpointOperatorErrorV2::InvalidSnapshot);
        }
        decoded.push(authenticate_forest_lane_account_v2(
            program_id.to_bytes(),
            master.address,
            crate::lane_forest_v2::LaneIdV2::new(index as u8)
                .map_err(|_| PairForestCheckpointOperatorErrorV2::InvalidSnapshot)?,
            account.address,
            &account.data,
        )?);
    }
    let lanes: [AuthenticatedForestLaneAccountV2; POOL_V1_PAIR_FOREST_LANE_COUNT] = decoded
        .try_into()
        .map_err(|_| PairForestCheckpointOperatorErrorV2::InvalidSnapshot)?;
    let lane_sequences = lanes.each_ref().map(|lane| lane.value.tree.next_leaf_index);
    if lane_sequences
        .iter()
        .zip(master.value.last_checkpoint_lane_sequences)
        .any(|(current, previous)| *current < previous)
    {
        return Err(PairForestCheckpointOperatorErrorV2::LaneRegression);
    }
    Ok(ValidatedCheckpointSnapshotV2 {
        point: snapshot.point,
        provider_set_digest: snapshot.provider_set_digest,
        master,
        lane_sequences,
    })
}

fn snapshot_has_progress_v2(snapshot: &ValidatedCheckpointSnapshotV2) -> bool {
    snapshot
        .lane_sequences
        .iter()
        .zip(snapshot.master.value.last_checkpoint_lane_sequences)
        .any(|(current, previous)| *current > previous)
}

fn sha256_v2(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn master_static_binding_v2(
    master: &aspis_statement::pool_v1::PoolV1PairForestMasterV1,
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"aspis:pool-v1:eight-lane-master-static:sha256:v2");
    hasher.update(master.identity.pool);
    hasher.update(master.identity.asset_mint);
    hasher.update(master.identity.token_program);
    hasher.update(master.identity.asset_id.to_le_bytes());
    hasher.update(master.identity.deployment_domain);
    hasher.update([master.verifier_policy.flags]);
    hasher.update(master.verifier_policy.registry_program);
    hasher.update(master.verifier_policy.registry_authority);
    hasher.update(master.verifier_policy.policy_binding);
    hasher.update([master.initialized_lane_mask]);
    hasher.finalize().into()
}

fn build_unsigned_checkpoint_transaction_v2(
    instruction: solana_program::instruction::Instruction,
    payer: Pubkey,
    blockhash: [u8; 32],
) -> Result<(VersionedMessage, Vec<u8>, Vec<u8>), PairForestCheckpointOperatorErrorV2> {
    let message = VersionedMessage::Legacy(legacy::Message::new_with_blockhash(
        &[instruction],
        Some(&payer),
        &Hash::new_from_array(blockhash),
    ));
    let serialized_message = bincode::serialize(&message)
        .map_err(|_| PairForestCheckpointOperatorErrorV2::SerializationFailed)?;
    let unsigned = bincode::serialize(&VersionedTransaction {
        signatures: vec![Signature::default()],
        message: message.clone(),
    })
    .map_err(|_| PairForestCheckpointOperatorErrorV2::SerializationFailed)?;
    if unsigned.len() > MAX_CHECKPOINT_TRANSACTION_BYTES_V2 {
        return Err(PairForestCheckpointOperatorErrorV2::ImageTooLarge);
    }
    Ok((message, serialized_message, unsigned))
}

fn signed_checkpoint_wire_v2(
    message: VersionedMessage,
    serialized_message: &[u8],
    payer: Pubkey,
    signature: [u8; 64],
) -> Result<Vec<u8>, PairForestCheckpointOperatorErrorV2> {
    let signature = Signature::from(signature);
    if !signature.verify(payer.as_ref(), serialized_message) {
        return Err(PairForestCheckpointOperatorErrorV2::InvalidSignature);
    }
    let wire = bincode::serialize(&VersionedTransaction {
        signatures: vec![signature],
        message,
    })
    .map_err(|_| PairForestCheckpointOperatorErrorV2::SerializationFailed)?;
    if wire.len() > MAX_CHECKPOINT_TRANSACTION_BYTES_V2 {
        return Err(PairForestCheckpointOperatorErrorV2::ImageTooLarge);
    }
    Ok(wire)
}

fn validate_finalized_confirmation_v2(
    program_id: Pubkey,
    master_address: Pubkey,
    record: &CheckpointJournalRecordV2,
    confirmation: &FinalizedCheckpointConfirmationV2,
) -> Result<[u8; 32], PairForestCheckpointOperatorErrorV2> {
    require_finalized_context_v2(
        confirmation.commitment,
        confirmation.context_slot,
        confirmation.point,
        confirmation.provider_set_digest,
    )?;
    if !confirmation.success {
        return Err(PairForestCheckpointOperatorErrorV2::FinalizedExecutionFailed);
    }
    if confirmation.transaction_signature != record.transaction_signature
        || confirmation.provider_set_digest != record.snapshot_provider_set_digest
        || confirmation.master.owner != program_id.to_bytes()
        || confirmation.checkpoint.owner != program_id.to_bytes()
        || confirmation.master.executable
        || confirmation.checkpoint.executable
    {
        return Err(PairForestCheckpointOperatorErrorV2::FinalizedStateMismatch);
    }
    let post_master = authenticate_forest_master_account_v2(
        program_id.to_bytes(),
        confirmation.master.address,
        &confirmation.master.data,
    )?;
    let checkpoint = authenticate_forest_checkpoint_account_v2(
        program_id.to_bytes(),
        master_address.to_bytes(),
        post_master.value.identity.deployment_domain,
        confirmation.checkpoint.address,
        &confirmation.checkpoint.data,
    )?;
    let expected_checkpoint =
        pool_v1_pair_forest_checkpoint_address(&program_id, &master_address, record.sequence).0;
    if post_master.address != master_address.to_bytes()
        || master_static_binding_v2(&post_master.value) != record.master_static_binding
        || checkpoint.address != expected_checkpoint.to_bytes()
        || !post_master.value.has_checkpoint
        || post_master.value.next_checkpoint_sequence != record.sequence + 1
        || checkpoint.value.checkpoint_sequence != record.sequence
        || checkpoint.value.lane_sequences != post_master.value.last_checkpoint_lane_sequences
        || checkpoint
            .value
            .lane_sequences
            .iter()
            .zip(record.lane_sequences)
            .any(|(landed, observed)| *landed < observed)
    {
        return Err(PairForestCheckpointOperatorErrorV2::FinalizedStateMismatch);
    }
    let mut hasher = Sha256::new();
    hasher.update(confirmation.master.address);
    hasher.update(&confirmation.master.data);
    hasher.update(confirmation.checkpoint.address);
    hasher.update(&confirmation.checkpoint.data);
    Ok(hasher.finalize().into())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PairForestCheckpointRunOutcomeV2 {
    NoProgress {
        finalized_point: FinalizedChainPointV1,
    },
    SubmittedAwaitingFinality {
        checkpoint_sequence: u64,
        transaction_signature: [u8; 64],
    },
    Finalized {
        checkpoint_sequence: u64,
        transaction_signature: [u8; 64],
        finalized_point: FinalizedChainPointV1,
    },
    Superseded {
        checkpoint_sequence: u64,
    },
}

fn try_finalize_pending_v2<R: PairForestCheckpointRpcV2>(
    program_id: Pubkey,
    master_address: Pubkey,
    rpc: &mut R,
    journal: &mut DurablePairForestCheckpointJournalV2,
) -> Result<Option<PairForestCheckpointRunOutcomeV2>, PairForestCheckpointOperatorErrorV2> {
    let record = match journal.pending_v2() {
        Some(record) if record.stage == CheckpointJournalStageV2::Submitted => record.clone(),
        _ => return Ok(None),
    };
    let Some(confirmation) = rpc.confirm_checkpoint_finalized_v2(record.transaction_signature)?
    else {
        return Ok(Some(
            PairForestCheckpointRunOutcomeV2::SubmittedAwaitingFinality {
                checkpoint_sequence: record.sequence,
                transaction_signature: record.transaction_signature,
            },
        ));
    };
    let poststate =
        validate_finalized_confirmation_v2(program_id, master_address, &record, &confirmation)?;
    journal.transition_last_v2(
        record.sequence,
        CheckpointJournalStageV2::Submitted,
        CheckpointJournalStageV2::Finalized,
        Some((confirmation.point, poststate)),
    )?;
    Ok(Some(PairForestCheckpointRunOutcomeV2::Finalized {
        checkpoint_sequence: record.sequence,
        transaction_signature: record.transaction_signature,
        finalized_point: confirmation.point,
    }))
}

/// Execute at most one submission. A submitted journal record is only polled;
/// a signed-but-not-submitted record is submitted byte-for-byte without
/// re-fetching a blockhash or invoking the signer again.
pub fn run_pair_forest_checkpoint_once_v2<
    R: PairForestCheckpointRpcV2,
    S: PairForestCheckpointSignerV2,
>(
    program_id: Pubkey,
    master_address: Pubkey,
    rpc: &mut R,
    signer: &mut S,
    journal: &mut DurablePairForestCheckpointJournalV2,
) -> Result<PairForestCheckpointRunOutcomeV2, PairForestCheckpointOperatorErrorV2> {
    if signer.fee_payer_v2() == Pubkey::default() {
        return Err(PairForestCheckpointOperatorErrorV2::WrongPayer);
    }
    if let Some(outcome) = try_finalize_pending_v2(program_id, master_address, rpc, journal)? {
        return Ok(outcome);
    }
    let snapshot = rpc.fetch_finalized_checkpoint_snapshot_v2(program_id, master_address)?;
    let snapshot = validate_checkpoint_snapshot_v2(program_id, master_address, &snapshot)?;

    if let Some(record) = journal.pending_v2().cloned() {
        if record.stage != CheckpointJournalStageV2::Signed {
            return Err(PairForestCheckpointOperatorErrorV2::JournalConflict);
        }
        if snapshot.master.value.next_checkpoint_sequence != record.sequence {
            journal.transition_last_v2(
                record.sequence,
                CheckpointJournalStageV2::Signed,
                CheckpointJournalStageV2::Superseded,
                None,
            )?;
            return Ok(PairForestCheckpointRunOutcomeV2::Superseded {
                checkpoint_sequence: record.sequence,
            });
        }
        let submitted = rpc.submit_checkpoint_transaction_v2(&record.signed_wire)?;
        if submitted != record.transaction_signature {
            return Err(PairForestCheckpointOperatorErrorV2::SubmissionMismatch);
        }
        journal.transition_last_v2(
            record.sequence,
            CheckpointJournalStageV2::Signed,
            CheckpointJournalStageV2::Submitted,
            None,
        )?;
        return try_finalize_pending_v2(program_id, master_address, rpc, journal)?
            .ok_or(PairForestCheckpointOperatorErrorV2::JournalConflict);
    }

    if !snapshot_has_progress_v2(&snapshot) {
        return Ok(PairForestCheckpointRunOutcomeV2::NoProgress {
            finalized_point: snapshot.point,
        });
    }
    let payer = signer.fee_payer_v2();
    let instruction =
        build_pair_forest_checkpoint_instruction_v2(program_id, payer, &snapshot.master.value)?;
    let instruction_sha256 = sha256_v2(&instruction.data);
    let blockhash = rpc.fetch_finalized_blockhash_v2()?;
    if blockhash.commitment != SolanaRpcCommitmentV1::Finalized {
        return Err(PairForestCheckpointOperatorErrorV2::NotFinalized);
    }
    if blockhash.context_slot < snapshot.point.slot()
        || blockhash.provider_set_digest != snapshot.provider_set_digest
    {
        return Err(PairForestCheckpointOperatorErrorV2::ProviderMismatch);
    }
    if blockhash.block_height > blockhash.last_valid_block_height {
        return Err(PairForestCheckpointOperatorErrorV2::BlockhashExpired);
    }
    let (message, serialized_message, unsigned_wire) =
        build_unsigned_checkpoint_transaction_v2(instruction, payer, blockhash.blockhash)?;
    let message_sha256 = sha256_v2(&serialized_message);
    let simulation = rpc.simulate_checkpoint_transaction_v2(&unsigned_wire)?;
    if simulation.commitment != SolanaRpcCommitmentV1::Finalized
        || simulation.context_slot < blockhash.context_slot
        || simulation.provider_set_digest != snapshot.provider_set_digest
        || simulation.message_sha256 != message_sha256
        || !simulation.success
    {
        return Err(PairForestCheckpointOperatorErrorV2::SimulationFailed);
    }
    let signature = signer.sign_checkpoint_message_v2(&serialized_message)?;
    let signed_wire = signed_checkpoint_wire_v2(message, &serialized_message, payer, signature)?;
    let sequence = snapshot.master.value.next_checkpoint_sequence;
    journal.append_signed_v2(CheckpointJournalRecordV2 {
        sequence,
        snapshot_point: snapshot.point,
        snapshot_provider_set_digest: snapshot.provider_set_digest,
        lane_sequences: snapshot.lane_sequences,
        master_static_binding: master_static_binding_v2(&snapshot.master.value),
        instruction_sha256,
        message_sha256,
        recent_blockhash: blockhash.blockhash,
        last_valid_block_height: blockhash.last_valid_block_height,
        transaction_signature: signature,
        signed_wire: signed_wire.clone(),
        stage: CheckpointJournalStageV2::Signed,
        finalized_point: None,
        finalized_poststate_sha256: None,
    })?;
    let submitted = rpc.submit_checkpoint_transaction_v2(&signed_wire)?;
    if submitted != signature {
        return Err(PairForestCheckpointOperatorErrorV2::SubmissionMismatch);
    }
    journal.transition_last_v2(
        sequence,
        CheckpointJournalStageV2::Signed,
        CheckpointJournalStageV2::Submitted,
        None,
    )?;
    try_finalize_pending_v2(program_id, master_address, rpc, journal)?
        .ok_or(PairForestCheckpointOperatorErrorV2::JournalConflict)
}

#[cfg(test)]
mod tests {
    use std::{cell::RefCell, rc::Rc};

    use super::*;
    use aspis_core::field::M31;
    use aspis_pool::{
        pool_v1_pair_forest_global_root_v1, pool_v1_pair_forest_lane_address,
        pool_v1_pair_forest_master_address, POOL_V1_PAIR_EMPTY_ROOTS,
    };
    use aspis_statement::pool_v1::{
        encode_pool_v1_pair_forest_checkpoint_v1, encode_pool_v1_pair_forest_lane_state_v1,
        encode_pool_v1_pair_forest_master_v1, plan_pool_v1_pair_forest_checkpoint_v1,
        IncrementalMerkleTreeV1, PoolIdentityV1, PoolV1PairForestLaneStateV1,
        PoolV1PairForestMasterV1, VerifierPolicyV1, POOL_V1_PAIR_TREE_DEPTH,
    };
    use solana_keypair::Keypair;
    use solana_signer::Signer as _;

    fn key(seed: u8) -> Pubkey {
        Pubkey::new_from_array([seed; 32])
    }

    fn point(slot: u64) -> FinalizedChainPointV1 {
        FinalizedChainPointV1::new(slot, [slot as u8; 32]).unwrap()
    }

    fn temp_path() -> std::path::PathBuf {
        std::env::temp_dir().join(format!(
            "aspis-eight-lane-checkpoint-{}-{}.bin",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ))
    }

    fn cleanup(path: &Path) {
        let lock = path.with_file_name(format!(
            "{}.lock",
            path.file_name().unwrap().to_string_lossy()
        ));
        std::fs::remove_file(path).unwrap();
        std::fs::remove_file(lock).unwrap();
    }

    #[derive(Clone)]
    struct Fixture {
        program: Pubkey,
        master: Pubkey,
        pre: FinalizedPairForestCheckpointSnapshotV2,
        post: FinalizedPairForestCheckpointSnapshotV2,
        confirmation: FinalizedCheckpointConfirmationV2,
    }

    fn fixture(progress: bool) -> Fixture {
        let program = key(1);
        let mint = key(2);
        let master_address = pool_v1_pair_forest_master_address(&program, &mint).0;
        let master = PoolV1PairForestMasterV1 {
            identity: PoolIdentityV1 {
                pool: master_address.to_bytes(),
                asset_mint: mint.to_bytes(),
                token_program: aspis_pool::LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
                asset_id: M31(3),
                deployment_domain: [4; 32],
            },
            verifier_policy: VerifierPolicyV1 {
                flags: 0,
                registry_program: [5; 32],
                registry_authority: [6; 32],
                policy_binding: [7; 32],
            },
            initialized_lane_mask: POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
            has_checkpoint: false,
            next_checkpoint_sequence: 0,
            last_checkpoint_lane_sequences: [0; 8],
        };
        let mut lanes = core::array::from_fn(|lane_id| PoolV1PairForestLaneStateV1 {
            master: master_address.to_bytes(),
            lane_id: lane_id as u8,
            tree: IncrementalMerkleTreeV1 {
                next_leaf_index: 0,
                root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
                frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
            },
        });
        if progress {
            lanes[0].tree = lanes[0]
                .tree
                .append_one_with_empty_roots(
                    core::array::from_fn(|index| M31(100 + index as u32)),
                    &POOL_V1_PAIR_EMPTY_ROOTS,
                )
                .unwrap()
                .0;
        }
        let master_account = FinalizedForestAccountV2 {
            address: master_address.to_bytes(),
            owner: program.to_bytes(),
            executable: false,
            data: encode_pool_v1_pair_forest_master_v1(&master)
                .unwrap()
                .to_vec(),
        };
        let lane_accounts = lanes
            .iter()
            .enumerate()
            .map(|(lane_id, lane)| FinalizedForestAccountV2 {
                address: pool_v1_pair_forest_lane_address(&program, &master_address, lane_id as u8)
                    .unwrap()
                    .0
                    .to_bytes(),
                owner: program.to_bytes(),
                executable: false,
                data: encode_pool_v1_pair_forest_lane_state_v1(lane, &POOL_V1_PAIR_EMPTY_ROOTS)
                    .unwrap()
                    .to_vec(),
            })
            .collect::<Vec<_>>();
        let provider_set_digest = [8; 32];
        let pre = FinalizedPairForestCheckpointSnapshotV2 {
            point: point(10),
            context_slot: 10,
            commitment: SolanaRpcCommitmentV1::Finalized,
            provider_set_digest,
            master: master_account,
            lanes: lane_accounts.clone(),
        };
        let global_root =
            pool_v1_pair_forest_global_root_v1(&lanes.each_ref().map(|lane| lane.tree.root));
        let planned = plan_pool_v1_pair_forest_checkpoint_v1(&master, &lanes, global_root).unwrap();
        let checkpoint_address = pool_v1_pair_forest_checkpoint_address(
            &program,
            &master_address,
            planned.checkpoint.checkpoint_sequence,
        )
        .0;
        let post_master = FinalizedForestAccountV2 {
            address: master_address.to_bytes(),
            owner: program.to_bytes(),
            executable: false,
            data: encode_pool_v1_pair_forest_master_v1(&planned.next_master)
                .unwrap()
                .to_vec(),
        };
        let post = FinalizedPairForestCheckpointSnapshotV2 {
            point: point(11),
            context_slot: 11,
            commitment: SolanaRpcCommitmentV1::Finalized,
            provider_set_digest,
            master: post_master.clone(),
            lanes: lane_accounts,
        };
        let confirmation = FinalizedCheckpointConfirmationV2 {
            point: point(11),
            context_slot: 11,
            commitment: SolanaRpcCommitmentV1::Finalized,
            provider_set_digest,
            transaction_signature: [0; 64],
            success: true,
            master: post_master,
            checkpoint: FinalizedForestAccountV2 {
                address: checkpoint_address.to_bytes(),
                owner: program.to_bytes(),
                executable: false,
                data: encode_pool_v1_pair_forest_checkpoint_v1(&planned.checkpoint)
                    .unwrap()
                    .to_vec(),
            },
        };
        Fixture {
            program,
            master: master_address,
            pre,
            post,
            confirmation,
        }
    }

    struct MockSigner {
        keypair: Keypair,
        operations: Rc<RefCell<Vec<&'static str>>>,
        calls: usize,
    }

    impl MockSigner {
        fn new(operations: Rc<RefCell<Vec<&'static str>>>) -> Self {
            Self {
                keypair: Keypair::new(),
                operations,
                calls: 0,
            }
        }
    }

    impl PairForestCheckpointSignerV2 for MockSigner {
        fn fee_payer_v2(&self) -> Pubkey {
            self.keypair.pubkey()
        }

        fn sign_checkpoint_message_v2(
            &mut self,
            serialized_message: &[u8],
        ) -> Result<[u8; 64], PairForestCheckpointOperatorErrorV2> {
            self.operations.borrow_mut().push("sign");
            self.calls += 1;
            Ok(self.keypair.sign_message(serialized_message).into())
        }
    }

    struct MockRpc {
        snapshot: FinalizedPairForestCheckpointSnapshotV2,
        post_snapshot: FinalizedPairForestCheckpointSnapshotV2,
        confirmation: FinalizedCheckpointConfirmationV2,
        operations: Rc<RefCell<Vec<&'static str>>>,
        fail_submit_once: bool,
        confirmation_available: bool,
        submit_calls: usize,
        simulation_calls: usize,
    }

    impl MockRpc {
        fn new(fixture: &Fixture, operations: Rc<RefCell<Vec<&'static str>>>) -> Self {
            Self {
                snapshot: fixture.pre.clone(),
                post_snapshot: fixture.post.clone(),
                confirmation: fixture.confirmation.clone(),
                operations,
                fail_submit_once: false,
                confirmation_available: true,
                submit_calls: 0,
                simulation_calls: 0,
            }
        }
    }

    impl PairForestCheckpointRpcV2 for MockRpc {
        fn fetch_finalized_checkpoint_snapshot_v2(
            &mut self,
            _program_id: Pubkey,
            _master: Pubkey,
        ) -> Result<FinalizedPairForestCheckpointSnapshotV2, PairForestCheckpointOperatorErrorV2>
        {
            self.operations.borrow_mut().push("snapshot");
            Ok(self.snapshot.clone())
        }

        fn fetch_finalized_blockhash_v2(
            &mut self,
        ) -> Result<FinalizedCheckpointBlockhashV2, PairForestCheckpointOperatorErrorV2> {
            self.operations.borrow_mut().push("blockhash");
            Ok(FinalizedCheckpointBlockhashV2 {
                context_slot: self.snapshot.context_slot,
                block_height: 100,
                last_valid_block_height: 200,
                blockhash: [9; 32],
                commitment: SolanaRpcCommitmentV1::Finalized,
                provider_set_digest: self.snapshot.provider_set_digest,
            })
        }

        fn simulate_checkpoint_transaction_v2(
            &mut self,
            unsigned_transaction_wire: &[u8],
        ) -> Result<CheckpointSimulationResultV2, PairForestCheckpointOperatorErrorV2> {
            self.operations.borrow_mut().push("simulate");
            self.simulation_calls += 1;
            let transaction: VersionedTransaction =
                bincode::deserialize(unsigned_transaction_wire).unwrap();
            Ok(CheckpointSimulationResultV2 {
                context_slot: self.snapshot.context_slot,
                commitment: SolanaRpcCommitmentV1::Finalized,
                provider_set_digest: self.snapshot.provider_set_digest,
                message_sha256: sha256_v2(&bincode::serialize(&transaction.message).unwrap()),
                success: true,
            })
        }

        fn submit_checkpoint_transaction_v2(
            &mut self,
            signed_transaction_wire: &[u8],
        ) -> Result<[u8; 64], PairForestCheckpointOperatorErrorV2> {
            self.operations.borrow_mut().push("submit");
            self.submit_calls += 1;
            if self.fail_submit_once {
                self.fail_submit_once = false;
                return Err(PairForestCheckpointOperatorErrorV2::RpcFailed);
            }
            let transaction: VersionedTransaction =
                bincode::deserialize(signed_transaction_wire).unwrap();
            Ok(transaction.signatures[0].as_ref().try_into().unwrap())
        }

        fn confirm_checkpoint_finalized_v2(
            &mut self,
            transaction_signature: [u8; 64],
        ) -> Result<Option<FinalizedCheckpointConfirmationV2>, PairForestCheckpointOperatorErrorV2>
        {
            self.operations.borrow_mut().push("confirm");
            if !self.confirmation_available {
                return Ok(None);
            }
            let mut confirmation = self.confirmation.clone();
            confirmation.transaction_signature = transaction_signature;
            self.snapshot = self.post_snapshot.clone();
            Ok(Some(confirmation))
        }
    }

    #[test]
    fn operator_simulates_before_signing_submits_once_and_reopens_finalized_journal() {
        let fixture = fixture(true);
        let operations = Rc::new(RefCell::new(Vec::new()));
        let mut rpc = MockRpc::new(&fixture, operations.clone());
        let mut signer = MockSigner::new(operations.clone());
        let path = temp_path();
        {
            let mut journal = DurablePairForestCheckpointJournalV2::open_or_create_v2(
                &path,
                fixture.program,
                fixture.master,
            )
            .unwrap();
            assert!(matches!(
                run_pair_forest_checkpoint_once_v2(
                    fixture.program,
                    fixture.master,
                    &mut rpc,
                    &mut signer,
                    &mut journal
                )
                .unwrap(),
                PairForestCheckpointRunOutcomeV2::Finalized {
                    checkpoint_sequence: 0,
                    ..
                }
            ));
            assert_eq!(journal.record_count_v2(), 1);
        }
        assert_eq!(
            &*operations.borrow(),
            &[
                "snapshot",
                "blockhash",
                "simulate",
                "sign",
                "submit",
                "confirm"
            ]
        );
        {
            let mut reopened = DurablePairForestCheckpointJournalV2::open_or_create_v2(
                &path,
                fixture.program,
                fixture.master,
            )
            .unwrap();
            assert!(matches!(
                run_pair_forest_checkpoint_once_v2(
                    fixture.program,
                    fixture.master,
                    &mut rpc,
                    &mut signer,
                    &mut reopened
                )
                .unwrap(),
                PairForestCheckpointRunOutcomeV2::NoProgress { .. }
            ));
        }
        assert_eq!(signer.calls, 1);
        assert_eq!(rpc.submit_calls, 1);
        cleanup(&path);
    }

    #[test]
    fn signed_wire_survives_submit_failure_and_restart_without_resigning() {
        let fixture = fixture(true);
        let operations = Rc::new(RefCell::new(Vec::new()));
        let mut rpc = MockRpc::new(&fixture, operations.clone());
        rpc.fail_submit_once = true;
        let mut signer = MockSigner::new(operations);
        let path = temp_path();
        {
            let mut journal = DurablePairForestCheckpointJournalV2::open_or_create_v2(
                &path,
                fixture.program,
                fixture.master,
            )
            .unwrap();
            assert_eq!(
                run_pair_forest_checkpoint_once_v2(
                    fixture.program,
                    fixture.master,
                    &mut rpc,
                    &mut signer,
                    &mut journal
                ),
                Err(PairForestCheckpointOperatorErrorV2::RpcFailed)
            );
        }
        {
            let mut reopened = DurablePairForestCheckpointJournalV2::open_or_create_v2(
                &path,
                fixture.program,
                fixture.master,
            )
            .unwrap();
            assert!(matches!(
                run_pair_forest_checkpoint_once_v2(
                    fixture.program,
                    fixture.master,
                    &mut rpc,
                    &mut signer,
                    &mut reopened
                )
                .unwrap(),
                PairForestCheckpointRunOutcomeV2::Finalized { .. }
            ));
        }
        assert_eq!(signer.calls, 1);
        assert_eq!(rpc.simulation_calls, 1);
        assert_eq!(rpc.submit_calls, 2);
        cleanup(&path);
    }

    #[test]
    fn submitted_is_only_polled_and_untrusted_snapshots_never_reach_signer() {
        let base = fixture(true);
        let operations = Rc::new(RefCell::new(Vec::new()));
        let mut rpc = MockRpc::new(&base, operations.clone());
        rpc.confirmation_available = false;
        let mut signer = MockSigner::new(operations);
        let path = temp_path();
        let mut journal = DurablePairForestCheckpointJournalV2::open_or_create_v2(
            &path,
            base.program,
            base.master,
        )
        .unwrap();
        assert!(matches!(
            run_pair_forest_checkpoint_once_v2(
                base.program,
                base.master,
                &mut rpc,
                &mut signer,
                &mut journal
            )
            .unwrap(),
            PairForestCheckpointRunOutcomeV2::SubmittedAwaitingFinality { .. }
        ));
        rpc.confirmation_available = true;
        assert!(matches!(
            run_pair_forest_checkpoint_once_v2(
                base.program,
                base.master,
                &mut rpc,
                &mut signer,
                &mut journal
            )
            .unwrap(),
            PairForestCheckpointRunOutcomeV2::Finalized { .. }
        ));
        assert_eq!(rpc.submit_calls, 1);
        drop(journal);
        cleanup(&path);

        let mut forged = fixture(true);
        forged.pre.lanes[3].owner = [0x55; 32];
        let operations = Rc::new(RefCell::new(Vec::new()));
        let mut forged_rpc = MockRpc::new(&forged, operations.clone());
        let mut forged_signer = MockSigner::new(operations);
        let forged_path = temp_path();
        let mut forged_journal = DurablePairForestCheckpointJournalV2::open_or_create_v2(
            &forged_path,
            forged.program,
            forged.master,
        )
        .unwrap();
        assert_eq!(
            run_pair_forest_checkpoint_once_v2(
                forged.program,
                forged.master,
                &mut forged_rpc,
                &mut forged_signer,
                &mut forged_journal
            ),
            Err(PairForestCheckpointOperatorErrorV2::InvalidSnapshot)
        );
        assert_eq!(forged_journal.record_count_v2(), 0);
        assert_eq!(forged_signer.calls, 0);
        cleanup(&forged_path);
    }

    #[test]
    fn no_progress_skips_blockhash_simulation_signing_and_submission() {
        let fixture = fixture(false);
        let operations = Rc::new(RefCell::new(Vec::new()));
        let mut rpc = MockRpc::new(&fixture, operations.clone());
        let mut signer = MockSigner::new(operations);
        let path = temp_path();
        let mut journal = DurablePairForestCheckpointJournalV2::open_or_create_v2(
            &path,
            fixture.program,
            fixture.master,
        )
        .unwrap();
        assert!(matches!(
            run_pair_forest_checkpoint_once_v2(
                fixture.program,
                fixture.master,
                &mut rpc,
                &mut signer,
                &mut journal
            )
            .unwrap(),
            PairForestCheckpointRunOutcomeV2::NoProgress { .. }
        ));
        assert_eq!(signer.calls, 0);
        assert_eq!(rpc.simulation_calls, 0);
        assert_eq!(rpc.submit_calls, 0);
        assert_eq!(journal.record_count_v2(), 0);
        cleanup(&path);
    }
}
