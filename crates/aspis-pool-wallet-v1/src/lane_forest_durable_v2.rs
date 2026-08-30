//! Durable, production-inactive wallet/indexer plumbing for the eight-lane
//! pair forest.
//!
//! The on-chain formats and PDA seeds are not reproduced here. Account input
//! is decoded with the committed statement codecs and authenticated with the
//! committed Pool PDA helpers. The wallet-only event and durable-state images
//! are explicitly versioned and checksummed. Nothing in this module is wired
//! into Pool instruction dispatch.

use std::{collections::HashSet, path::Path};

use aspis_core::field::M31;
use aspis_pool::{
    pool_v1_pair_forest_checkpoint_address, pool_v1_pair_forest_lane_address,
    pool_v1_pair_forest_lane_root_page_address, pool_v1_pair_forest_master_address,
    POOL_V1_PAIR_EMPTY_ROOTS,
};
use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{
        decode_pool_v1_pair_forest_checkpoint_v1, decode_pool_v1_pair_forest_lane_state_v1,
        decode_pool_v1_pair_forest_master_v1, encode_pool_v1_pair_forest_checkpoint_v1,
        encode_pool_v1_pair_forest_lane_state_v1, encode_pool_v1_pair_forest_master_v1,
        pool_v1_tree_parent, root_history_location, IncrementalMerkleTreeV1,
        PoolV1PairForestAccountErrorV1, PoolV1PairForestCheckpointV1, PoolV1PairForestLaneStateV1,
        PoolV1PairForestMasterV1, PoolV1PairLeafErrorV1, PoolV1PairLeafWitnessV1, PoolV1TreeError,
        POOL_V1_PAIR_CAPACITY, POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
        POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES,
        POOL_V1_PAIR_FOREST_LANE_COUNT, POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES,
        POOL_V1_TREE_DEPTH,
    },
    Digest,
};
use bincode::Options;
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};
use solana_program::pubkey::Pubkey;

use crate::{
    durable_state::{AtomicStateFileV1, DurableStateErrorV1},
    lane_forest_v2::{lane_forest_global_root_v2, LaneIdV2, PairSlotV2, POOL_V1_LANE_COUNT_V2},
    scan_note_v1,
    scan_state::{DepositEventIdV1, FinalizedChainPointV1},
    NoteContextV1, NoteOpeningV1, PoolV1WalletError, ScanResultV1, ViewingSecretKeyV1,
    POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES,
};

pub const LANE_FOREST_EVENT_MAGIC_V2: [u8; 4] = *b"ASE8";
pub const LANE_FOREST_EVENT_VERSION_V2: u8 = 2;
pub const LANE_FOREST_EVENT_HEADER_BYTES_V2: usize = 1184;
pub const LANE_FOREST_EVENT_DEPOSIT: u8 = 1;
pub const LANE_FOREST_EVENT_PRIVATE_TRANSFER: u8 = 2;
pub const LANE_FOREST_EVENT_WITHDRAWAL: u8 = 3;

pub const LANE_FOREST_DURABLE_MAGIC_V2: [u8; 4] = *b"ASD8";
pub const LANE_FOREST_DURABLE_VERSION_V2: u8 = 2;
pub const LANE_FOREST_DURABLE_HEADER_BYTES_V2: usize = 56;
const LANE_FOREST_DURABLE_CHECKSUM_OFFSET_V2: usize = 24;
const LANE_FOREST_DURABLE_CHECKSUM_DOMAIN_V2: &[u8] =
    b"aspis:pool-v1:eight-lane-wallet-durable:sha256:v2";
const MAX_LANE_FOREST_DURABLE_BYTES_V2: usize = 64 * 1024 * 1024;
const MAX_LANE_FOREST_EVENTS_V2: usize = 1_048_576;
const MAX_LANE_FOREST_SNAPSHOTS_V2: usize = 1_000_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LaneForestDurableErrorV2 {
    Account(PoolV1PairForestAccountErrorV1),
    Tree(PoolV1TreeError),
    PairLeaf(PoolV1PairLeafErrorV1),
    Wallet(PoolV1WalletError),
    Durable(DurableStateErrorV1),
    WrongLength,
    WrongMagic,
    WrongVersion,
    NonZeroReserved,
    ChecksumMismatch,
    CountOverflow,
    InvalidProgram,
    InvalidMasterAddress,
    InvalidLaneAddress,
    InvalidCheckpointAddress,
    MasterMismatch,
    DeploymentMismatch,
    LaneAlias,
    LaneOrderMismatch,
    LaneStateMismatch,
    LaneSequenceMismatch,
    GlobalRootMismatch,
    CheckpointSequenceMismatch,
    CheckpointNoProgress,
    InvalidEvent,
    DuplicateEvent,
    EventOutsideFinalizedOrder,
    WrongRoutedLane,
    LegacyPerOutputAppend,
    WitnessMismatch,
    InvalidRollback,
    InvalidDurableImage,
    IdentityMismatch,
}

impl From<PoolV1PairForestAccountErrorV1> for LaneForestDurableErrorV2 {
    fn from(error: PoolV1PairForestAccountErrorV1) -> Self {
        Self::Account(error)
    }
}

impl From<PoolV1TreeError> for LaneForestDurableErrorV2 {
    fn from(error: PoolV1TreeError) -> Self {
        Self::Tree(error)
    }
}

impl From<PoolV1PairLeafErrorV1> for LaneForestDurableErrorV2 {
    fn from(error: PoolV1PairLeafErrorV1) -> Self {
        Self::PairLeaf(error)
    }
}

impl From<PoolV1WalletError> for LaneForestDurableErrorV2 {
    fn from(error: PoolV1WalletError) -> Self {
        Self::Wallet(error)
    }
}

impl From<DurableStateErrorV1> for LaneForestDurableErrorV2 {
    fn from(error: DurableStateErrorV1) -> Self {
        Self::Durable(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuthenticatedForestMasterAccountV2 {
    pub address: [u8; 32],
    pub bump: u8,
    pub value: PoolV1PairForestMasterV1,
    pub image: [u8; POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuthenticatedForestLaneAccountV2 {
    pub address: [u8; 32],
    pub bump: u8,
    pub value: PoolV1PairForestLaneStateV1,
    pub image: [u8; POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuthenticatedForestCheckpointAccountV2 {
    pub address: [u8; 32],
    pub bump: u8,
    pub value: PoolV1PairForestCheckpointV1,
    pub image: [u8; POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LaneRootPageCursorV2 {
    pub lane_id: LaneIdV2,
    pub root_sequence: u64,
    pub page_number: u64,
    pub address: [u8; 32],
    pub bump: u8,
}

pub fn authenticate_forest_master_account_v2(
    program_id: [u8; 32],
    address: [u8; 32],
    bytes: &[u8],
) -> Result<AuthenticatedForestMasterAccountV2, LaneForestDurableErrorV2> {
    if program_id == [0u8; 32] {
        return Err(LaneForestDurableErrorV2::InvalidProgram);
    }
    let value = decode_pool_v1_pair_forest_master_v1(bytes)?;
    let program = Pubkey::new_from_array(program_id);
    let mint = Pubkey::new_from_array(value.identity.asset_mint);
    let (expected, bump) = pool_v1_pair_forest_master_address(&program, &mint);
    if address != expected.to_bytes() || value.identity.pool != address {
        return Err(LaneForestDurableErrorV2::InvalidMasterAddress);
    }
    let image = encode_pool_v1_pair_forest_master_v1(&value)?;
    if bytes != image {
        return Err(LaneForestDurableErrorV2::InvalidDurableImage);
    }
    Ok(AuthenticatedForestMasterAccountV2 {
        address,
        bump,
        value,
        image,
    })
}

pub fn authenticate_forest_lane_account_v2(
    program_id: [u8; 32],
    master: [u8; 32],
    expected_lane: LaneIdV2,
    address: [u8; 32],
    bytes: &[u8],
) -> Result<AuthenticatedForestLaneAccountV2, LaneForestDurableErrorV2> {
    let program = Pubkey::new_from_array(program_id);
    let master_key = Pubkey::new_from_array(master);
    let (expected, bump) =
        pool_v1_pair_forest_lane_address(&program, &master_key, expected_lane.as_u8())
            .map_err(|_| LaneForestDurableErrorV2::InvalidLaneAddress)?;
    if expected.to_bytes() != address {
        return Err(LaneForestDurableErrorV2::InvalidLaneAddress);
    }
    let value = decode_pool_v1_pair_forest_lane_state_v1(bytes, &POOL_V1_PAIR_EMPTY_ROOTS)?;
    if value.master != master || value.lane_id != expected_lane.as_u8() {
        return Err(LaneForestDurableErrorV2::MasterMismatch);
    }
    let image = encode_pool_v1_pair_forest_lane_state_v1(&value, &POOL_V1_PAIR_EMPTY_ROOTS)?;
    if bytes != image {
        return Err(LaneForestDurableErrorV2::InvalidDurableImage);
    }
    Ok(AuthenticatedForestLaneAccountV2 {
        address,
        bump,
        value,
        image,
    })
}

pub fn authenticate_forest_checkpoint_account_v2(
    program_id: [u8; 32],
    master: [u8; 32],
    deployment_domain: [u8; 32],
    address: [u8; 32],
    bytes: &[u8],
) -> Result<AuthenticatedForestCheckpointAccountV2, LaneForestDurableErrorV2> {
    let value = decode_pool_v1_pair_forest_checkpoint_v1(bytes)?;
    if value.master != master {
        return Err(LaneForestDurableErrorV2::MasterMismatch);
    }
    if value.deployment_domain != deployment_domain {
        return Err(LaneForestDurableErrorV2::DeploymentMismatch);
    }
    let program = Pubkey::new_from_array(program_id);
    let master_key = Pubkey::new_from_array(master);
    let (expected, bump) =
        pool_v1_pair_forest_checkpoint_address(&program, &master_key, value.checkpoint_sequence);
    if expected.to_bytes() != address {
        return Err(LaneForestDurableErrorV2::InvalidCheckpointAddress);
    }
    let image = encode_pool_v1_pair_forest_checkpoint_v1(&value)?;
    if bytes != image {
        return Err(LaneForestDurableErrorV2::InvalidDurableImage);
    }
    Ok(AuthenticatedForestCheckpointAccountV2 {
        address,
        bump,
        value,
        image,
    })
}

pub fn canonical_lane_root_page_cursor_v2(
    program_id: [u8; 32],
    master: [u8; 32],
    lane_id: LaneIdV2,
    root_sequence: u64,
) -> Result<LaneRootPageCursorV2, LaneForestDurableErrorV2> {
    let page_number = root_history_location(root_sequence).page_number;
    let (address, bump) = pool_v1_pair_forest_lane_root_page_address(
        &Pubkey::new_from_array(program_id),
        &Pubkey::new_from_array(master),
        lane_id.as_u8(),
        page_number,
    )
    .map_err(|_| LaneForestDurableErrorV2::InvalidLaneAddress)?;
    Ok(LaneRootPageCursorV2 {
        lane_id,
        root_sequence,
        page_number,
        address: address.to_bytes(),
        bump,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForestFinalizedAppendKindV2 {
    Deposit {
        event_id: DepositEventIdV1,
        commitment: [u8; 32],
        encrypted_note: Option<[u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES]>,
    },
    PrivateTransfer {
        recipient_event_id: DepositEventIdV1,
        change_event_id: DepositEventIdV1,
        nullifier: [u8; 32],
        recipient_commitment: [u8; 32],
        change_commitment: [u8; 32],
        recipient_encrypted_note: Option<[u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES]>,
        change_encrypted_note: Option<[u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES]>,
    },
    Withdrawal {
        event_id: DepositEventIdV1,
        nullifier: [u8; 32],
        change_commitment: [u8; 32],
        destination_token_account: [u8; 32],
        amount: u32,
        encrypted_note: Option<[u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES]>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForestFinalizedAppendEventV2 {
    pub master: [u8; 32],
    pub lane_id: LaneIdV2,
    pub pair_leaf_index: u64,
    pub root_sequence: u64,
    pub after_lane_address: [u8; 32],
    pub after_lane_image: [u8; POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES],
    pub kind: ForestFinalizedAppendKindV2,
}

impl ForestFinalizedAppendEventV2 {
    pub fn point(&self) -> FinalizedChainPointV1 {
        match self.kind {
            ForestFinalizedAppendKindV2::Deposit { event_id, .. } => event_id.point(),
            ForestFinalizedAppendKindV2::PrivateTransfer {
                recipient_event_id, ..
            } => recipient_event_id.point(),
            ForestFinalizedAppendKindV2::Withdrawal { event_id, .. } => event_id.point(),
        }
    }

    pub(crate) fn event_ids(&self) -> (DepositEventIdV1, Option<DepositEventIdV1>) {
        match self.kind {
            ForestFinalizedAppendKindV2::Deposit { event_id, .. } => (event_id, None),
            ForestFinalizedAppendKindV2::PrivateTransfer {
                recipient_event_id,
                change_event_id,
                ..
            } => (recipient_event_id, Some(change_event_id)),
            ForestFinalizedAppendKindV2::Withdrawal { event_id, .. } => (event_id, None),
        }
    }
}

fn encode_event_id_v2(event: DepositEventIdV1) -> [u8; 108] {
    let mut output = [0u8; 108];
    output[..8].copy_from_slice(&event.point().slot().to_le_bytes());
    output[8..40].copy_from_slice(event.point().block_hash());
    output[40..104].copy_from_slice(event.transaction_signature());
    output[104..106].copy_from_slice(&event.instruction_index().to_le_bytes());
    output[106..108].copy_from_slice(&event.event_index().to_le_bytes());
    output
}

fn decode_event_id_v2(bytes: &[u8]) -> Result<DepositEventIdV1, LaneForestDurableErrorV2> {
    if bytes.len() != 108 {
        return Err(LaneForestDurableErrorV2::WrongLength);
    }
    let point = FinalizedChainPointV1::new(
        u64::from_le_bytes(bytes[..8].try_into().unwrap()),
        bytes[8..40].try_into().unwrap(),
    )
    .map_err(|_| LaneForestDurableErrorV2::InvalidEvent)?;
    DepositEventIdV1::new(
        point,
        bytes[40..104].try_into().unwrap(),
        u16::from_le_bytes(bytes[104..106].try_into().unwrap()),
        u16::from_le_bytes(bytes[106..108].try_into().unwrap()),
    )
    .map_err(|_| LaneForestDurableErrorV2::InvalidEvent)
}

fn same_transfer_event_v2(first: DepositEventIdV1, second: DepositEventIdV1) -> bool {
    first.point() == second.point()
        && first.transaction_signature() == second.transaction_signature()
        && first.instruction_index() == second.instruction_index()
        && first
            .event_index()
            .checked_add(1)
            .is_some_and(|next| next == second.event_index())
}

fn validate_forest_append_event_semantics_v2(
    event: &ForestFinalizedAppendEventV2,
) -> Result<PoolV1PairForestLaneStateV1, LaneForestDurableErrorV2> {
    if event.master == [0u8; 32]
        || event.after_lane_address == [0u8; 32]
        || event.pair_leaf_index >= POOL_V1_PAIR_CAPACITY
        || event.root_sequence != event.pair_leaf_index + 1
    {
        return Err(LaneForestDurableErrorV2::InvalidEvent);
    }
    let after = decode_pool_v1_pair_forest_lane_state_v1(
        &event.after_lane_image,
        &POOL_V1_PAIR_EMPTY_ROOTS,
    )
    .map_err(|_| LaneForestDurableErrorV2::InvalidEvent)?;
    if after.master != event.master
        || after.lane_id != event.lane_id.as_u8()
        || after.tree.next_leaf_index != event.root_sequence
        || encode_pool_v1_pair_forest_lane_state_v1(&after, &POOL_V1_PAIR_EMPTY_ROOTS)
            .map_err(|_| LaneForestDurableErrorV2::InvalidEvent)?
            != event.after_lane_image
    {
        return Err(LaneForestDurableErrorV2::InvalidEvent);
    }
    let route_digest = match &event.kind {
        ForestFinalizedAppendKindV2::Deposit { commitment, .. } => commitment,
        ForestFinalizedAppendKindV2::PrivateTransfer { nullifier, .. }
        | ForestFinalizedAppendKindV2::Withdrawal { nullifier, .. } => nullifier,
    };
    let route_digest = decode_digest_canonical(route_digest)
        .map_err(|_| LaneForestDurableErrorV2::InvalidEvent)?;
    let routed_lane = LaneIdV2::new(encode_digest_canonical(&route_digest)[0] & 7)
        .map_err(|_| LaneForestDurableErrorV2::WrongRoutedLane)?;
    if routed_lane != event.lane_id {
        return Err(LaneForestDurableErrorV2::WrongRoutedLane);
    }
    Ok(after)
}

pub fn encode_forest_finalized_append_event_v2(
    event: &ForestFinalizedAppendEventV2,
) -> Result<Vec<u8>, LaneForestDurableErrorV2> {
    validate_forest_append_event_semantics_v2(event)?;
    let (
        kind,
        first_id,
        second_id,
        nullifier,
        first_commitment,
        second_commitment,
        first_payload,
        second_payload,
    ) = match &event.kind {
        ForestFinalizedAppendKindV2::Deposit {
            event_id,
            commitment,
            encrypted_note,
        } => (
            LANE_FOREST_EVENT_DEPOSIT,
            *event_id,
            None,
            [0u8; 32],
            *commitment,
            [0u8; 32],
            encrypted_note.as_ref(),
            None,
        ),
        ForestFinalizedAppendKindV2::PrivateTransfer {
            recipient_event_id,
            change_event_id,
            nullifier,
            recipient_commitment,
            change_commitment,
            recipient_encrypted_note,
            change_encrypted_note,
        } => {
            if !same_transfer_event_v2(*recipient_event_id, *change_event_id) {
                return Err(LaneForestDurableErrorV2::InvalidEvent);
            }
            (
                LANE_FOREST_EVENT_PRIVATE_TRANSFER,
                *recipient_event_id,
                Some(*change_event_id),
                *nullifier,
                *recipient_commitment,
                *change_commitment,
                recipient_encrypted_note.as_ref(),
                change_encrypted_note.as_ref(),
            )
        }
        ForestFinalizedAppendKindV2::Withdrawal {
            event_id,
            nullifier,
            change_commitment,
            destination_token_account,
            amount,
            encrypted_note,
        } => {
            if *amount == 0 || *destination_token_account == [0u8; 32] {
                return Err(LaneForestDurableErrorV2::InvalidEvent);
            }
            (
                LANE_FOREST_EVENT_WITHDRAWAL,
                *event_id,
                None,
                *nullifier,
                *change_commitment,
                *destination_token_account,
                encrypted_note.as_ref(),
                None,
            )
        }
    };
    decode_digest_canonical(&first_commitment)
        .map_err(|_| LaneForestDurableErrorV2::InvalidEvent)?;
    if kind != LANE_FOREST_EVENT_DEPOSIT {
        decode_digest_canonical(&nullifier).map_err(|_| LaneForestDurableErrorV2::InvalidEvent)?;
    }
    if kind == LANE_FOREST_EVENT_PRIVATE_TRANSFER {
        decode_digest_canonical(&second_commitment)
            .map_err(|_| LaneForestDurableErrorV2::InvalidEvent)?;
    }
    let payload_count =
        usize::from(first_payload.is_some()) + usize::from(second_payload.is_some());
    let mut output = vec![
        0u8;
        LANE_FOREST_EVENT_HEADER_BYTES_V2
            + payload_count * POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES
    ];
    output[..4].copy_from_slice(&LANE_FOREST_EVENT_MAGIC_V2);
    output[4] = LANE_FOREST_EVENT_VERSION_V2;
    output[5] = kind;
    output[6] = event.lane_id.as_u8();
    output[7] = u8::from(first_payload.is_some()) | (u8::from(second_payload.is_some()) << 1);
    output[8..40].copy_from_slice(&event.master);
    output[40..148].copy_from_slice(&encode_event_id_v2(first_id));
    if let Some(second) = second_id {
        output[148..256].copy_from_slice(&encode_event_id_v2(second));
    }
    output[256..288].copy_from_slice(&nullifier);
    output[288..320].copy_from_slice(&first_commitment);
    output[320..352].copy_from_slice(&second_commitment);
    output[352..360].copy_from_slice(&event.pair_leaf_index.to_le_bytes());
    output[360..368].copy_from_slice(&event.root_sequence.to_le_bytes());
    output[368..400].copy_from_slice(&event.after_lane_address);
    output[400..1168].copy_from_slice(&event.after_lane_image);
    output[1168..1170].copy_from_slice(
        &(first_payload.map_or(0, |_| POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES as u16)).to_le_bytes(),
    );
    output[1170..1172].copy_from_slice(
        &(second_payload.map_or(0, |_| POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES as u16)).to_le_bytes(),
    );
    if let ForestFinalizedAppendKindV2::Withdrawal { amount, .. } = &event.kind {
        output[1172..1176].copy_from_slice(&amount.to_le_bytes());
    }
    let mut offset = LANE_FOREST_EVENT_HEADER_BYTES_V2;
    if let Some(payload) = first_payload {
        output[offset..offset + payload.len()].copy_from_slice(payload);
        offset += payload.len();
    }
    if let Some(payload) = second_payload {
        output[offset..offset + payload.len()].copy_from_slice(payload);
    }
    Ok(output)
}

pub fn decode_forest_finalized_append_event_v2(
    bytes: &[u8],
) -> Result<ForestFinalizedAppendEventV2, LaneForestDurableErrorV2> {
    if bytes.len() < LANE_FOREST_EVENT_HEADER_BYTES_V2 {
        return Err(LaneForestDurableErrorV2::WrongLength);
    }
    if bytes[..4] != LANE_FOREST_EVENT_MAGIC_V2 {
        return Err(LaneForestDurableErrorV2::WrongMagic);
    }
    if bytes[4] != LANE_FOREST_EVENT_VERSION_V2 {
        return Err(LaneForestDurableErrorV2::WrongVersion);
    }
    if bytes[1176..LANE_FOREST_EVENT_HEADER_BYTES_V2]
        .iter()
        .any(|byte| *byte != 0)
    {
        return Err(LaneForestDurableErrorV2::NonZeroReserved);
    }
    let kind = bytes[5];
    if kind != LANE_FOREST_EVENT_WITHDRAWAL && bytes[1172..1176] != [0u8; 4] {
        return Err(LaneForestDurableErrorV2::NonZeroReserved);
    }
    let lane_id = LaneIdV2::new(bytes[6]).map_err(|_| LaneForestDurableErrorV2::InvalidEvent)?;
    let flags = bytes[7];
    if flags & !3 != 0 {
        return Err(LaneForestDurableErrorV2::InvalidEvent);
    }
    let first_len = usize::from(u16::from_le_bytes(bytes[1168..1170].try_into().unwrap()));
    let second_len = usize::from(u16::from_le_bytes(bytes[1170..1172].try_into().unwrap()));
    for (present, length) in [(flags & 1 != 0, first_len), (flags & 2 != 0, second_len)] {
        if length
            != if present {
                POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES
            } else {
                0
            }
        {
            return Err(LaneForestDurableErrorV2::WrongLength);
        }
    }
    if bytes.len() != LANE_FOREST_EVENT_HEADER_BYTES_V2 + first_len + second_len {
        return Err(LaneForestDurableErrorV2::WrongLength);
    }
    let first_payload = (first_len != 0).then(|| {
        bytes[LANE_FOREST_EVENT_HEADER_BYTES_V2..LANE_FOREST_EVENT_HEADER_BYTES_V2 + first_len]
            .try_into()
            .unwrap()
    });
    let second_payload = (second_len != 0).then(|| {
        bytes[LANE_FOREST_EVENT_HEADER_BYTES_V2 + first_len..]
            .try_into()
            .unwrap()
    });
    let first_id = decode_event_id_v2(&bytes[40..148])?;
    let second_id_bytes = &bytes[148..256];
    let nullifier: [u8; 32] = bytes[256..288].try_into().unwrap();
    let first_commitment: [u8; 32] = bytes[288..320].try_into().unwrap();
    let second_commitment: [u8; 32] = bytes[320..352].try_into().unwrap();
    let event_kind = match kind {
        LANE_FOREST_EVENT_DEPOSIT => {
            if second_id_bytes.iter().any(|byte| *byte != 0)
                || nullifier != [0u8; 32]
                || second_commitment != [0u8; 32]
                || second_payload.is_some()
            {
                return Err(LaneForestDurableErrorV2::InvalidEvent);
            }
            ForestFinalizedAppendKindV2::Deposit {
                event_id: first_id,
                commitment: first_commitment,
                encrypted_note: first_payload,
            }
        }
        LANE_FOREST_EVENT_PRIVATE_TRANSFER => {
            let second_id = decode_event_id_v2(second_id_bytes)?;
            if !same_transfer_event_v2(first_id, second_id) {
                return Err(LaneForestDurableErrorV2::InvalidEvent);
            }
            ForestFinalizedAppendKindV2::PrivateTransfer {
                recipient_event_id: first_id,
                change_event_id: second_id,
                nullifier,
                recipient_commitment: first_commitment,
                change_commitment: second_commitment,
                recipient_encrypted_note: first_payload,
                change_encrypted_note: second_payload,
            }
        }
        LANE_FOREST_EVENT_WITHDRAWAL => {
            if second_id_bytes.iter().any(|byte| *byte != 0) || second_payload.is_some() {
                return Err(LaneForestDurableErrorV2::InvalidEvent);
            }
            ForestFinalizedAppendKindV2::Withdrawal {
                event_id: first_id,
                nullifier,
                change_commitment: first_commitment,
                destination_token_account: second_commitment,
                amount: u32::from_le_bytes(bytes[1172..1176].try_into().unwrap()),
                encrypted_note: first_payload,
            }
        }
        _ => return Err(LaneForestDurableErrorV2::InvalidEvent),
    };
    let event = ForestFinalizedAppendEventV2 {
        master: bytes[8..40].try_into().unwrap(),
        lane_id,
        pair_leaf_index: u64::from_le_bytes(bytes[352..360].try_into().unwrap()),
        root_sequence: u64::from_le_bytes(bytes[360..368].try_into().unwrap()),
        after_lane_address: bytes[368..400].try_into().unwrap(),
        after_lane_image: bytes[400..1168].try_into().unwrap(),
        kind: event_kind,
    };
    encode_forest_finalized_append_event_v2(&event)?;
    Ok(event)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairTrackedWitnessV2 {
    pub event_id: DepositEventIdV1,
    pub pair_leaf_index: u64,
    pub pair_leaf: Digest,
    pub siblings: [Digest; POOL_V1_TREE_DEPTH],
}

impl PairTrackedWitnessV2 {
    pub fn root(&self) -> Digest {
        pair_witness_root_v2(self.pair_leaf_index, self.pair_leaf, &self.siblings)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairLaneWitnessStateV2 {
    tree: IncrementalMerkleTreeV1,
    tracked: Vec<PairTrackedWitnessV2>,
}

impl PairLaneWitnessStateV2 {
    pub fn from_authenticated_lane_v2(lane: &AuthenticatedForestLaneAccountV2) -> Self {
        Self {
            tree: lane.value.tree,
            tracked: Vec::new(),
        }
    }

    pub fn tree(&self) -> &IncrementalMerkleTreeV1 {
        &self.tree
    }

    pub fn tracked(&self) -> &[PairTrackedWitnessV2] {
        &self.tracked
    }

    fn append_authenticated_pair_v2(
        &mut self,
        event_id: Option<DepositEventIdV1>,
        pair_leaf_index: u64,
        pair_leaf: Digest,
        expected_tree: IncrementalMerkleTreeV1,
    ) -> Result<(), LaneForestDurableErrorV2> {
        if pair_leaf_index != self.tree.next_leaf_index {
            return Err(LaneForestDurableErrorV2::LaneSequenceMismatch);
        }
        if event_id.is_some_and(|id| self.tracked.iter().any(|entry| entry.event_id == id)) {
            return Err(LaneForestDurableErrorV2::DuplicateEvent);
        }
        let (partial, terminal) = pair_append_partial_roots_v2(&self.tree, pair_leaf)?;
        let (next, receipt) = self
            .tree
            .append_one_with_empty_roots(pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)?;
        if next != expected_tree
            || receipt.leaf_index != pair_leaf_index
            || receipt.root_sequence != pair_leaf_index + 1
            || terminal != expected_tree.root
        {
            return Err(LaneForestDurableErrorV2::LaneStateMismatch);
        }
        let mut tracked = self.tracked.clone();
        for witness in &mut tracked {
            let differing = witness.pair_leaf_index ^ pair_leaf_index;
            if differing == 0 {
                return Err(LaneForestDurableErrorV2::DuplicateEvent);
            }
            let level = (u64::BITS - 1 - differing.leading_zeros()) as usize;
            if level >= POOL_V1_TREE_DEPTH {
                return Err(LaneForestDurableErrorV2::WitnessMismatch);
            }
            witness.siblings[level] = partial[level];
        }
        if let Some(event_id) = event_id {
            let siblings = core::array::from_fn(|level| {
                if (pair_leaf_index >> level) & 1 == 0 {
                    POOL_V1_PAIR_EMPTY_ROOTS[level]
                } else {
                    self.tree.frontier[level]
                }
            });
            tracked.push(PairTrackedWitnessV2 {
                event_id,
                pair_leaf_index,
                pair_leaf,
                siblings,
            });
        }
        if tracked.iter().any(|witness| witness.root() != next.root) {
            return Err(LaneForestDurableErrorV2::WitnessMismatch);
        }
        self.tree = next;
        self.tracked = tracked;
        Ok(())
    }
}

fn pair_append_partial_roots_v2(
    tree: &IncrementalMerkleTreeV1,
    leaf: Digest,
) -> Result<([Digest; POOL_V1_TREE_DEPTH], Digest), LaneForestDurableErrorV2> {
    if tree.next_leaf_index >= POOL_V1_PAIR_CAPACITY {
        return Err(LaneForestDurableErrorV2::Tree(PoolV1TreeError::TreeFull));
    }
    let mut partial = [[M31::ZERO; 8]; POOL_V1_TREE_DEPTH];
    let mut current = leaf;
    for level in 0..POOL_V1_TREE_DEPTH {
        partial[level] = current;
        current = if (tree.next_leaf_index >> level) & 1 == 0 {
            pool_v1_tree_parent(&current, &POOL_V1_PAIR_EMPTY_ROOTS[level])
        } else {
            pool_v1_tree_parent(&tree.frontier[level], &current)
        };
    }
    Ok((partial, current))
}

fn pair_witness_root_v2(
    index: u64,
    leaf: Digest,
    siblings: &[Digest; POOL_V1_TREE_DEPTH],
) -> Digest {
    let mut current = leaf;
    for (level, sibling) in siblings.iter().enumerate() {
        current = if (index >> level) & 1 == 0 {
            pool_v1_tree_parent(&current, sibling)
        } else {
            pool_v1_tree_parent(sibling, &current)
        };
    }
    current
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ForestTrackedOutputV2 {
    pub output_event_id: DepositEventIdV1,
    pub witness_event_id: DepositEventIdV1,
    pub lane_id: LaneIdV2,
    pub pair_leaf_index: u64,
    pub slot: PairSlotV2,
    pub commitment: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct DurableLaneCoreV2 {
    account: AuthenticatedForestLaneAccountV2,
    witness: PairLaneWitnessStateV2,
    tracked_outputs: Vec<ForestTrackedOutputV2>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ForestCoreV2 {
    master: AuthenticatedForestMasterAccountV2,
    lanes: [DurableLaneCoreV2; POOL_V1_LANE_COUNT_V2],
    events: Vec<ForestFinalizedAppendEventV2>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ForestCheckpointSnapshotV2 {
    point: FinalizedChainPointV1,
    checkpoint: AuthenticatedForestCheckpointAccountV2,
    core: ForestCoreV2,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LaneForestDurableStateV2 {
    program_id: [u8; 32],
    core: ForestCoreV2,
    checkpoints: Vec<ForestCheckpointSnapshotV2>,
    finalized_head: Option<FinalizedChainPointV1>,
}

pub enum ForestNoteAssociationOutcomeV2 {
    PayloadAbsent,
    InvalidEncryptedPayload(PoolV1WalletError),
    NotForViewingKey,
    Recovered(NoteOpeningV1),
}

impl core::fmt::Debug for ForestNoteAssociationOutcomeV2 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::PayloadAbsent => formatter.write_str("PayloadAbsent"),
            Self::InvalidEncryptedPayload(error) => formatter
                .debug_tuple("InvalidEncryptedPayload")
                .field(error)
                .finish(),
            Self::NotForViewingKey => formatter.write_str("NotForViewingKey"),
            Self::Recovered(_) => formatter.write_str("Recovered([REDACTED])"),
        }
    }
}

pub struct ForestNoteAssociationV2 {
    pub output_event_id: DepositEventIdV1,
    pub lane_id: LaneIdV2,
    pub pair_leaf_index: u64,
    pub slot: PairSlotV2,
    pub commitment: [u8; 32],
    pub outcome: ForestNoteAssociationOutcomeV2,
}

impl LaneForestDurableStateV2 {
    pub fn from_authenticated_accounts_v2(
        program_id: [u8; 32],
        master_address: [u8; 32],
        master_image: &[u8],
        lane_accounts: &[([u8; 32], Vec<u8>)],
        retained_checkpoint: Option<(FinalizedChainPointV1, [u8; 32], Vec<u8>)>,
    ) -> Result<Self, LaneForestDurableErrorV2> {
        let master =
            authenticate_forest_master_account_v2(program_id, master_address, master_image)?;
        if master.value.initialized_lane_mask != POOL_V1_PAIR_FOREST_ALL_LANES_MASK
            || lane_accounts.len() != POOL_V1_PAIR_FOREST_LANE_COUNT
        {
            return Err(LaneForestDurableErrorV2::LaneOrderMismatch);
        }
        let mut lanes = Vec::with_capacity(POOL_V1_PAIR_FOREST_LANE_COUNT);
        let mut addresses = HashSet::new();
        for (index, (address, image)) in lane_accounts.iter().enumerate() {
            if !addresses.insert(*address) {
                return Err(LaneForestDurableErrorV2::LaneAlias);
            }
            let lane_id = LaneIdV2::new(index as u8)
                .map_err(|_| LaneForestDurableErrorV2::LaneOrderMismatch)?;
            let account = authenticate_forest_lane_account_v2(
                program_id,
                master_address,
                lane_id,
                *address,
                image,
            )?;
            lanes.push(DurableLaneCoreV2 {
                witness: PairLaneWitnessStateV2::from_authenticated_lane_v2(&account),
                account,
                tracked_outputs: Vec::new(),
            });
        }
        let lanes: [DurableLaneCoreV2; POOL_V1_LANE_COUNT_V2] = lanes
            .try_into()
            .map_err(|_| LaneForestDurableErrorV2::LaneOrderMismatch)?;
        let core = ForestCoreV2 {
            master,
            lanes,
            events: Vec::new(),
        };
        let mut result = Self {
            program_id,
            core,
            checkpoints: Vec::new(),
            finalized_head: None,
        };
        match (result.core.master.value.has_checkpoint, retained_checkpoint) {
            (false, None) => {}
            (true, Some((point, address, image))) => {
                let checkpoint = authenticate_forest_checkpoint_account_v2(
                    program_id,
                    master_address,
                    result.core.master.value.identity.deployment_domain,
                    address,
                    &image,
                )?;
                result.validate_checkpoint_matches_current_v2(&checkpoint)?;
                if checkpoint.value.checkpoint_sequence + 1
                    != result.core.master.value.next_checkpoint_sequence
                    || checkpoint.value.lane_sequences
                        != result.core.master.value.last_checkpoint_lane_sequences
                {
                    return Err(LaneForestDurableErrorV2::CheckpointSequenceMismatch);
                }
                result.checkpoints.push(ForestCheckpointSnapshotV2 {
                    point,
                    checkpoint,
                    core: result.core.clone(),
                });
            }
            _ => return Err(LaneForestDurableErrorV2::CheckpointSequenceMismatch),
        }
        Ok(result)
    }

    pub fn program_id(&self) -> &[u8; 32] {
        &self.program_id
    }

    pub fn master(&self) -> &AuthenticatedForestMasterAccountV2 {
        &self.core.master
    }

    pub fn lane(
        &self,
        lane_id: LaneIdV2,
    ) -> (&AuthenticatedForestLaneAccountV2, &PairLaneWitnessStateV2) {
        let lane = &self.core.lanes[lane_id.index()];
        (&lane.account, &lane.witness)
    }

    pub fn tracked_outputs(&self, lane_id: LaneIdV2) -> &[ForestTrackedOutputV2] {
        &self.core.lanes[lane_id.index()].tracked_outputs
    }

    pub fn contains_event_id_v2(&self, event_id: DepositEventIdV1) -> bool {
        self.retained_event_v2(event_id).is_some()
    }

    pub(crate) fn retained_event_v2(
        &self,
        event_id: DepositEventIdV1,
    ) -> Option<&ForestFinalizedAppendEventV2> {
        self.core.events.iter().find(|event| {
            let (first, second) = event.event_ids();
            first == event_id || second == Some(event_id)
        })
    }

    pub fn lane_page_cursors_v2(
        &self,
    ) -> Result<[LaneRootPageCursorV2; POOL_V1_LANE_COUNT_V2], LaneForestDurableErrorV2> {
        let mut cursors = Vec::with_capacity(POOL_V1_LANE_COUNT_V2);
        for lane in &self.core.lanes {
            cursors.push(canonical_lane_root_page_cursor_v2(
                self.program_id,
                self.core.master.address,
                LaneIdV2::new(lane.account.value.lane_id)
                    .map_err(|_| LaneForestDurableErrorV2::LaneOrderMismatch)?,
                lane.account.value.tree.next_leaf_index,
            )?);
        }
        cursors
            .try_into()
            .map_err(|_| LaneForestDurableErrorV2::LaneOrderMismatch)
    }

    pub fn checkpoint_count(&self) -> usize {
        self.checkpoints.len()
    }

    pub fn retained_event_count_v2(&self) -> usize {
        self.core.events.len()
    }

    pub fn finalized_head_v2(&self) -> Option<FinalizedChainPointV1> {
        self.finalized_head
    }

    pub fn retained_checkpoint_sequence_at_point_v2(
        &self,
        point: FinalizedChainPointV1,
    ) -> Option<u64> {
        self.checkpoints.iter().find_map(|snapshot| {
            (snapshot.point == point).then_some(snapshot.checkpoint.value.checkpoint_sequence)
        })
    }

    pub fn validate_current_account_snapshot_v2(
        &self,
        master_address: [u8; 32],
        master_image: &[u8],
        lane_accounts: &[([u8; 32], Vec<u8>)],
    ) -> Result<(), LaneForestDurableErrorV2> {
        let master =
            authenticate_forest_master_account_v2(self.program_id, master_address, master_image)?;
        if master != self.core.master || lane_accounts.len() != POOL_V1_LANE_COUNT_V2 {
            return Err(LaneForestDurableErrorV2::LaneStateMismatch);
        }
        let mut seen = HashSet::new();
        for (index, (address, image)) in lane_accounts.iter().enumerate() {
            if !seen.insert(*address) {
                return Err(LaneForestDurableErrorV2::LaneAlias);
            }
            let lane_id = LaneIdV2::new(index as u8)
                .map_err(|_| LaneForestDurableErrorV2::LaneOrderMismatch)?;
            let lane = authenticate_forest_lane_account_v2(
                self.program_id,
                self.core.master.address,
                lane_id,
                *address,
                image,
            )?;
            if lane != self.core.lanes[index].account {
                return Err(LaneForestDurableErrorV2::LaneStateMismatch);
            }
        }
        Ok(())
    }

    pub(crate) fn set_finalized_head_v2(&mut self, point: FinalizedChainPointV1) {
        self.finalized_head = Some(point);
    }

    /// Ingest one finalized append. An exact canonical replay is a no-op that
    /// returns an empty association vector; conflicting identity reuse errors.
    pub fn ingest_finalized_append_v2(
        &mut self,
        event: ForestFinalizedAppendEventV2,
        viewing_secret: Option<&ViewingSecretKeyV1>,
    ) -> Result<Vec<ForestNoteAssociationV2>, LaneForestDurableErrorV2> {
        self.ingest_finalized_append_inner_v2(event, viewing_secret, None)
    }

    /// Apply an append whose selected outputs were already authenticated by
    /// the authoritative local-note envelope. This keeps witness selection in
    /// the same atomic candidate without requiring the HPKE viewing key again.
    pub(crate) fn ingest_finalized_append_preselected_v2(
        &mut self,
        event: ForestFinalizedAppendEventV2,
        selected_output_ids: &[DepositEventIdV1],
    ) -> Result<(), LaneForestDurableErrorV2> {
        let selected = selected_output_ids.iter().copied().collect::<HashSet<_>>();
        if selected.len() != selected_output_ids.len() {
            return Err(LaneForestDurableErrorV2::DuplicateEvent);
        }
        self.ingest_finalized_append_inner_v2(event, None, Some(&selected))?;
        Ok(())
    }

    fn ingest_finalized_append_inner_v2(
        &mut self,
        event: ForestFinalizedAppendEventV2,
        viewing_secret: Option<&ViewingSecretKeyV1>,
        preselected: Option<&HashSet<DepositEventIdV1>>,
    ) -> Result<Vec<ForestNoteAssociationV2>, LaneForestDurableErrorV2> {
        if event.master != self.core.master.address {
            return Err(LaneForestDurableErrorV2::MasterMismatch);
        }
        let event_wire = encode_forest_finalized_append_event_v2(&event)?;
        let event = decode_forest_finalized_append_event_v2(&event_wire)?;
        let (first_id, second_id) = event.event_ids();
        if preselected.is_some_and(|selected| {
            selected
                .iter()
                .any(|event_id| *event_id != first_id && Some(*event_id) != second_id)
        }) {
            return Err(LaneForestDurableErrorV2::InvalidEvent);
        }
        if let Some(previous) = self.core.events.iter().find(|previous| {
            let (previous_first, previous_second) = previous.event_ids();
            previous_first == first_id
                || previous_second == Some(first_id)
                || second_id.is_some_and(|second| {
                    previous_first == second || previous_second == Some(second)
                })
        }) {
            // Every newly accepted append produces one or two associations,
            // so an empty vector is an unambiguous exact-replay no-op.  Any
            // reuse of either stable output identity with different canonical
            // event data remains a fail-closed conflict.
            if previous != &event {
                return Err(LaneForestDurableErrorV2::DuplicateEvent);
            }
            if let Some(selected) = preselected {
                let retained = self.core.lanes[event.lane_id.index()]
                    .tracked_outputs
                    .iter()
                    .filter(|output| output.witness_event_id == first_id)
                    .map(|output| output.output_event_id)
                    .collect::<HashSet<_>>();
                if &retained != selected {
                    return Err(LaneForestDurableErrorV2::DuplicateEvent);
                }
            }
            return Ok(Vec::new());
        }
        if self
            .core
            .events
            .last()
            .is_some_and(|previous| previous.point().slot() > event.point().slot())
        {
            return Err(LaneForestDurableErrorV2::EventOutsideFinalizedOrder);
        }
        let after = authenticate_forest_lane_account_v2(
            self.program_id,
            self.core.master.address,
            event.lane_id,
            event.after_lane_address,
            &event.after_lane_image,
        )?;
        let lane = &self.core.lanes[event.lane_id.index()];
        if lane.account.address != after.address
            || lane.account.value.tree.next_leaf_index != event.pair_leaf_index
            || after.value.tree.next_leaf_index != event.root_sequence
        {
            return Err(LaneForestDurableErrorV2::LaneSequenceMismatch);
        }

        let (pair_leaf, output_data) = match &event.kind {
            ForestFinalizedAppendKindV2::Deposit {
                event_id,
                commitment,
                encrypted_note,
            } => {
                let digest = decode_digest_canonical(commitment)
                    .map_err(|_| LaneForestDurableErrorV2::InvalidEvent)?;
                let expected_lane = LaneIdV2::new(encode_digest_canonical(&digest)[0] & 7)
                    .map_err(|_| LaneForestDurableErrorV2::WrongRoutedLane)?;
                if expected_lane != event.lane_id {
                    return Err(LaneForestDurableErrorV2::WrongRoutedLane);
                }
                (
                    PoolV1PairLeafWitnessV1::single_output(digest)?.leaf_digest()?,
                    vec![(
                        *event_id,
                        PairSlotV2::First,
                        *commitment,
                        encrypted_note.as_ref(),
                    )],
                )
            }
            ForestFinalizedAppendKindV2::PrivateTransfer {
                recipient_event_id,
                change_event_id,
                nullifier,
                recipient_commitment,
                change_commitment,
                recipient_encrypted_note,
                change_encrypted_note,
            } => {
                let nullifier_digest = decode_digest_canonical(nullifier)
                    .map_err(|_| LaneForestDurableErrorV2::InvalidEvent)?;
                let expected_lane =
                    LaneIdV2::new(encode_digest_canonical(&nullifier_digest)[0] & 7)
                        .map_err(|_| LaneForestDurableErrorV2::WrongRoutedLane)?;
                if expected_lane != event.lane_id {
                    return Err(LaneForestDurableErrorV2::WrongRoutedLane);
                }
                let recipient = decode_digest_canonical(recipient_commitment)
                    .map_err(|_| LaneForestDurableErrorV2::InvalidEvent)?;
                let change = decode_digest_canonical(change_commitment)
                    .map_err(|_| LaneForestDurableErrorV2::InvalidEvent)?;
                (
                    PoolV1PairLeafWitnessV1::two_outputs(recipient, change)?.leaf_digest()?,
                    vec![
                        (
                            *recipient_event_id,
                            PairSlotV2::First,
                            *recipient_commitment,
                            recipient_encrypted_note.as_ref(),
                        ),
                        (
                            *change_event_id,
                            PairSlotV2::Second,
                            *change_commitment,
                            change_encrypted_note.as_ref(),
                        ),
                    ],
                )
            }
            ForestFinalizedAppendKindV2::Withdrawal {
                event_id,
                nullifier,
                change_commitment,
                encrypted_note,
                ..
            } => {
                let nullifier_digest = decode_digest_canonical(nullifier)
                    .map_err(|_| LaneForestDurableErrorV2::InvalidEvent)?;
                let expected_lane =
                    LaneIdV2::new(encode_digest_canonical(&nullifier_digest)[0] & 7)
                        .map_err(|_| LaneForestDurableErrorV2::WrongRoutedLane)?;
                if expected_lane != event.lane_id {
                    return Err(LaneForestDurableErrorV2::WrongRoutedLane);
                }
                let change = decode_digest_canonical(change_commitment)
                    .map_err(|_| LaneForestDurableErrorV2::InvalidEvent)?;
                (
                    PoolV1PairLeafWitnessV1::single_output(change)?.leaf_digest()?,
                    vec![(
                        *event_id,
                        PairSlotV2::First,
                        *change_commitment,
                        encrypted_note.as_ref(),
                    )],
                )
            }
        };
        let expected_next = lane
            .account
            .value
            .tree
            .append_one_with_empty_roots(pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)?
            .0;
        if expected_next != after.value.tree {
            return Err(LaneForestDurableErrorV2::LaneStateMismatch);
        }

        let mut associations = Vec::with_capacity(output_data.len());
        let mut track = Vec::with_capacity(output_data.len());
        for (event_id, slot, commitment, payload) in output_data {
            let outcome = match (viewing_secret, payload) {
                (_, None) => ForestNoteAssociationOutcomeV2::PayloadAbsent,
                (None, Some(_)) => ForestNoteAssociationOutcomeV2::NotForViewingKey,
                (Some(secret), Some(payload)) => {
                    let context = NoteContextV1::new(
                        self.core.master.address,
                        self.core.master.value.identity.deployment_domain,
                        event.pair_leaf_index,
                        commitment,
                    )?;
                    match scan_note_v1(secret, &context, payload) {
                        Ok(ScanResultV1::NotForViewingKey) => {
                            ForestNoteAssociationOutcomeV2::NotForViewingKey
                        }
                        Ok(ScanResultV1::RecoveredView(note)) => {
                            ForestNoteAssociationOutcomeV2::Recovered(note)
                        }
                        Err(error) => {
                            ForestNoteAssociationOutcomeV2::InvalidEncryptedPayload(error)
                        }
                    }
                }
            };
            track.push(preselected.map_or_else(
                || matches!(outcome, ForestNoteAssociationOutcomeV2::Recovered(_)),
                |selected| selected.contains(&event_id),
            ));
            associations.push(ForestNoteAssociationV2 {
                output_event_id: event_id,
                lane_id: event.lane_id,
                pair_leaf_index: event.pair_leaf_index,
                slot,
                commitment,
                outcome,
            });
        }

        let mut candidate = self.core.clone();
        let candidate_lane = &mut candidate.lanes[event.lane_id.index()];
        let witness_event = track.iter().any(|selected| *selected).then_some(first_id);
        candidate_lane.witness.append_authenticated_pair_v2(
            witness_event,
            event.pair_leaf_index,
            pair_leaf,
            after.value.tree,
        )?;
        for (association, selected) in associations.iter().zip(track) {
            if selected {
                candidate_lane.tracked_outputs.push(ForestTrackedOutputV2 {
                    output_event_id: association.output_event_id,
                    witness_event_id: first_id,
                    lane_id: event.lane_id,
                    pair_leaf_index: event.pair_leaf_index,
                    slot: association.slot,
                    commitment: association.commitment,
                });
            }
        }
        candidate_lane.account = after;
        candidate.events.push(event);
        if candidate.events.len() > MAX_LANE_FOREST_EVENTS_V2 {
            return Err(LaneForestDurableErrorV2::CountOverflow);
        }
        self.core = candidate;
        Ok(associations)
    }

    pub fn ingest_finalized_checkpoint_v2(
        &mut self,
        point: FinalizedChainPointV1,
        next_master_address: [u8; 32],
        next_master_image: &[u8],
        lane_accounts: &[([u8; 32], Vec<u8>)],
        checkpoint_address: [u8; 32],
        checkpoint_image: &[u8],
    ) -> Result<(), LaneForestDurableErrorV2> {
        if lane_accounts.len() != POOL_V1_LANE_COUNT_V2 {
            return Err(LaneForestDurableErrorV2::LaneOrderMismatch);
        }
        if self
            .checkpoints
            .last()
            .is_some_and(|snapshot| snapshot.point.slot() >= point.slot())
        {
            return Err(LaneForestDurableErrorV2::EventOutsideFinalizedOrder);
        }
        let checkpoint = authenticate_forest_checkpoint_account_v2(
            self.program_id,
            self.core.master.address,
            self.core.master.value.identity.deployment_domain,
            checkpoint_address,
            checkpoint_image,
        )?;
        if checkpoint.value.checkpoint_sequence != self.core.master.value.next_checkpoint_sequence {
            return Err(LaneForestDurableErrorV2::CheckpointSequenceMismatch);
        }
        let mut seen = HashSet::new();
        for (index, (address, image)) in lane_accounts.iter().enumerate() {
            if !seen.insert(*address) {
                return Err(LaneForestDurableErrorV2::LaneAlias);
            }
            let lane_id = LaneIdV2::new(index as u8)
                .map_err(|_| LaneForestDurableErrorV2::LaneOrderMismatch)?;
            let decoded = authenticate_forest_lane_account_v2(
                self.program_id,
                self.core.master.address,
                lane_id,
                *address,
                image,
            )?;
            if decoded != self.core.lanes[index].account {
                return Err(LaneForestDurableErrorV2::LaneStateMismatch);
            }
        }
        self.validate_checkpoint_matches_current_v2(&checkpoint)?;
        let next_master = authenticate_forest_master_account_v2(
            self.program_id,
            next_master_address,
            next_master_image,
        )?;
        if next_master.address != self.core.master.address
            || next_master.value.identity != self.core.master.value.identity
            || next_master.value.verifier_policy != self.core.master.value.verifier_policy
            || !next_master.value.has_checkpoint
            || next_master.value.next_checkpoint_sequence
                != checkpoint.value.checkpoint_sequence + 1
            || next_master.value.last_checkpoint_lane_sequences != checkpoint.value.lane_sequences
        {
            return Err(LaneForestDurableErrorV2::CheckpointSequenceMismatch);
        }
        if self.core.master.value.has_checkpoint {
            let progressed = checkpoint
                .value
                .lane_sequences
                .iter()
                .zip(self.core.master.value.last_checkpoint_lane_sequences)
                .try_fold(false, |strict, (next, previous)| {
                    if *next < previous {
                        Err(LaneForestDurableErrorV2::LaneSequenceMismatch)
                    } else {
                        Ok(strict || *next > previous)
                    }
                })?;
            if !progressed {
                return Err(LaneForestDurableErrorV2::CheckpointNoProgress);
            }
        }
        let mut core = self.core.clone();
        core.master = next_master;
        self.checkpoints.push(ForestCheckpointSnapshotV2 {
            point,
            checkpoint,
            core: core.clone(),
        });
        if self.checkpoints.len() > MAX_LANE_FOREST_SNAPSHOTS_V2 {
            return Err(LaneForestDurableErrorV2::CountOverflow);
        }
        self.core = core;
        self.finalized_head = Some(point);
        Ok(())
    }

    fn validate_checkpoint_matches_current_v2(
        &self,
        checkpoint: &AuthenticatedForestCheckpointAccountV2,
    ) -> Result<(), LaneForestDurableErrorV2> {
        let sequences = self
            .core
            .lanes
            .each_ref()
            .map(|lane| lane.account.value.tree.next_leaf_index);
        if checkpoint.value.lane_sequences != sequences {
            return Err(LaneForestDurableErrorV2::LaneSequenceMismatch);
        }
        let roots = self
            .core
            .lanes
            .each_ref()
            .map(|lane| encode_digest_canonical(&lane.account.value.tree.root));
        if encode_digest_canonical(&checkpoint.value.global_root)
            != lane_forest_global_root_v2(&roots)
                .map_err(|_| LaneForestDurableErrorV2::GlobalRootMismatch)?
        {
            return Err(LaneForestDurableErrorV2::GlobalRootMismatch);
        }
        Ok(())
    }

    pub fn rollback_to_finalized_checkpoint_v2(
        &mut self,
        checkpoint_sequence: u64,
    ) -> Result<(), LaneForestDurableErrorV2> {
        if !self
            .checkpoints
            .iter()
            .any(|snapshot| snapshot.checkpoint.value.checkpoint_sequence == checkpoint_sequence)
        {
            return Err(LaneForestDurableErrorV2::InvalidRollback);
        }
        // This state retains finalized events only. Removing any suffix could
        // lose a finalized note or resurrect a spend in the authoritative V2
        // wallet envelope. Confirmed/tentative observations are reorged by the
        // coordinator without mutating this finalized forest.
        Err(LaneForestDurableErrorV2::InvalidRollback)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct DurableImageV2 {
    program_id: Vec<u8>,
    finalized_head: Option<Vec<u8>>,
    core: CoreImageV2,
    checkpoints: Vec<CheckpointSnapshotImageV2>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct CoreImageV2 {
    master_address: Vec<u8>,
    master_image: Vec<u8>,
    lanes: Vec<LaneCoreImageV2>,
    events: Vec<Vec<u8>>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct LaneCoreImageV2 {
    address: Vec<u8>,
    account_image: Vec<u8>,
    witnesses: Vec<PairWitnessImageV2>,
    outputs: Vec<TrackedOutputImageV2>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct PairWitnessImageV2 {
    event_id: Vec<u8>,
    pair_leaf_index: u64,
    pair_leaf: Vec<u8>,
    siblings: Vec<Vec<u8>>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct TrackedOutputImageV2 {
    output_event_id: Vec<u8>,
    witness_event_id: Vec<u8>,
    lane_id: u8,
    pair_leaf_index: u64,
    slot: u8,
    commitment: Vec<u8>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct CheckpointSnapshotImageV2 {
    point: Vec<u8>,
    checkpoint_address: Vec<u8>,
    checkpoint_image: Vec<u8>,
    core: CoreImageV2,
}

fn exact_array<const N: usize>(bytes: &[u8]) -> Result<[u8; N], LaneForestDurableErrorV2> {
    bytes
        .try_into()
        .map_err(|_| LaneForestDurableErrorV2::WrongLength)
}

fn encode_point_v2(point: FinalizedChainPointV1) -> Vec<u8> {
    let mut output = vec![0u8; 40];
    output[..8].copy_from_slice(&point.slot().to_le_bytes());
    output[8..].copy_from_slice(point.block_hash());
    output
}

fn decode_point_v2(bytes: &[u8]) -> Result<FinalizedChainPointV1, LaneForestDurableErrorV2> {
    if bytes.len() != 40 {
        return Err(LaneForestDurableErrorV2::WrongLength);
    }
    FinalizedChainPointV1::new(
        u64::from_le_bytes(bytes[..8].try_into().unwrap()),
        bytes[8..].try_into().unwrap(),
    )
    .map_err(|_| LaneForestDurableErrorV2::InvalidDurableImage)
}

fn core_to_image_v2(core: &ForestCoreV2) -> Result<CoreImageV2, LaneForestDurableErrorV2> {
    let lanes = core
        .lanes
        .iter()
        .map(|lane| {
            let witnesses = lane
                .witness
                .tracked
                .iter()
                .map(|witness| PairWitnessImageV2 {
                    event_id: encode_event_id_v2(witness.event_id).to_vec(),
                    pair_leaf_index: witness.pair_leaf_index,
                    pair_leaf: encode_digest_canonical(&witness.pair_leaf).to_vec(),
                    siblings: witness
                        .siblings
                        .iter()
                        .map(|sibling| encode_digest_canonical(sibling).to_vec())
                        .collect(),
                })
                .collect();
            let outputs = lane
                .tracked_outputs
                .iter()
                .map(|output| TrackedOutputImageV2 {
                    output_event_id: encode_event_id_v2(output.output_event_id).to_vec(),
                    witness_event_id: encode_event_id_v2(output.witness_event_id).to_vec(),
                    lane_id: output.lane_id.as_u8(),
                    pair_leaf_index: output.pair_leaf_index,
                    slot: match output.slot {
                        PairSlotV2::First => 0,
                        PairSlotV2::Second => 1,
                    },
                    commitment: output.commitment.to_vec(),
                })
                .collect();
            LaneCoreImageV2 {
                address: lane.account.address.to_vec(),
                account_image: lane.account.image.to_vec(),
                witnesses,
                outputs,
            }
        })
        .collect();
    let events = core
        .events
        .iter()
        .map(encode_forest_finalized_append_event_v2)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(CoreImageV2 {
        master_address: core.master.address.to_vec(),
        master_image: core.master.image.to_vec(),
        lanes,
        events,
    })
}

fn core_from_image_v2(
    program_id: [u8; 32],
    image: CoreImageV2,
) -> Result<ForestCoreV2, LaneForestDurableErrorV2> {
    let master_address = exact_array(&image.master_address)?;
    let master =
        authenticate_forest_master_account_v2(program_id, master_address, &image.master_image)?;
    if image.lanes.len() != POOL_V1_LANE_COUNT_V2 {
        return Err(LaneForestDurableErrorV2::LaneOrderMismatch);
    }
    let mut lanes = Vec::with_capacity(POOL_V1_LANE_COUNT_V2);
    let mut all_output_ids = HashSet::new();
    for (index, lane_image) in image.lanes.into_iter().enumerate() {
        let lane_id =
            LaneIdV2::new(index as u8).map_err(|_| LaneForestDurableErrorV2::LaneOrderMismatch)?;
        let address = exact_array(&lane_image.address)?;
        let account = authenticate_forest_lane_account_v2(
            program_id,
            master.address,
            lane_id,
            address,
            &lane_image.account_image,
        )?;
        let mut tracked = Vec::with_capacity(lane_image.witnesses.len());
        let mut witness_ids = HashSet::new();
        let mut witness_indices = HashSet::new();
        for witness in lane_image.witnesses {
            if witness.siblings.len() != POOL_V1_TREE_DEPTH {
                return Err(LaneForestDurableErrorV2::WitnessMismatch);
            }
            let event_id = decode_event_id_v2(&witness.event_id)?;
            if !witness_ids.insert(event_id) || !witness_indices.insert(witness.pair_leaf_index) {
                return Err(LaneForestDurableErrorV2::DuplicateEvent);
            }
            let pair_leaf = decode_digest_canonical(&exact_array(&witness.pair_leaf)?)
                .map_err(|_| LaneForestDurableErrorV2::WitnessMismatch)?;
            let mut siblings = [[M31::ZERO; 8]; POOL_V1_TREE_DEPTH];
            for (output, encoded) in siblings.iter_mut().zip(witness.siblings) {
                *output = decode_digest_canonical(&exact_array(&encoded)?)
                    .map_err(|_| LaneForestDurableErrorV2::WitnessMismatch)?;
            }
            let decoded = PairTrackedWitnessV2 {
                event_id,
                pair_leaf_index: witness.pair_leaf_index,
                pair_leaf,
                siblings,
            };
            if decoded.pair_leaf_index >= account.value.tree.next_leaf_index
                || decoded.root() != account.value.tree.root
            {
                return Err(LaneForestDurableErrorV2::WitnessMismatch);
            }
            tracked.push(decoded);
        }
        let mut outputs = Vec::with_capacity(lane_image.outputs.len());
        for output in lane_image.outputs {
            let output_event_id = decode_event_id_v2(&output.output_event_id)?;
            let witness_event_id = decode_event_id_v2(&output.witness_event_id)?;
            let output_lane = LaneIdV2::new(output.lane_id)
                .map_err(|_| LaneForestDurableErrorV2::LaneOrderMismatch)?;
            if output_lane != lane_id
                || !all_output_ids.insert(output_event_id)
                || !tracked.iter().any(|witness| {
                    witness.event_id == witness_event_id
                        && witness.pair_leaf_index == output.pair_leaf_index
                })
            {
                return Err(LaneForestDurableErrorV2::WitnessMismatch);
            }
            let commitment = exact_array(&output.commitment)?;
            decode_digest_canonical(&commitment)
                .map_err(|_| LaneForestDurableErrorV2::WitnessMismatch)?;
            outputs.push(ForestTrackedOutputV2 {
                output_event_id,
                witness_event_id,
                lane_id,
                pair_leaf_index: output.pair_leaf_index,
                slot: match output.slot {
                    0 => PairSlotV2::First,
                    1 => PairSlotV2::Second,
                    _ => return Err(LaneForestDurableErrorV2::InvalidDurableImage),
                },
                commitment,
            });
        }
        lanes.push(DurableLaneCoreV2 {
            account,
            witness: PairLaneWitnessStateV2 {
                tree: account.value.tree,
                tracked,
            },
            tracked_outputs: outputs,
        });
    }
    let lanes: [DurableLaneCoreV2; POOL_V1_LANE_COUNT_V2] = lanes
        .try_into()
        .map_err(|_| LaneForestDurableErrorV2::LaneOrderMismatch)?;
    if image.events.len() > MAX_LANE_FOREST_EVENTS_V2 {
        return Err(LaneForestDurableErrorV2::CountOverflow);
    }
    let mut event_ids = HashSet::new();
    let mut events = Vec::with_capacity(image.events.len());
    let mut previous_event_slot = None;
    let mut latest_event_account: [Option<AuthenticatedForestLaneAccountV2>;
        POOL_V1_LANE_COUNT_V2] = [None; POOL_V1_LANE_COUNT_V2];
    for encoded in image.events {
        let event = decode_forest_finalized_append_event_v2(&encoded)?;
        if event.master != master.address {
            return Err(LaneForestDurableErrorV2::MasterMismatch);
        }
        if previous_event_slot.is_some_and(|slot| slot > event.point().slot()) {
            return Err(LaneForestDurableErrorV2::EventOutsideFinalizedOrder);
        }
        let after = authenticate_forest_lane_account_v2(
            program_id,
            master.address,
            event.lane_id,
            event.after_lane_address,
            &event.after_lane_image,
        )?;
        let (first, second) = event.event_ids();
        if !event_ids.insert(first) || second.is_some_and(|id| !event_ids.insert(id)) {
            return Err(LaneForestDurableErrorV2::DuplicateEvent);
        }
        previous_event_slot = Some(event.point().slot());
        latest_event_account[event.lane_id.index()] = Some(after);
        events.push(event);
    }
    for (lane, latest) in lanes.iter().zip(latest_event_account) {
        if latest.is_some_and(|account| account != lane.account) {
            return Err(LaneForestDurableErrorV2::LaneStateMismatch);
        }
    }
    Ok(ForestCoreV2 {
        master,
        lanes,
        events,
    })
}

pub fn encode_lane_forest_durable_state_v2(
    state: &LaneForestDurableStateV2,
) -> Result<Vec<u8>, LaneForestDurableErrorV2> {
    let image = DurableImageV2 {
        program_id: state.program_id.to_vec(),
        finalized_head: state.finalized_head.map(encode_point_v2),
        core: core_to_image_v2(&state.core)?,
        checkpoints: state
            .checkpoints
            .iter()
            .map(|snapshot| {
                Ok(CheckpointSnapshotImageV2 {
                    point: encode_point_v2(snapshot.point),
                    checkpoint_address: snapshot.checkpoint.address.to_vec(),
                    checkpoint_image: snapshot.checkpoint.image.to_vec(),
                    core: core_to_image_v2(&snapshot.core)?,
                })
            })
            .collect::<Result<Vec<_>, LaneForestDurableErrorV2>>()?,
    };
    let payload = bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_little_endian()
        .serialize(&image)
        .map_err(|_| LaneForestDurableErrorV2::InvalidDurableImage)?;
    let length = LANE_FOREST_DURABLE_HEADER_BYTES_V2
        .checked_add(payload.len())
        .ok_or(LaneForestDurableErrorV2::CountOverflow)?;
    if length > MAX_LANE_FOREST_DURABLE_BYTES_V2 {
        return Err(LaneForestDurableErrorV2::CountOverflow);
    }
    let mut output = vec![0u8; length];
    output[..4].copy_from_slice(&LANE_FOREST_DURABLE_MAGIC_V2);
    output[4] = LANE_FOREST_DURABLE_VERSION_V2;
    output[5] = POOL_V1_LANE_COUNT_V2 as u8;
    output[8..16].copy_from_slice(&(payload.len() as u64).to_le_bytes());
    output[16..24].copy_from_slice(&(state.checkpoints.len() as u64).to_le_bytes());
    output[LANE_FOREST_DURABLE_HEADER_BYTES_V2..].copy_from_slice(&payload);
    let checksum = lane_forest_durable_checksum_v2(&output)?;
    output[LANE_FOREST_DURABLE_CHECKSUM_OFFSET_V2..LANE_FOREST_DURABLE_HEADER_BYTES_V2]
        .copy_from_slice(&checksum);
    Ok(output)
}

pub fn decode_lane_forest_durable_state_v2(
    bytes: &[u8],
) -> Result<LaneForestDurableStateV2, LaneForestDurableErrorV2> {
    if bytes.len() < LANE_FOREST_DURABLE_HEADER_BYTES_V2
        || bytes.len() > MAX_LANE_FOREST_DURABLE_BYTES_V2
    {
        return Err(LaneForestDurableErrorV2::WrongLength);
    }
    if bytes[..4] != LANE_FOREST_DURABLE_MAGIC_V2 {
        return Err(LaneForestDurableErrorV2::WrongMagic);
    }
    if bytes[4] != LANE_FOREST_DURABLE_VERSION_V2 {
        return Err(LaneForestDurableErrorV2::WrongVersion);
    }
    if bytes[5] != POOL_V1_LANE_COUNT_V2 as u8 || bytes[6..8] != [0u8; 2] {
        return Err(LaneForestDurableErrorV2::NonZeroReserved);
    }
    let payload_length = usize::try_from(u64::from_le_bytes(bytes[8..16].try_into().unwrap()))
        .map_err(|_| LaneForestDurableErrorV2::CountOverflow)?;
    let checkpoint_count = usize::try_from(u64::from_le_bytes(bytes[16..24].try_into().unwrap()))
        .map_err(|_| LaneForestDurableErrorV2::CountOverflow)?;
    if checkpoint_count > MAX_LANE_FOREST_SNAPSHOTS_V2
        || payload_length != bytes.len() - LANE_FOREST_DURABLE_HEADER_BYTES_V2
        || bytes[LANE_FOREST_DURABLE_CHECKSUM_OFFSET_V2..LANE_FOREST_DURABLE_HEADER_BYTES_V2]
            != lane_forest_durable_checksum_v2(bytes)?
    {
        return Err(LaneForestDurableErrorV2::ChecksumMismatch);
    }
    let image: DurableImageV2 = bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_little_endian()
        .reject_trailing_bytes()
        .with_limit(MAX_LANE_FOREST_DURABLE_BYTES_V2 as u64)
        .deserialize(&bytes[LANE_FOREST_DURABLE_HEADER_BYTES_V2..])
        .map_err(|_| LaneForestDurableErrorV2::InvalidDurableImage)?;
    if image.checkpoints.len() != checkpoint_count {
        return Err(LaneForestDurableErrorV2::InvalidDurableImage);
    }
    let program_id = exact_array(&image.program_id)?;
    let finalized_head = image
        .finalized_head
        .as_deref()
        .map(decode_point_v2)
        .transpose()?;
    let core = core_from_image_v2(program_id, image.core)?;
    let mut checkpoints = Vec::with_capacity(image.checkpoints.len());
    let mut previous_sequence = None;
    let mut previous_slot = None;
    for snapshot in image.checkpoints {
        let point = decode_point_v2(&snapshot.point)?;
        let checkpoint_address = exact_array(&snapshot.checkpoint_address)?;
        let checkpoint = authenticate_forest_checkpoint_account_v2(
            program_id,
            core.master.address,
            core.master.value.identity.deployment_domain,
            checkpoint_address,
            &snapshot.checkpoint_image,
        )?;
        if previous_sequence
            .is_some_and(|sequence| sequence >= checkpoint.value.checkpoint_sequence)
            || previous_slot.is_some_and(|slot| slot >= point.slot())
        {
            return Err(LaneForestDurableErrorV2::InvalidDurableImage);
        }
        let snapshot_core = core_from_image_v2(program_id, snapshot.core)?;
        if snapshot_core.master.address != core.master.address
            || !snapshot_core.master.value.has_checkpoint
            || snapshot_core.master.value.next_checkpoint_sequence
                != checkpoint.value.checkpoint_sequence + 1
            || snapshot_core.master.value.last_checkpoint_lane_sequences
                != checkpoint.value.lane_sequences
            || snapshot_core
                .events
                .last()
                .is_some_and(|event| event.point().slot() > point.slot())
        {
            return Err(LaneForestDurableErrorV2::InvalidDurableImage);
        }
        let snapshot_state = LaneForestDurableStateV2 {
            program_id,
            core: snapshot_core.clone(),
            checkpoints: Vec::new(),
            finalized_head: Some(point),
        };
        snapshot_state.validate_checkpoint_matches_current_v2(&checkpoint)?;
        previous_sequence = Some(checkpoint.value.checkpoint_sequence);
        previous_slot = Some(point.slot());
        checkpoints.push(ForestCheckpointSnapshotV2 {
            point,
            checkpoint,
            core: snapshot_core,
        });
    }
    match checkpoints.last() {
        Some(last)
            if !core.master.value.has_checkpoint
                || last.checkpoint.value.checkpoint_sequence + 1
                    != core.master.value.next_checkpoint_sequence
                || last.checkpoint.value.lane_sequences
                    != core.master.value.last_checkpoint_lane_sequences =>
        {
            return Err(LaneForestDurableErrorV2::InvalidDurableImage);
        }
        None if core.master.value.has_checkpoint => {
            return Err(LaneForestDurableErrorV2::InvalidDurableImage);
        }
        _ => {}
    }
    Ok(LaneForestDurableStateV2 {
        program_id,
        core,
        checkpoints,
        finalized_head,
    })
}

fn lane_forest_durable_checksum_v2(bytes: &[u8]) -> Result<[u8; 32], LaneForestDurableErrorV2> {
    if bytes.len() < LANE_FOREST_DURABLE_HEADER_BYTES_V2 {
        return Err(LaneForestDurableErrorV2::WrongLength);
    }
    let mut hasher = Sha256::new();
    hasher.update(LANE_FOREST_DURABLE_CHECKSUM_DOMAIN_V2);
    hasher.update(&bytes[..LANE_FOREST_DURABLE_CHECKSUM_OFFSET_V2]);
    hasher.update([0u8; 32]);
    hasher.update(&bytes[LANE_FOREST_DURABLE_HEADER_BYTES_V2..]);
    Ok(hasher.finalize().into())
}

pub struct DurableLaneForestWalletFileV2 {
    file: AtomicStateFileV1,
    state: LaneForestDurableStateV2,
}

impl DurableLaneForestWalletFileV2 {
    pub fn open_or_create_v2(
        path: impl AsRef<Path>,
        initial: LaneForestDurableStateV2,
    ) -> Result<Self, LaneForestDurableErrorV2> {
        let file = AtomicStateFileV1::acquire(path.as_ref())?;
        let state = match file.read_optional()? {
            Some(bytes) => {
                let stored = decode_lane_forest_durable_state_v2(&bytes)?;
                if stored.program_id != initial.program_id
                    || stored.core.master.address != initial.core.master.address
                {
                    return Err(LaneForestDurableErrorV2::IdentityMismatch);
                }
                stored
            }
            None => {
                file.replace(&encode_lane_forest_durable_state_v2(&initial)?)?;
                initial
            }
        };
        Ok(Self { file, state })
    }

    pub fn state(&self) -> &LaneForestDurableStateV2 {
        &self.state
    }

    pub fn replace_state_v2(
        &mut self,
        candidate: LaneForestDurableStateV2,
    ) -> Result<(), LaneForestDurableErrorV2> {
        if candidate.program_id != self.state.program_id
            || candidate.core.master.address != self.state.core.master.address
        {
            return Err(LaneForestDurableErrorV2::IdentityMismatch);
        }
        let bytes = encode_lane_forest_durable_state_v2(&candidate)?;
        self.file.replace(&bytes)?;
        self.state = candidate;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_statement::pool_v1::{PoolIdentityV1, VerifierPolicyV1, POOL_V1_PAIR_TREE_DEPTH};
    use core::convert::Infallible;
    use hpke::rand_core::{TryCryptoRng, TryRng};

    use crate::{
        derive_viewing_keypair_v1, encrypt_note_v1, recompute_note_commitment_v1, NoteOpeningV1,
    };

    struct FixedTestRng(u8);

    impl TryRng for FixedTestRng {
        type Error = Infallible;

        fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Self::Error> {
            for byte in dest {
                *byte = self.0;
                self.0 = self.0.wrapping_add(1);
            }
            Ok(())
        }

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
    }

    impl TryCryptoRng for FixedTestRng {}

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32 + 1))
    }

    fn event(slot: u64, instruction: u16, event_index: u16) -> DepositEventIdV1 {
        DepositEventIdV1::new(
            FinalizedChainPointV1::new(slot, [slot as u8 + 1; 32]).unwrap(),
            [slot as u8 + 2; 64],
            instruction,
            event_index,
        )
        .unwrap()
    }

    fn master_value(master: Pubkey, mint: Pubkey) -> PoolV1PairForestMasterV1 {
        PoolV1PairForestMasterV1 {
            identity: PoolIdentityV1 {
                pool: master.to_bytes(),
                asset_mint: mint.to_bytes(),
                token_program: [3u8; 32],
                asset_id: M31(4),
                deployment_domain: [5u8; 32],
            },
            verifier_policy: VerifierPolicyV1 {
                flags: 1,
                registry_program: [6u8; 32],
                registry_authority: [0u8; 32],
                policy_binding: [7u8; 32],
            },
            initialized_lane_mask: POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
            has_checkpoint: false,
            next_checkpoint_sequence: 0,
            last_checkpoint_lane_sequences: [0u64; 8],
        }
    }

    fn empty_lane(master: Pubkey, lane_id: u8) -> PoolV1PairForestLaneStateV1 {
        PoolV1PairForestLaneStateV1 {
            master: master.to_bytes(),
            lane_id,
            tree: IncrementalMerkleTreeV1 {
                next_leaf_index: 0,
                root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
                frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
            },
        }
    }

    fn fixtures() -> (
        Pubkey,
        Pubkey,
        PoolV1PairForestMasterV1,
        Vec<([u8; 32], Vec<u8>)>,
        LaneForestDurableStateV2,
    ) {
        let program = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let master = pool_v1_pair_forest_master_address(&program, &mint).0;
        let value = master_value(master, mint);
        let master_image = encode_pool_v1_pair_forest_master_v1(&value).unwrap();
        let lanes = (0..8u8)
            .map(|lane_id| {
                let address = pool_v1_pair_forest_lane_address(&program, &master, lane_id)
                    .unwrap()
                    .0;
                let image = encode_pool_v1_pair_forest_lane_state_v1(
                    &empty_lane(master, lane_id),
                    &POOL_V1_PAIR_EMPTY_ROOTS,
                )
                .unwrap();
                (address.to_bytes(), image.to_vec())
            })
            .collect::<Vec<_>>();
        let state = LaneForestDurableStateV2::from_authenticated_accounts_v2(
            program.to_bytes(),
            master.to_bytes(),
            &master_image,
            &lanes,
            None,
        )
        .unwrap();
        (program, master, value, lanes, state)
    }

    fn after_lane_for_leaf(
        state: &LaneForestDurableStateV2,
        lane_id: LaneIdV2,
        pair_leaf: Digest,
    ) -> ([u8; 32], [u8; POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES]) {
        let lane = state.core.lanes[lane_id.index()].account;
        let next = lane
            .value
            .tree
            .append_one_with_empty_roots(pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
            .unwrap()
            .0;
        let value = PoolV1PairForestLaneStateV1 {
            tree: next,
            ..lane.value
        };
        (
            lane.address,
            encode_pool_v1_pair_forest_lane_state_v1(&value, &POOL_V1_PAIR_EMPTY_ROOTS).unwrap(),
        )
    }

    fn deposit_event(
        state: &LaneForestDurableStateV2,
        id: DepositEventIdV1,
        commitment: [u8; 32],
        payload: Option<[u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES]>,
    ) -> ForestFinalizedAppendEventV2 {
        let commitment_digest = decode_digest_canonical(&commitment).unwrap();
        let lane_id = LaneIdV2::new(encode_digest_canonical(&commitment_digest)[0] & 7).unwrap();
        let pair_leaf = PoolV1PairLeafWitnessV1::single_output(commitment_digest)
            .unwrap()
            .leaf_digest()
            .unwrap();
        let (address, image) = after_lane_for_leaf(state, lane_id, pair_leaf);
        let index = state.core.lanes[lane_id.index()]
            .account
            .value
            .tree
            .next_leaf_index;
        ForestFinalizedAppendEventV2 {
            master: state.core.master.address,
            lane_id,
            pair_leaf_index: index,
            root_sequence: index + 1,
            after_lane_address: address,
            after_lane_image: image,
            kind: ForestFinalizedAppendKindV2::Deposit {
                event_id: id,
                commitment,
                encrypted_note: payload,
            },
        }
    }

    fn checkpoint_inputs(
        state: &LaneForestDurableStateV2,
    ) -> (
        [u8; 32],
        [u8; POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES],
        Vec<([u8; 32], Vec<u8>)>,
        [u8; 32],
        [u8; POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES],
    ) {
        let sequences = state
            .core
            .lanes
            .each_ref()
            .map(|lane| lane.account.value.tree.next_leaf_index);
        let roots = state
            .core
            .lanes
            .each_ref()
            .map(|lane| encode_digest_canonical(&lane.account.value.tree.root));
        let global_root =
            decode_digest_canonical(&lane_forest_global_root_v2(&roots).unwrap()).unwrap();
        let checkpoint = PoolV1PairForestCheckpointV1 {
            master: state.core.master.address,
            deployment_domain: state.core.master.value.identity.deployment_domain,
            checkpoint_sequence: state.core.master.value.next_checkpoint_sequence,
            global_root,
            lane_sequences: sequences,
        };
        let checkpoint_address = pool_v1_pair_forest_checkpoint_address(
            &Pubkey::new_from_array(state.program_id),
            &Pubkey::new_from_array(state.core.master.address),
            checkpoint.checkpoint_sequence,
        )
        .0
        .to_bytes();
        let next_master = PoolV1PairForestMasterV1 {
            has_checkpoint: true,
            next_checkpoint_sequence: checkpoint.checkpoint_sequence + 1,
            last_checkpoint_lane_sequences: sequences,
            ..state.core.master.value
        };
        (
            state.core.master.address,
            encode_pool_v1_pair_forest_master_v1(&next_master).unwrap(),
            state
                .core
                .lanes
                .iter()
                .map(|lane| (lane.account.address, lane.account.image.to_vec()))
                .collect(),
            checkpoint_address,
            encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint).unwrap(),
        )
    }

    #[test]
    fn committed_account_codecs_and_all_lane_page_pdas_are_exact() {
        let (program, master, value, lanes, state) = fixtures();
        let master_image = encode_pool_v1_pair_forest_master_v1(&value).unwrap();
        assert_eq!(
            authenticate_forest_master_account_v2(
                program.to_bytes(),
                master.to_bytes(),
                &master_image
            )
            .unwrap()
            .value,
            value
        );
        assert_eq!(
            authenticate_forest_master_account_v2(
                program.to_bytes(),
                Pubkey::new_unique().to_bytes(),
                &master_image
            ),
            Err(LaneForestDurableErrorV2::InvalidMasterAddress)
        );
        let cursors = state.lane_page_cursors_v2().unwrap();
        let unique = cursors
            .iter()
            .map(|cursor| cursor.address)
            .collect::<HashSet<_>>();
        assert_eq!(unique.len(), 8);
        for (index, cursor) in cursors.iter().enumerate() {
            assert_eq!(cursor.lane_id.index(), index);
            assert_eq!(cursor.page_number, 0);
            assert_eq!(cursor.root_sequence, 0);
            assert_eq!(
                authenticate_forest_lane_account_v2(
                    program.to_bytes(),
                    master.to_bytes(),
                    cursor.lane_id,
                    lanes[index].0,
                    &lanes[index].1,
                )
                .unwrap()
                .value
                .lane_id as usize,
                index
            );
        }
        assert_eq!(
            LaneForestDurableStateV2::from_authenticated_accounts_v2(
                program.to_bytes(),
                master.to_bytes(),
                &master_image,
                &lanes[..7],
                None,
            ),
            Err(LaneForestDurableErrorV2::LaneOrderMismatch)
        );
        let mut aliased = lanes.clone();
        aliased[1] = aliased[0].clone();
        assert_eq!(
            LaneForestDurableStateV2::from_authenticated_accounts_v2(
                program.to_bytes(),
                master.to_bytes(),
                &master_image,
                &aliased,
                None,
            ),
            Err(LaneForestDurableErrorV2::LaneAlias)
        );
    }

    #[test]
    fn event_wire_round_trips_and_rejects_legacy_two_append_claim() {
        let (_, _, _, _, state) = fixtures();
        let event = deposit_event(
            &state,
            event(10, 1, 0),
            encode_digest_canonical(&digest(50)),
            None,
        );
        let wire = encode_forest_finalized_append_event_v2(&event).unwrap();
        assert_eq!(
            decode_forest_finalized_append_event_v2(&wire).unwrap(),
            event
        );
        let mut trailing = wire.clone();
        trailing.push(0);
        assert_eq!(
            decode_forest_finalized_append_event_v2(&trailing),
            Err(LaneForestDurableErrorV2::WrongLength)
        );
        let mut legacy = wire;
        legacy[360..368].copy_from_slice(&(event.root_sequence + 1).to_le_bytes());
        assert_eq!(
            decode_forest_finalized_append_event_v2(&legacy),
            Err(LaneForestDurableErrorV2::InvalidEvent)
        );
        let mut malformed_after = event;
        malformed_after.after_lane_image[0] ^= 1;
        assert_eq!(
            encode_forest_finalized_append_event_v2(&malformed_after),
            Err(LaneForestDurableErrorV2::InvalidEvent)
        );
    }

    #[test]
    fn preauthenticated_local_note_selection_updates_the_same_witness_candidate() {
        let (_, _, _, _, mut state) = fixtures();
        let output_id = event(19, 1, 0);
        let append = deposit_event(
            &state,
            output_id,
            encode_digest_canonical(&digest(49)),
            None,
        );
        let lane_id = append.lane_id;
        let before = state.clone();
        assert_eq!(
            state.ingest_finalized_append_preselected_v2(append.clone(), &[event(19, 2, 0)],),
            Err(LaneForestDurableErrorV2::InvalidEvent)
        );
        assert_eq!(state, before);

        state
            .ingest_finalized_append_preselected_v2(append.clone(), &[output_id])
            .unwrap();
        assert_eq!(state.tracked_outputs(lane_id).len(), 1);
        assert_eq!(state.lane(lane_id).1.tracked().len(), 1);
        state
            .ingest_finalized_append_preselected_v2(append.clone(), &[output_id])
            .unwrap();
        assert_eq!(state.tracked_outputs(lane_id).len(), 1);
        assert_eq!(
            state.ingest_finalized_append_preselected_v2(append, &[]),
            Err(LaneForestDurableErrorV2::DuplicateEvent)
        );
        assert_eq!(state.tracked_outputs(lane_id).len(), 1);
    }

    #[test]
    fn encrypted_deposit_hook_tracks_pair_witness_and_private_transfer_is_one_append() {
        let (_, _, _, _, mut state) = fixtures();
        let (secret, public) = derive_viewing_keypair_v1(&[0x42; 32]).unwrap();
        let note = NoteOpeningV1::new(
            encode_digest_canonical(&digest(100)),
            7,
            4,
            encode_digest_canonical(&digest(200)),
        )
        .unwrap();
        let commitment = recompute_note_commitment_v1(&note).unwrap();
        let lane_id = LaneIdV2::new(commitment[0] & 7).unwrap();
        let context = NoteContextV1::new(
            state.core.master.address,
            state.core.master.value.identity.deployment_domain,
            0,
            commitment,
        )
        .unwrap();
        let payload = encrypt_note_v1(&mut FixedTestRng(9), &public, &context, &note).unwrap();
        let deposit = deposit_event(&state, event(20, 1, 0), commitment, Some(payload));
        let outcomes = state
            .ingest_finalized_append_v2(deposit, Some(&secret))
            .unwrap();
        assert!(matches!(
            outcomes[0].outcome,
            ForestNoteAssociationOutcomeV2::Recovered(_)
        ));
        assert_eq!(state.lane(lane_id).1.tracked().len(), 1);

        let nullifier = encode_digest_canonical(&digest(301));
        let output_lane = LaneIdV2::new(nullifier[0] & 7).unwrap();
        let recipient = encode_digest_canonical(&digest(401));
        let change = encode_digest_canonical(&digest(501));
        let pair_leaf = PoolV1PairLeafWitnessV1::two_outputs(
            decode_digest_canonical(&recipient).unwrap(),
            decode_digest_canonical(&change).unwrap(),
        )
        .unwrap()
        .leaf_digest()
        .unwrap();
        let before = state.core.lanes[output_lane.index()]
            .account
            .value
            .tree
            .next_leaf_index;
        let (address, image) = after_lane_for_leaf(&state, output_lane, pair_leaf);
        let transfer = ForestFinalizedAppendEventV2 {
            master: state.core.master.address,
            lane_id: output_lane,
            pair_leaf_index: before,
            root_sequence: before + 1,
            after_lane_address: address,
            after_lane_image: image,
            kind: ForestFinalizedAppendKindV2::PrivateTransfer {
                recipient_event_id: event(21, 2, 0),
                change_event_id: event(21, 2, 1),
                nullifier,
                recipient_commitment: recipient,
                change_commitment: change,
                recipient_encrypted_note: None,
                change_encrypted_note: None,
            },
        };
        let wire = encode_forest_finalized_append_event_v2(&transfer).unwrap();
        let transfer = decode_forest_finalized_append_event_v2(&wire).unwrap();
        state.ingest_finalized_append_v2(transfer, None).unwrap();
        assert_eq!(
            state.core.lanes[output_lane.index()]
                .account
                .value
                .tree
                .next_leaf_index,
            before + 1
        );
    }

    #[test]
    fn checkpoint_durable_roundtrip_and_finalized_rollback_is_rejected() {
        let (_, _, _, _, mut state) = fixtures();
        let first = deposit_event(
            &state,
            event(30, 1, 0),
            encode_digest_canonical(&digest(601)),
            None,
        );
        state.ingest_finalized_append_v2(first, None).unwrap();
        let (master_address, master_image, lanes, checkpoint_address, checkpoint_image) =
            checkpoint_inputs(&state);
        state
            .ingest_finalized_checkpoint_v2(
                FinalizedChainPointV1::new(31, [32; 32]).unwrap(),
                master_address,
                &master_image,
                &lanes,
                checkpoint_address,
                &checkpoint_image,
            )
            .unwrap();
        let at_checkpoint = state.clone();
        let encoded = encode_lane_forest_durable_state_v2(&state).unwrap();
        assert_eq!(
            decode_lane_forest_durable_state_v2(&encoded).unwrap(),
            state
        );
        let mut tampered = encoded;
        *tampered.last_mut().unwrap() ^= 1;
        assert_eq!(
            decode_lane_forest_durable_state_v2(&tampered),
            Err(LaneForestDurableErrorV2::ChecksumMismatch)
        );

        let second = deposit_event(
            &state,
            event(32, 1, 0),
            encode_digest_canonical(&digest(701)),
            None,
        );
        state.ingest_finalized_append_v2(second, None).unwrap();
        let after_second = state.clone();
        assert_eq!(
            state.rollback_to_finalized_checkpoint_v2(0),
            Err(LaneForestDurableErrorV2::InvalidRollback)
        );
        assert_eq!(state, after_second);
        assert_ne!(state, at_checkpoint);
    }

    #[test]
    fn atomic_file_reopens_and_replaces_the_exact_durable_forest() {
        let (_, _, _, _, initial) = fixtures();
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "aspis-eight-lane-durable-v2-{}-{nonce}.bin",
            std::process::id()
        ));
        let lock_path = path.with_file_name(format!(
            "{}.lock",
            path.file_name().unwrap().to_string_lossy()
        ));
        let mut advanced = initial.clone();
        advanced
            .ingest_finalized_append_v2(
                deposit_event(
                    &advanced,
                    event(40, 1, 0),
                    encode_digest_canonical(&digest(801)),
                    None,
                ),
                None,
            )
            .unwrap();
        {
            let mut file =
                DurableLaneForestWalletFileV2::open_or_create_v2(&path, initial.clone()).unwrap();
            assert_eq!(file.state(), &initial);
            file.replace_state_v2(advanced.clone()).unwrap();
            assert_eq!(file.state(), &advanced);
        }
        {
            let file = DurableLaneForestWalletFileV2::open_or_create_v2(&path, initial).unwrap();
            assert_eq!(file.state(), &advanced);
        }
        std::fs::remove_file(&path).unwrap();
        std::fs::remove_file(&lock_path).unwrap();
    }
}
