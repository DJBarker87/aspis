//! Default-off finalized RPC adapter for the eight-lane pair forest.
//!
//! The compact `ASF8` append image below is the frozen wallet-side consumer
//! ABI. No deployed Pool instruction emits it yet. Production activation must
//! therefore wait for a separately reviewed program emitter; this module never
//! synthesizes an event from unauthenticated logs. Given authenticated event
//! bytes and one coherent finalized account snapshot, ingestion is staged in a
//! cloned durable state and persisted once.
//!
//! The existing relayer execution journal is a separate atomic file and this
//! consumer ABI has no authenticated relayer request identifier. Cross-file
//! atomic coordination is therefore not claimed: withdrawals are returned to
//! the caller for later correlation once the producer ABI supplies that link.

use aspis_pool::POOL_V1_PAIR_EMPTY_ROOTS;
use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{
        encode_pool_v1_pair_forest_lane_state_v1,
        root_history::{read_root_history_page_root_v1, validate_root_history_page_bytes_v1},
        PoolV1PairForestLaneStateV1, PoolV1PairLeafWitnessV1, PoolV1RootHistoryError,
        POOL_V1_PAIR_CAPACITY, POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES,
        POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES,
        POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
    },
};

use crate::{
    finalized_indexer::SolanaRpcCommitmentV1,
    lane_forest_durable_v2::{
        canonical_lane_root_page_cursor_v2, DurableLaneForestWalletFileV2,
        ForestFinalizedAppendEventV2, ForestFinalizedAppendKindV2, ForestNoteAssociationV2,
        LaneForestDurableErrorV2, LaneForestDurableStateV2,
    },
    lane_forest_v2::{LaneIdV2, POOL_V1_LANE_COUNT_V2},
    scan_state::{DepositEventIdV1, FinalizedChainPointV1},
    ViewingSecretKeyV1, POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES,
};

pub type ForestRpcCommitmentV2 = SolanaRpcCommitmentV1;

pub const PAIR_FOREST_PROGRAM_EVENT_MAGIC_V2: [u8; 4] = *b"ASF8";
pub const PAIR_FOREST_PROGRAM_EVENT_VERSION_V2: u8 = 2;
pub const PAIR_FOREST_PROGRAM_EVENT_HEADER_BYTES_V2: usize = 232;
pub const PAIR_FOREST_PROGRAM_EVENT_DEPOSIT_V2: u8 = 1;
pub const PAIR_FOREST_PROGRAM_EVENT_PRIVATE_TRANSFER_V2: u8 = 2;
pub const PAIR_FOREST_PROGRAM_EVENT_WITHDRAWAL_V2: u8 = 3;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LaneForestRpcErrorV2 {
    NotFinalized,
    ContextTooOld,
    WrongProgram,
    ExecutableAccount,
    WrongAccountCount,
    WrongAccountOwner,
    WrongEventLength,
    WrongEventMagic,
    WrongEventVersion,
    WrongEventKind,
    NonZeroReserved,
    InvalidEvent,
    EventOrder,
    EventPointMismatch,
    ReplayMismatch,
    InvalidChainLink,
    UnretainedFork,
    MissingCheckpoint,
    UnexpectedCheckpoint,
    MissingRootPage,
    WrongRootPage,
    RootPage(PoolV1RootHistoryError),
    Durable(LaneForestDurableErrorV2),
}

impl From<LaneForestDurableErrorV2> for LaneForestRpcErrorV2 {
    fn from(error: LaneForestDurableErrorV2) -> Self {
        Self::Durable(error)
    }
}

impl From<PoolV1RootHistoryError> for LaneForestRpcErrorV2 {
    fn from(error: PoolV1RootHistoryError) -> Self {
        Self::RootPage(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PairForestProgramEventKindV2 {
    Deposit {
        commitment: [u8; 32],
        encrypted_note: Option<[u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES]>,
    },
    PrivateTransfer {
        nullifier: [u8; 32],
        recipient_commitment: [u8; 32],
        change_commitment: [u8; 32],
        recipient_encrypted_note: Option<[u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES]>,
        change_encrypted_note: Option<[u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES]>,
    },
    Withdrawal {
        nullifier: [u8; 32],
        change_commitment: [u8; 32],
        destination_token_account: [u8; 32],
        amount: u32,
        encrypted_note: Option<[u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES]>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairForestProgramEventV2 {
    pub master: [u8; 32],
    pub pair_leaf_index: u64,
    pub root_sequence: u64,
    pub after_lane_root: [u8; 32],
    pub kind: PairForestProgramEventKindV2,
}

fn canonical_digest_v2(bytes: &[u8; 32]) -> Result<(), LaneForestRpcErrorV2> {
    decode_digest_canonical(bytes)
        .map(|_| ())
        .map_err(|_| LaneForestRpcErrorV2::InvalidEvent)
}

pub fn encode_pair_forest_program_event_v2(
    event: &PairForestProgramEventV2,
) -> Result<Vec<u8>, LaneForestRpcErrorV2> {
    if event.master == [0u8; 32]
        || event.pair_leaf_index >= POOL_V1_PAIR_CAPACITY
        || event.root_sequence != event.pair_leaf_index + 1
    {
        return Err(LaneForestRpcErrorV2::InvalidEvent);
    }
    canonical_digest_v2(&event.after_lane_root)?;
    let (kind, route, first, second, destination, amount, first_payload, second_payload) =
        match &event.kind {
            PairForestProgramEventKindV2::Deposit {
                commitment,
                encrypted_note,
            } => (
                PAIR_FOREST_PROGRAM_EVENT_DEPOSIT_V2,
                *commitment,
                *commitment,
                [0u8; 32],
                [0u8; 32],
                0,
                encrypted_note.as_ref(),
                None,
            ),
            PairForestProgramEventKindV2::PrivateTransfer {
                nullifier,
                recipient_commitment,
                change_commitment,
                recipient_encrypted_note,
                change_encrypted_note,
            } => (
                PAIR_FOREST_PROGRAM_EVENT_PRIVATE_TRANSFER_V2,
                *nullifier,
                *recipient_commitment,
                *change_commitment,
                [0u8; 32],
                0,
                recipient_encrypted_note.as_ref(),
                change_encrypted_note.as_ref(),
            ),
            PairForestProgramEventKindV2::Withdrawal {
                nullifier,
                change_commitment,
                destination_token_account,
                amount,
                encrypted_note,
            } => {
                if *destination_token_account == [0u8; 32] || *amount == 0 {
                    return Err(LaneForestRpcErrorV2::InvalidEvent);
                }
                (
                    PAIR_FOREST_PROGRAM_EVENT_WITHDRAWAL_V2,
                    *nullifier,
                    *change_commitment,
                    [0u8; 32],
                    *destination_token_account,
                    *amount,
                    encrypted_note.as_ref(),
                    None,
                )
            }
        };
    canonical_digest_v2(&route)?;
    canonical_digest_v2(&first)?;
    if kind == PAIR_FOREST_PROGRAM_EVENT_PRIVATE_TRANSFER_V2 {
        canonical_digest_v2(&second)?;
    }
    let payload_count =
        usize::from(first_payload.is_some()) + usize::from(second_payload.is_some());
    let mut output = vec![
        0u8;
        PAIR_FOREST_PROGRAM_EVENT_HEADER_BYTES_V2
            + payload_count * POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES
    ];
    output[..4].copy_from_slice(&PAIR_FOREST_PROGRAM_EVENT_MAGIC_V2);
    output[4] = PAIR_FOREST_PROGRAM_EVENT_VERSION_V2;
    output[5] = kind;
    output[6] = u8::from(first_payload.is_some()) | (u8::from(second_payload.is_some()) << 1);
    output[8..40].copy_from_slice(&event.master);
    output[40..72].copy_from_slice(&route);
    output[72..104].copy_from_slice(&first);
    output[104..136].copy_from_slice(&second);
    output[136..144].copy_from_slice(&event.pair_leaf_index.to_le_bytes());
    output[144..152].copy_from_slice(&event.root_sequence.to_le_bytes());
    output[152..184].copy_from_slice(&event.after_lane_root);
    output[184..216].copy_from_slice(&destination);
    output[216..220].copy_from_slice(&amount.to_le_bytes());
    output[220..222].copy_from_slice(
        &(first_payload.map_or(0, |_| POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES as u16)).to_le_bytes(),
    );
    output[222..224].copy_from_slice(
        &(second_payload.map_or(0, |_| POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES as u16)).to_le_bytes(),
    );
    let mut offset = PAIR_FOREST_PROGRAM_EVENT_HEADER_BYTES_V2;
    if let Some(payload) = first_payload {
        output[offset..offset + payload.len()].copy_from_slice(payload);
        offset += payload.len();
    }
    if let Some(payload) = second_payload {
        output[offset..offset + payload.len()].copy_from_slice(payload);
    }
    Ok(output)
}

pub fn decode_pair_forest_program_event_v2(
    bytes: &[u8],
) -> Result<PairForestProgramEventV2, LaneForestRpcErrorV2> {
    if bytes.len() < PAIR_FOREST_PROGRAM_EVENT_HEADER_BYTES_V2 {
        return Err(LaneForestRpcErrorV2::WrongEventLength);
    }
    if bytes[..4] != PAIR_FOREST_PROGRAM_EVENT_MAGIC_V2 {
        return Err(LaneForestRpcErrorV2::WrongEventMagic);
    }
    if bytes[4] != PAIR_FOREST_PROGRAM_EVENT_VERSION_V2 {
        return Err(LaneForestRpcErrorV2::WrongEventVersion);
    }
    if bytes[7] != 0 || bytes[224..232].iter().any(|byte| *byte != 0) {
        return Err(LaneForestRpcErrorV2::NonZeroReserved);
    }
    let flags = bytes[6];
    if flags & !3 != 0 {
        return Err(LaneForestRpcErrorV2::InvalidEvent);
    }
    let first_len = usize::from(u16::from_le_bytes(bytes[220..222].try_into().unwrap()));
    let second_len = usize::from(u16::from_le_bytes(bytes[222..224].try_into().unwrap()));
    for (present, length) in [(flags & 1 != 0, first_len), (flags & 2 != 0, second_len)] {
        if length
            != if present {
                POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES
            } else {
                0
            }
        {
            return Err(LaneForestRpcErrorV2::WrongEventLength);
        }
    }
    if bytes.len() != PAIR_FOREST_PROGRAM_EVENT_HEADER_BYTES_V2 + first_len + second_len {
        return Err(LaneForestRpcErrorV2::WrongEventLength);
    }
    let first_payload = (first_len != 0).then(|| {
        bytes[PAIR_FOREST_PROGRAM_EVENT_HEADER_BYTES_V2
            ..PAIR_FOREST_PROGRAM_EVENT_HEADER_BYTES_V2 + first_len]
            .try_into()
            .unwrap()
    });
    let second_payload = (second_len != 0).then(|| {
        bytes[PAIR_FOREST_PROGRAM_EVENT_HEADER_BYTES_V2 + first_len..]
            .try_into()
            .unwrap()
    });
    let route: [u8; 32] = bytes[40..72].try_into().unwrap();
    let first: [u8; 32] = bytes[72..104].try_into().unwrap();
    let second: [u8; 32] = bytes[104..136].try_into().unwrap();
    let destination: [u8; 32] = bytes[184..216].try_into().unwrap();
    let amount = u32::from_le_bytes(bytes[216..220].try_into().unwrap());
    let kind = match bytes[5] {
        PAIR_FOREST_PROGRAM_EVENT_DEPOSIT_V2 => {
            if route != first
                || second != [0u8; 32]
                || destination != [0u8; 32]
                || amount != 0
                || second_payload.is_some()
            {
                return Err(LaneForestRpcErrorV2::InvalidEvent);
            }
            PairForestProgramEventKindV2::Deposit {
                commitment: first,
                encrypted_note: first_payload,
            }
        }
        PAIR_FOREST_PROGRAM_EVENT_PRIVATE_TRANSFER_V2 => {
            if destination != [0u8; 32] || amount != 0 {
                return Err(LaneForestRpcErrorV2::InvalidEvent);
            }
            PairForestProgramEventKindV2::PrivateTransfer {
                nullifier: route,
                recipient_commitment: first,
                change_commitment: second,
                recipient_encrypted_note: first_payload,
                change_encrypted_note: second_payload,
            }
        }
        PAIR_FOREST_PROGRAM_EVENT_WITHDRAWAL_V2 => {
            if second != [0u8; 32]
                || destination == [0u8; 32]
                || amount == 0
                || second_payload.is_some()
            {
                return Err(LaneForestRpcErrorV2::InvalidEvent);
            }
            PairForestProgramEventKindV2::Withdrawal {
                nullifier: route,
                change_commitment: first,
                destination_token_account: destination,
                amount,
                encrypted_note: first_payload,
            }
        }
        _ => return Err(LaneForestRpcErrorV2::WrongEventKind),
    };
    let event = PairForestProgramEventV2 {
        master: bytes[8..40].try_into().unwrap(),
        pair_leaf_index: u64::from_le_bytes(bytes[136..144].try_into().unwrap()),
        root_sequence: u64::from_le_bytes(bytes[144..152].try_into().unwrap()),
        after_lane_root: bytes[152..184].try_into().unwrap(),
        kind,
    };
    encode_pair_forest_program_event_v2(&event)?;
    Ok(event)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedForestAccountV2 {
    pub address: [u8; 32],
    pub owner: [u8; 32],
    pub executable: bool,
    pub data: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedForestRootPageV2 {
    pub lane_id: LaneIdV2,
    pub page_number: u64,
    pub account: FinalizedForestAccountV2,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedForestAccountSnapshotV2 {
    pub asserted_commitment: ForestRpcCommitmentV2,
    pub context_slot: u64,
    pub master: FinalizedForestAccountV2,
    pub lanes: Vec<FinalizedForestAccountV2>,
    /// Present only when this batch observes a newly advanced master.
    pub new_checkpoint: Option<FinalizedForestAccountV2>,
    pub current_root_pages: Vec<FinalizedForestRootPageV2>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedForestEventObservationV2 {
    pub transaction_index: u32,
    pub event_id: DepositEventIdV1,
    pub emitting_program: [u8; 32],
    pub event_bytes: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedForestRpcBatchV2 {
    pub asserted_commitment: ForestRpcCommitmentV2,
    pub point: FinalizedChainPointV1,
    pub parent: FinalizedChainPointV1,
    pub observations: Vec<FinalizedForestEventObservationV2>,
    pub accounts: FinalizedForestAccountSnapshotV2,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FinalizedForestIngestStatusV2 {
    Advanced,
    Replayed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedForestWithdrawalObservationV2 {
    pub event_id: DepositEventIdV1,
    pub nullifier: [u8; 32],
    pub destination_token_account: [u8; 32],
    pub amount: u32,
}

pub struct FinalizedForestIngestResultV2 {
    pub status: FinalizedForestIngestStatusV2,
    pub rolled_back_checkpoint_sequence: Option<u64>,
    pub note_associations: Vec<ForestNoteAssociationV2>,
    pub withdrawals: Vec<FinalizedForestWithdrawalObservationV2>,
}

fn require_program_account_v2(
    account: &FinalizedForestAccountV2,
    program_id: [u8; 32],
) -> Result<(), LaneForestRpcErrorV2> {
    if account.owner != program_id {
        return Err(LaneForestRpcErrorV2::WrongAccountOwner);
    }
    if account.executable {
        return Err(LaneForestRpcErrorV2::ExecutableAccount);
    }
    Ok(())
}

fn second_event_id_v2(first: DepositEventIdV1) -> Result<DepositEventIdV1, LaneForestRpcErrorV2> {
    DepositEventIdV1::new(
        first.point(),
        *first.transaction_signature(),
        first.instruction_index(),
        first
            .event_index()
            .checked_add(1)
            .ok_or(LaneForestRpcErrorV2::InvalidEvent)?,
    )
    .map_err(|_| LaneForestRpcErrorV2::InvalidEvent)
}

fn durable_event_from_program_v2(
    state: &LaneForestDurableStateV2,
    event_id: DepositEventIdV1,
    event: PairForestProgramEventV2,
) -> Result<
    (
        ForestFinalizedAppendEventV2,
        Option<FinalizedForestWithdrawalObservationV2>,
    ),
    LaneForestRpcErrorV2,
> {
    if event.master != state.master().address {
        return Err(LaneForestRpcErrorV2::InvalidEvent);
    }
    let (route, pair_leaf, durable_kind, withdrawal) = match event.kind {
        PairForestProgramEventKindV2::Deposit {
            commitment,
            encrypted_note,
        } => {
            let commitment_digest = decode_digest_canonical(&commitment)
                .map_err(|_| LaneForestRpcErrorV2::InvalidEvent)?;
            (
                commitment,
                PoolV1PairLeafWitnessV1::single_output(commitment_digest)
                    .map_err(|_| LaneForestRpcErrorV2::InvalidEvent)?
                    .leaf_digest()
                    .map_err(|_| LaneForestRpcErrorV2::InvalidEvent)?,
                ForestFinalizedAppendKindV2::Deposit {
                    event_id,
                    commitment,
                    encrypted_note,
                },
                None,
            )
        }
        PairForestProgramEventKindV2::PrivateTransfer {
            nullifier,
            recipient_commitment,
            change_commitment,
            recipient_encrypted_note,
            change_encrypted_note,
        } => {
            let recipient = decode_digest_canonical(&recipient_commitment)
                .map_err(|_| LaneForestRpcErrorV2::InvalidEvent)?;
            let change = decode_digest_canonical(&change_commitment)
                .map_err(|_| LaneForestRpcErrorV2::InvalidEvent)?;
            (
                nullifier,
                PoolV1PairLeafWitnessV1::two_outputs(recipient, change)
                    .map_err(|_| LaneForestRpcErrorV2::InvalidEvent)?
                    .leaf_digest()
                    .map_err(|_| LaneForestRpcErrorV2::InvalidEvent)?,
                ForestFinalizedAppendKindV2::PrivateTransfer {
                    recipient_event_id: event_id,
                    change_event_id: second_event_id_v2(event_id)?,
                    nullifier,
                    recipient_commitment,
                    change_commitment,
                    recipient_encrypted_note,
                    change_encrypted_note,
                },
                None,
            )
        }
        PairForestProgramEventKindV2::Withdrawal {
            nullifier,
            change_commitment,
            destination_token_account,
            amount,
            encrypted_note,
        } => {
            let change = decode_digest_canonical(&change_commitment)
                .map_err(|_| LaneForestRpcErrorV2::InvalidEvent)?;
            (
                nullifier,
                PoolV1PairLeafWitnessV1::single_output(change)
                    .map_err(|_| LaneForestRpcErrorV2::InvalidEvent)?
                    .leaf_digest()
                    .map_err(|_| LaneForestRpcErrorV2::InvalidEvent)?,
                ForestFinalizedAppendKindV2::Withdrawal {
                    event_id,
                    nullifier,
                    change_commitment,
                    destination_token_account,
                    amount,
                    encrypted_note,
                },
                Some(FinalizedForestWithdrawalObservationV2 {
                    event_id,
                    nullifier,
                    destination_token_account,
                    amount,
                }),
            )
        }
    };
    let route = decode_digest_canonical(&route).map_err(|_| LaneForestRpcErrorV2::InvalidEvent)?;
    let lane_id = LaneIdV2::new(encode_digest_canonical(&route)[0] & 7)
        .map_err(|_| LaneForestRpcErrorV2::InvalidEvent)?;
    let (lane, _) = state.lane(lane_id);
    if lane.value.tree.next_leaf_index != event.pair_leaf_index {
        return Err(LaneForestRpcErrorV2::InvalidEvent);
    }
    let next_tree = lane
        .value
        .tree
        .append_one_with_empty_roots(pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
        .map_err(LaneForestDurableErrorV2::from)?
        .0;
    if next_tree.next_leaf_index != event.root_sequence
        || encode_digest_canonical(&next_tree.root) != event.after_lane_root
    {
        return Err(LaneForestRpcErrorV2::InvalidEvent);
    }
    let after_value = PoolV1PairForestLaneStateV1 {
        tree: next_tree,
        ..lane.value
    };
    let after_lane_image =
        encode_pool_v1_pair_forest_lane_state_v1(&after_value, &POOL_V1_PAIR_EMPTY_ROOTS)
            .map_err(LaneForestDurableErrorV2::from)?;
    Ok((
        ForestFinalizedAppendEventV2 {
            master: state.master().address,
            lane_id,
            pair_leaf_index: event.pair_leaf_index,
            root_sequence: event.root_sequence,
            after_lane_address: lane.address,
            after_lane_image,
            kind: durable_kind,
        },
        withdrawal,
    ))
}

fn validate_root_pages_v2(
    state: &LaneForestDurableStateV2,
    snapshot: &FinalizedForestAccountSnapshotV2,
) -> Result<(), LaneForestRpcErrorV2> {
    if snapshot.current_root_pages.len() != POOL_V1_LANE_COUNT_V2 {
        return Err(LaneForestRpcErrorV2::MissingRootPage);
    }
    for (index, page) in snapshot.current_root_pages.iter().enumerate() {
        let lane_id =
            LaneIdV2::new(index as u8).map_err(|_| LaneForestRpcErrorV2::WrongRootPage)?;
        if page.lane_id != lane_id {
            return Err(LaneForestRpcErrorV2::WrongRootPage);
        }
        require_program_account_v2(&page.account, *state.program_id())?;
        if page.account.data.len() != POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES {
            return Err(LaneForestRpcErrorV2::WrongRootPage);
        }
        let (lane, _) = state.lane(lane_id);
        let cursor = canonical_lane_root_page_cursor_v2(
            *state.program_id(),
            state.master().address,
            lane_id,
            lane.value.tree.next_leaf_index,
        )?;
        let header = validate_root_history_page_bytes_v1(&page.account.data)?;
        if page.page_number != cursor.page_number
            || page.account.address != cursor.address
            || header.pool != lane.address
            || header.page_number != cursor.page_number
            || read_root_history_page_root_v1(&page.account.data, lane.value.tree.next_leaf_index)?
                != lane.value.tree.root
        {
            return Err(LaneForestRpcErrorV2::WrongRootPage);
        }
    }
    Ok(())
}

fn validate_account_snapshot_v2(
    state: &LaneForestDurableStateV2,
    snapshot: &FinalizedForestAccountSnapshotV2,
) -> Result<(), LaneForestRpcErrorV2> {
    require_program_account_v2(&snapshot.master, *state.program_id())?;
    if snapshot.master.data.len() != POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES
        || snapshot.lanes.len() != POOL_V1_LANE_COUNT_V2
    {
        return Err(LaneForestRpcErrorV2::WrongAccountCount);
    }
    let mut lanes = Vec::with_capacity(POOL_V1_LANE_COUNT_V2);
    for lane in &snapshot.lanes {
        require_program_account_v2(lane, *state.program_id())?;
        if lane.data.len() != POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES {
            return Err(LaneForestRpcErrorV2::WrongAccountCount);
        }
        lanes.push((lane.address, lane.data.clone()));
    }
    state.validate_current_account_snapshot_v2(
        snapshot.master.address,
        &snapshot.master.data,
        &lanes,
    )?;
    validate_root_pages_v2(state, snapshot)
}

pub fn ingest_finalized_forest_rpc_batch_v2(
    wallet: &mut DurableLaneForestWalletFileV2,
    batch: &FinalizedForestRpcBatchV2,
    viewing_secret: Option<&ViewingSecretKeyV1>,
) -> Result<FinalizedForestIngestResultV2, LaneForestRpcErrorV2> {
    if batch.asserted_commitment != ForestRpcCommitmentV2::Finalized
        || batch.accounts.asserted_commitment != ForestRpcCommitmentV2::Finalized
    {
        return Err(LaneForestRpcErrorV2::NotFinalized);
    }
    if batch.accounts.context_slot < batch.point.slot() {
        return Err(LaneForestRpcErrorV2::ContextTooOld);
    }
    if batch.parent.slot() >= batch.point.slot() {
        return Err(LaneForestRpcErrorV2::InvalidChainLink);
    }
    let program_id = *wallet.state().program_id();
    let replay = wallet.state().finalized_head_v2() == Some(batch.point);
    let mut candidate = wallet.state().clone();
    let mut rolled_back_checkpoint_sequence = None;
    if !replay {
        if let Some(head) = candidate.finalized_head_v2() {
            if batch.parent != head {
                let checkpoint_sequence = candidate
                    .retained_checkpoint_sequence_at_point_v2(batch.parent)
                    .ok_or(LaneForestRpcErrorV2::UnretainedFork)?;
                candidate.rollback_to_finalized_checkpoint_v2(checkpoint_sequence)?;
                rolled_back_checkpoint_sequence = Some(checkpoint_sequence);
            }
        }
    }
    let mut previous_order = None;
    let mut decoded = Vec::with_capacity(batch.observations.len());
    for observation in &batch.observations {
        if observation.emitting_program != program_id {
            return Err(LaneForestRpcErrorV2::WrongProgram);
        }
        if observation.event_id.point() != batch.point || observation.event_id.event_index() != 0 {
            return Err(LaneForestRpcErrorV2::EventPointMismatch);
        }
        let order = (
            observation.transaction_index,
            observation.event_id.instruction_index(),
        );
        if previous_order.is_some_and(|previous| previous >= order) {
            return Err(LaneForestRpcErrorV2::EventOrder);
        }
        previous_order = Some(order);
        decoded.push((
            observation.event_id,
            decode_pair_forest_program_event_v2(&observation.event_bytes)?,
        ));
    }
    if replay {
        for (event_id, event) in &decoded {
            if !candidate.contains_event_id_v2(*event_id)
                || matches!(
                    event.kind,
                    PairForestProgramEventKindV2::PrivateTransfer { .. }
                ) && !candidate.contains_event_id_v2(second_event_id_v2(*event_id)?)
            {
                return Err(LaneForestRpcErrorV2::ReplayMismatch);
            }
        }
        if batch.accounts.new_checkpoint.is_some() {
            return Err(LaneForestRpcErrorV2::UnexpectedCheckpoint);
        }
        validate_account_snapshot_v2(&candidate, &batch.accounts)?;
        return Ok(FinalizedForestIngestResultV2 {
            status: FinalizedForestIngestStatusV2::Replayed,
            rolled_back_checkpoint_sequence: None,
            note_associations: Vec::new(),
            withdrawals: Vec::new(),
        });
    }

    let mut note_associations = Vec::new();
    let mut withdrawals = Vec::new();
    for (event_id, event) in decoded {
        let (event, withdrawal) = durable_event_from_program_v2(&candidate, event_id, event)?;
        note_associations.extend(candidate.ingest_finalized_append_v2(event, viewing_secret)?);
        withdrawals.extend(withdrawal);
    }

    let current_master_image = candidate.master().image;
    if batch.master_image_differs_v2(&current_master_image) {
        let checkpoint = batch
            .accounts
            .new_checkpoint
            .as_ref()
            .ok_or(LaneForestRpcErrorV2::MissingCheckpoint)?;
        require_program_account_v2(checkpoint, program_id)?;
        if checkpoint.data.len() != POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES {
            return Err(LaneForestRpcErrorV2::WrongAccountCount);
        }
        let lane_accounts = batch
            .accounts
            .lanes
            .iter()
            .map(|lane| (lane.address, lane.data.clone()))
            .collect::<Vec<_>>();
        candidate.ingest_finalized_checkpoint_v2(
            batch.point,
            batch.accounts.master.address,
            &batch.accounts.master.data,
            &lane_accounts,
            checkpoint.address,
            &checkpoint.data,
        )?;
    } else if batch.accounts.new_checkpoint.is_some() {
        return Err(LaneForestRpcErrorV2::UnexpectedCheckpoint);
    }
    validate_account_snapshot_v2(&candidate, &batch.accounts)?;
    candidate.set_finalized_head_v2(batch.point);
    wallet.replace_state_v2(candidate)?;
    Ok(FinalizedForestIngestResultV2 {
        status: FinalizedForestIngestStatusV2::Advanced,
        rolled_back_checkpoint_sequence,
        note_associations,
        withdrawals,
    })
}

impl FinalizedForestRpcBatchV2 {
    fn master_image_differs_v2(
        &self,
        current: &[u8; POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES],
    ) -> bool {
        self.accounts.master.data.as_slice() != current
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_pool::{
        pool_v1_pair_forest_checkpoint_address, pool_v1_pair_forest_lane_address,
        pool_v1_pair_forest_master_address,
    };
    use aspis_statement::pool_v1::{
        encode_pool_v1_pair_forest_checkpoint_v1, encode_pool_v1_pair_forest_master_v1,
        IncrementalMerkleTreeV1, PoolIdentityV1, PoolV1PairForestCheckpointV1,
        PoolV1PairForestMasterV1, RootHistoryPageV1, VerifierPolicyV1,
        POOL_V1_PAIR_FOREST_ALL_LANES_MASK, POOL_V1_PAIR_TREE_DEPTH,
    };
    use solana_program::pubkey::Pubkey;

    use crate::lane_forest_v2::lane_forest_global_root_v2;

    fn digest(seed: u32) -> [M31; 8] {
        core::array::from_fn(|index| M31(seed + 17 * index as u32 + 1))
    }

    fn point(slot: u64) -> FinalizedChainPointV1 {
        FinalizedChainPointV1::new(slot, [slot as u8 + 1; 32]).unwrap()
    }

    fn event_id(point: FinalizedChainPointV1, transaction: u8) -> DepositEventIdV1 {
        DepositEventIdV1::new(point, [transaction; 64], 1, 0).unwrap()
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

    fn fixture() -> (Pubkey, LaneForestDurableStateV2) {
        let program = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let master = pool_v1_pair_forest_master_address(&program, &mint).0;
        let master_image =
            encode_pool_v1_pair_forest_master_v1(&master_value(master, mint)).unwrap();
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
        (program, state)
    }

    fn program_event(
        state: &LaneForestDurableStateV2,
        kind: PairForestProgramEventKindV2,
    ) -> PairForestProgramEventV2 {
        let (route, leaf) = match &kind {
            PairForestProgramEventKindV2::Deposit { commitment, .. } => {
                let commitment = decode_digest_canonical(commitment).unwrap();
                (
                    encode_digest_canonical(&commitment),
                    PoolV1PairLeafWitnessV1::single_output(commitment)
                        .unwrap()
                        .leaf_digest()
                        .unwrap(),
                )
            }
            PairForestProgramEventKindV2::PrivateTransfer {
                nullifier,
                recipient_commitment,
                change_commitment,
                ..
            } => (
                *nullifier,
                PoolV1PairLeafWitnessV1::two_outputs(
                    decode_digest_canonical(recipient_commitment).unwrap(),
                    decode_digest_canonical(change_commitment).unwrap(),
                )
                .unwrap()
                .leaf_digest()
                .unwrap(),
            ),
            PairForestProgramEventKindV2::Withdrawal {
                nullifier,
                change_commitment,
                ..
            } => (
                *nullifier,
                PoolV1PairLeafWitnessV1::single_output(
                    decode_digest_canonical(change_commitment).unwrap(),
                )
                .unwrap()
                .leaf_digest()
                .unwrap(),
            ),
        };
        let lane_id = LaneIdV2::new(route[0] & 7).unwrap();
        let (lane, _) = state.lane(lane_id);
        let next = lane
            .value
            .tree
            .append_one_with_empty_roots(leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
            .unwrap()
            .0;
        PairForestProgramEventV2 {
            master: state.master().address,
            pair_leaf_index: lane.value.tree.next_leaf_index,
            root_sequence: next.next_leaf_index,
            after_lane_root: encode_digest_canonical(&next.root),
            kind,
        }
    }

    fn apply_program_event(
        state: &mut LaneForestDurableStateV2,
        id: DepositEventIdV1,
        event: PairForestProgramEventV2,
    ) {
        let (event, _) = durable_event_from_program_v2(state, id, event).unwrap();
        state.ingest_finalized_append_v2(event, None).unwrap();
    }

    fn snapshot(
        program: Pubkey,
        state: &LaneForestDurableStateV2,
        context_slot: u64,
        new_checkpoint: Option<FinalizedForestAccountV2>,
    ) -> FinalizedForestAccountSnapshotV2 {
        let lanes = (0..8u8)
            .map(|index| {
                let lane_id = LaneIdV2::new(index).unwrap();
                let (lane, _) = state.lane(lane_id);
                FinalizedForestAccountV2 {
                    address: lane.address,
                    owner: program.to_bytes(),
                    executable: false,
                    data: lane.image.to_vec(),
                }
            })
            .collect::<Vec<_>>();
        let current_root_pages = (0..8u8)
            .map(|index| {
                let lane_id = LaneIdV2::new(index).unwrap();
                let (lane, _) = state.lane(lane_id);
                assert!(lane.value.tree.next_leaf_index <= 1);
                let mut page = RootHistoryPageV1::genesis(
                    lane.address,
                    POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
                );
                if lane.value.tree.next_leaf_index == 1 {
                    page.push(1, lane.value.tree.root).unwrap();
                }
                let cursor = canonical_lane_root_page_cursor_v2(
                    program.to_bytes(),
                    state.master().address,
                    lane_id,
                    lane.value.tree.next_leaf_index,
                )
                .unwrap();
                FinalizedForestRootPageV2 {
                    lane_id,
                    page_number: cursor.page_number,
                    account: FinalizedForestAccountV2 {
                        address: cursor.address,
                        owner: program.to_bytes(),
                        executable: false,
                        data: page.encode().unwrap().to_vec(),
                    },
                }
            })
            .collect();
        FinalizedForestAccountSnapshotV2 {
            asserted_commitment: ForestRpcCommitmentV2::Finalized,
            context_slot,
            master: FinalizedForestAccountV2 {
                address: state.master().address,
                owner: program.to_bytes(),
                executable: false,
                data: state.master().image.to_vec(),
            },
            lanes,
            new_checkpoint,
            current_root_pages,
        }
    }

    fn checkpointed(
        program: Pubkey,
        state: &LaneForestDurableStateV2,
        observed_at: FinalizedChainPointV1,
    ) -> (LaneForestDurableStateV2, FinalizedForestAccountV2) {
        let sequences = core::array::from_fn(|index| {
            state
                .lane(LaneIdV2::new(index as u8).unwrap())
                .0
                .value
                .tree
                .next_leaf_index
        });
        let roots = core::array::from_fn(|index| {
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
            global_root: decode_digest_canonical(&lane_forest_global_root_v2(&roots).unwrap())
                .unwrap(),
            lane_sequences: sequences,
        };
        let checkpoint_address = pool_v1_pair_forest_checkpoint_address(
            &program,
            &Pubkey::new_from_array(state.master().address),
            checkpoint.checkpoint_sequence,
        )
        .0;
        let checkpoint_image = encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint).unwrap();
        let next_master = PoolV1PairForestMasterV1 {
            has_checkpoint: true,
            next_checkpoint_sequence: checkpoint.checkpoint_sequence + 1,
            last_checkpoint_lane_sequences: sequences,
            ..state.master().value
        };
        let next_master_image = encode_pool_v1_pair_forest_master_v1(&next_master).unwrap();
        let lanes = (0..8u8)
            .map(|index| {
                let lane = state.lane(LaneIdV2::new(index).unwrap()).0;
                (lane.address, lane.image.to_vec())
            })
            .collect::<Vec<_>>();
        let mut next = state.clone();
        next.ingest_finalized_checkpoint_v2(
            observed_at,
            state.master().address,
            &next_master_image,
            &lanes,
            checkpoint_address.to_bytes(),
            &checkpoint_image,
        )
        .unwrap();
        (
            next,
            FinalizedForestAccountV2 {
                address: checkpoint_address.to_bytes(),
                owner: program.to_bytes(),
                executable: false,
                data: checkpoint_image.to_vec(),
            },
        )
    }

    fn temp_path() -> std::path::PathBuf {
        std::env::temp_dir().join(format!(
            "aspis-forest-rpc-v2-{}-{}.bin",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ))
    }

    fn cleanup(path: &std::path::Path) {
        let lock = path.with_file_name(format!(
            "{}.lock",
            path.file_name().unwrap().to_string_lossy()
        ));
        std::fs::remove_file(path).unwrap();
        std::fs::remove_file(lock).unwrap();
    }

    #[test]
    fn compact_program_event_abi_round_trips_all_variants_and_rejects_drift() {
        let (_, state) = fixture();
        let variants = [
            PairForestProgramEventKindV2::Deposit {
                commitment: encode_digest_canonical(&digest(10)),
                encrypted_note: Some([1u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES]),
            },
            PairForestProgramEventKindV2::PrivateTransfer {
                nullifier: encode_digest_canonical(&digest(20)),
                recipient_commitment: encode_digest_canonical(&digest(30)),
                change_commitment: encode_digest_canonical(&digest(40)),
                recipient_encrypted_note: Some([2u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES]),
                change_encrypted_note: Some([3u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES]),
            },
            PairForestProgramEventKindV2::Withdrawal {
                nullifier: encode_digest_canonical(&digest(50)),
                change_commitment: encode_digest_canonical(&digest(60)),
                destination_token_account: [9u8; 32],
                amount: 7,
                encrypted_note: None,
            },
        ];
        for kind in variants {
            let event = program_event(&state, kind);
            let encoded = encode_pair_forest_program_event_v2(&event).unwrap();
            assert_eq!(decode_pair_forest_program_event_v2(&encoded), Ok(event));
            let mut trailing = encoded;
            trailing.push(0);
            assert_eq!(
                decode_pair_forest_program_event_v2(&trailing),
                Err(LaneForestRpcErrorV2::WrongEventLength)
            );
        }
    }

    #[test]
    fn finalized_adapter_commits_once_replays_idempotently_and_rejects_untrusted_input() {
        let (program, initial) = fixture();
        let chain_point = point(10);
        let id = event_id(chain_point, 11);
        let event = program_event(
            &initial,
            PairForestProgramEventKindV2::Deposit {
                commitment: encode_digest_canonical(&digest(80)),
                encrypted_note: None,
            },
        );
        let mut expected = initial.clone();
        apply_program_event(&mut expected, id, event.clone());
        expected.set_finalized_head_v2(chain_point);
        let batch = FinalizedForestRpcBatchV2 {
            asserted_commitment: ForestRpcCommitmentV2::Finalized,
            point: chain_point,
            parent: point(9),
            observations: vec![FinalizedForestEventObservationV2 {
                transaction_index: 0,
                event_id: id,
                emitting_program: program.to_bytes(),
                event_bytes: encode_pair_forest_program_event_v2(&event).unwrap(),
            }],
            accounts: snapshot(program, &expected, 10, None),
        };
        let path = temp_path();
        {
            let mut wallet =
                DurableLaneForestWalletFileV2::open_or_create_v2(&path, initial.clone()).unwrap();
            let result = ingest_finalized_forest_rpc_batch_v2(&mut wallet, &batch, None).unwrap();
            assert_eq!(result.status, FinalizedForestIngestStatusV2::Advanced);
            assert_eq!(wallet.state(), &expected);
            assert_eq!(
                ingest_finalized_forest_rpc_batch_v2(&mut wallet, &batch, None)
                    .unwrap()
                    .status,
                FinalizedForestIngestStatusV2::Replayed
            );
            let before = wallet.state().clone();
            let mut untrusted = batch.clone();
            untrusted.observations[0].emitting_program = [0x55; 32];
            assert!(matches!(
                ingest_finalized_forest_rpc_batch_v2(&mut wallet, &untrusted, None),
                Err(LaneForestRpcErrorV2::WrongProgram)
            ));
            assert_eq!(wallet.state(), &before);

            let mut forged_page = batch.clone();
            forged_page.accounts.current_root_pages[0].account.owner = [0x66; 32];
            assert!(matches!(
                ingest_finalized_forest_rpc_batch_v2(&mut wallet, &forged_page, None),
                Err(LaneForestRpcErrorV2::WrongAccountOwner)
            ));
            assert_eq!(wallet.state(), &before);
        }
        cleanup(&path);
    }

    #[test]
    fn private_transfer_and_withdrawal_each_advance_one_routed_pair() {
        let (program, initial) = fixture();
        let chain_point = point(20);
        let private = program_event(
            &initial,
            PairForestProgramEventKindV2::PrivateTransfer {
                nullifier: encode_digest_canonical(&digest(0)),
                recipient_commitment: encode_digest_canonical(&digest(100)),
                change_commitment: encode_digest_canonical(&digest(200)),
                recipient_encrypted_note: None,
                change_encrypted_note: None,
            },
        );
        let withdrawal = program_event(
            &initial,
            PairForestProgramEventKindV2::Withdrawal {
                nullifier: encode_digest_canonical(&digest(1)),
                change_commitment: encode_digest_canonical(&digest(300)),
                destination_token_account: [0x77; 32],
                amount: 99,
                encrypted_note: None,
            },
        );
        let first_id = event_id(chain_point, 21);
        let second_id = event_id(chain_point, 22);
        let mut expected = initial.clone();
        apply_program_event(&mut expected, first_id, private.clone());
        apply_program_event(&mut expected, second_id, withdrawal.clone());
        expected.set_finalized_head_v2(chain_point);
        let batch = FinalizedForestRpcBatchV2 {
            asserted_commitment: ForestRpcCommitmentV2::Finalized,
            point: chain_point,
            parent: point(19),
            observations: vec![
                FinalizedForestEventObservationV2 {
                    transaction_index: 0,
                    event_id: first_id,
                    emitting_program: program.to_bytes(),
                    event_bytes: encode_pair_forest_program_event_v2(&private).unwrap(),
                },
                FinalizedForestEventObservationV2 {
                    transaction_index: 1,
                    event_id: second_id,
                    emitting_program: program.to_bytes(),
                    event_bytes: encode_pair_forest_program_event_v2(&withdrawal).unwrap(),
                },
            ],
            accounts: snapshot(program, &expected, 20, None),
        };
        let path = temp_path();
        {
            let mut wallet =
                DurableLaneForestWalletFileV2::open_or_create_v2(&path, initial).unwrap();
            let result = ingest_finalized_forest_rpc_batch_v2(&mut wallet, &batch, None).unwrap();
            assert_eq!(result.withdrawals.len(), 1);
            assert_eq!(result.withdrawals[0].amount, 99);
            assert_eq!(
                wallet
                    .state()
                    .lane(LaneIdV2::new(1).unwrap())
                    .0
                    .value
                    .tree
                    .next_leaf_index,
                1
            );
            assert_eq!(
                wallet
                    .state()
                    .lane(LaneIdV2::new(2).unwrap())
                    .0
                    .value
                    .tree
                    .next_leaf_index,
                1
            );
        }
        {
            let reopened =
                DurableLaneForestWalletFileV2::open_or_create_v2(&path, expected.clone()).unwrap();
            assert_eq!(reopened.state(), &expected);
        }
        cleanup(&path);
    }

    #[test]
    fn retained_checkpoint_fork_rolls_back_all_lanes_before_new_branch() {
        let (program, initial) = fixture();
        let first_point = point(30);
        let first_id = event_id(first_point, 31);
        let first = program_event(
            &initial,
            PairForestProgramEventKindV2::Deposit {
                commitment: encode_digest_canonical(&digest(0)),
                encrypted_note: None,
            },
        );
        let mut after_first = initial.clone();
        apply_program_event(&mut after_first, first_id, first.clone());
        after_first.set_finalized_head_v2(first_point);
        let first_batch = FinalizedForestRpcBatchV2 {
            asserted_commitment: ForestRpcCommitmentV2::Finalized,
            point: first_point,
            parent: point(29),
            observations: vec![FinalizedForestEventObservationV2 {
                transaction_index: 0,
                event_id: first_id,
                emitting_program: program.to_bytes(),
                event_bytes: encode_pair_forest_program_event_v2(&first).unwrap(),
            }],
            accounts: snapshot(program, &after_first, 30, None),
        };
        let checkpoint_point = point(31);
        let (mut at_checkpoint, checkpoint_account) =
            checkpointed(program, &after_first, checkpoint_point);
        at_checkpoint.set_finalized_head_v2(checkpoint_point);
        let checkpoint_batch = FinalizedForestRpcBatchV2 {
            asserted_commitment: ForestRpcCommitmentV2::Finalized,
            point: checkpoint_point,
            parent: first_point,
            observations: Vec::new(),
            accounts: snapshot(
                program,
                &at_checkpoint,
                31,
                Some(checkpoint_account.clone()),
            ),
        };
        let stale_point = point(32);
        let stale_id = event_id(stale_point, 32);
        let stale = program_event(
            &at_checkpoint,
            PairForestProgramEventKindV2::Deposit {
                commitment: encode_digest_canonical(&digest(1)),
                encrypted_note: None,
            },
        );
        let mut stale_state = at_checkpoint.clone();
        apply_program_event(&mut stale_state, stale_id, stale.clone());
        stale_state.set_finalized_head_v2(stale_point);
        let stale_batch = FinalizedForestRpcBatchV2 {
            asserted_commitment: ForestRpcCommitmentV2::Finalized,
            point: stale_point,
            parent: checkpoint_point,
            observations: vec![FinalizedForestEventObservationV2 {
                transaction_index: 0,
                event_id: stale_id,
                emitting_program: program.to_bytes(),
                event_bytes: encode_pair_forest_program_event_v2(&stale).unwrap(),
            }],
            accounts: snapshot(program, &stale_state, 32, None),
        };
        let fork_point = point(33);
        let fork_id = event_id(fork_point, 33);
        let fork = program_event(
            &at_checkpoint,
            PairForestProgramEventKindV2::Deposit {
                commitment: encode_digest_canonical(&digest(2)),
                encrypted_note: None,
            },
        );
        let mut fork_state = at_checkpoint.clone();
        apply_program_event(&mut fork_state, fork_id, fork.clone());
        fork_state.set_finalized_head_v2(fork_point);
        let fork_batch = FinalizedForestRpcBatchV2 {
            asserted_commitment: ForestRpcCommitmentV2::Finalized,
            point: fork_point,
            parent: checkpoint_point,
            observations: vec![FinalizedForestEventObservationV2 {
                transaction_index: 0,
                event_id: fork_id,
                emitting_program: program.to_bytes(),
                event_bytes: encode_pair_forest_program_event_v2(&fork).unwrap(),
            }],
            accounts: snapshot(program, &fork_state, 33, None),
        };

        let path = temp_path();
        {
            let mut wallet =
                DurableLaneForestWalletFileV2::open_or_create_v2(&path, initial).unwrap();
            ingest_finalized_forest_rpc_batch_v2(&mut wallet, &first_batch, None).unwrap();
            ingest_finalized_forest_rpc_batch_v2(&mut wallet, &checkpoint_batch, None).unwrap();
            ingest_finalized_forest_rpc_batch_v2(&mut wallet, &stale_batch, None).unwrap();
            let result =
                ingest_finalized_forest_rpc_batch_v2(&mut wallet, &fork_batch, None).unwrap();
            assert_eq!(result.rolled_back_checkpoint_sequence, Some(0));
            assert_eq!(wallet.state(), &fork_state);
            assert_eq!(
                wallet
                    .state()
                    .lane(LaneIdV2::new(2).unwrap())
                    .0
                    .value
                    .tree
                    .next_leaf_index,
                0
            );
        }
        cleanup(&path);
    }
}
