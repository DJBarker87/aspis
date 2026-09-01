//! Default-off finalized RPC adapter for the eight-lane pair forest.
//!
//! `ASF8` is exclusively the 1,880-byte cryptographic semantic statement. The
//! compact wallet-side normalized scanner record in this module is `ASFE`; it
//! is not an on-chain Pool event and must never be accepted from program logs.
//! The production boundary bypasses that record and derives the ASL2 event
//! directly from the exact successful, finalized, last top-level `ASQ8` Pool
//! instruction, its Pool-owned `ASR8` return data and the deployment-owned
//! finalized root page. The older batch adapter remains default-off for
//! fixtures and independently supplied scanner evidence.
//!
//! The existing relayer execution journal is a separate atomic file and this
//! consumer ABI has no authenticated relayer request identifier. Cross-file
//! atomic coordination is therefore not claimed: withdrawals are returned to
//! the caller for later correlation once the producer ABI supplies that link.

use aspis_pool::POOL_V1_PAIR_EMPTY_ROOTS;
use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{
        decode_pool_v1_pair_forest_lane_state_v1, decode_pool_v1_pair_forest_terminal_request_v1,
        decode_pool_v1_pair_forest_terminal_result_v1, encode_pool_v1_pair_forest_lane_state_v1,
        root_history::{read_root_history_page_root_v1, validate_root_history_page_bytes_v1},
        PoolV1PairForestLaneStateV1, PoolV1PairForestTerminalPaymentV1, PoolV1PairLeafWitnessV1,
        PoolV1RootHistoryError, PoolV1TransitionKind, POOL_V1_PAIR_CAPACITY,
        POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES,
        POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES, POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
    },
};
use hpke::rand_core::CryptoRng;

use crate::{
    durable_state::SealedNoteAccessV1,
    finalized_indexer::SolanaRpcCommitmentV1,
    lane_forest_durable_v2::{
        canonical_lane_root_page_cursor_v2, DurableLaneForestWalletFileV2,
        ForestFinalizedAppendEventV2, ForestFinalizedAppendKindV2, ForestNoteAssociationV2,
        LaneForestDurableErrorV2, LaneForestDurableStateV2,
    },
    lane_forest_v2::{LaneIdV2, POOL_V1_LANE_COUNT_V2},
    lane_forest_wallet_txn_v2::{
        FinalizedLedgerPositionV2, LaneForestWalletCheckpointBindingV2,
        LaneForestWalletCommittedStateV2, LaneForestWalletNoteBindingV2,
        LaneForestWalletSpendBindingV2, LaneForestWalletTxnErrorV2, LaneForestWalletTxnIntentV2,
    },
    note_matches_spending_key_v1,
    note_store_crypto::{
        seal_recovered_note_v1, LocalNullifierKeyStoreV1, NoteStoreCipherV1, NoteStoreCryptoErrorV1,
    },
    scan_note_v1,
    scan_state::{DepositEventIdV1, FinalizedBlockV1, FinalizedChainPointV1},
    PoolV1WalletError, ScanResultV1, ViewingSecretKeyV1, POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES,
};

pub type ForestRpcCommitmentV2 = SolanaRpcCommitmentV1;

/// Wallet-only normalized scanner evidence. This value deliberately differs
/// from the cryptographic `ASF8` semantic statement magic.
pub const PAIR_FOREST_SCANNER_EVENT_MAGIC_V2: [u8; 4] = *b"ASFE";
pub const PAIR_FOREST_PROGRAM_EVENT_VERSION_V2: u8 = 2;
pub const PAIR_FOREST_PROGRAM_EVENT_HEADER_BYTES_V2: usize = 232;
pub const PAIR_FOREST_PROGRAM_EVENT_DEPOSIT_V2: u8 = 1;
pub const PAIR_FOREST_PROGRAM_EVENT_PRIVATE_TRANSFER_V2: u8 = 2;
pub const PAIR_FOREST_PROGRAM_EVENT_WITHDRAWAL_V2: u8 = 3;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LaneForestRpcErrorV2 {
    NotFinalized,
    TransactionFailed,
    ContextTooOld,
    WrongProgram,
    WrongReturnDataProgram,
    WrongInstructionPosition,
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
    FinalizedRollback,
    UnretainedFork,
    MissingCheckpoint,
    UnexpectedCheckpoint,
    MissingRootPage,
    WrongRootPage,
    TerminalResultMismatch,
    RootPage(PoolV1RootHistoryError),
    Durable(LaneForestDurableErrorV2),
    Wallet(LaneForestWalletTxnErrorV2),
    NoteEnvelope(PoolV1WalletError),
    NoteStore(NoteStoreCryptoErrorV1),
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

impl From<LaneForestWalletTxnErrorV2> for LaneForestRpcErrorV2 {
    fn from(error: LaneForestWalletTxnErrorV2) -> Self {
        Self::Wallet(error)
    }
}

impl From<PoolV1WalletError> for LaneForestRpcErrorV2 {
    fn from(error: PoolV1WalletError) -> Self {
        Self::NoteEnvelope(error)
    }
}

impl From<NoteStoreCryptoErrorV1> for LaneForestRpcErrorV2 {
    fn from(error: NoteStoreCryptoErrorV1) -> Self {
        Self::NoteStore(error)
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
    output[..4].copy_from_slice(&PAIR_FOREST_SCANNER_EVENT_MAGIC_V2);
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
    if bytes[..4] != PAIR_FOREST_SCANNER_EVENT_MAGIC_V2 {
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

/// Wallet delivery metadata is deliberately subordinate to the proved Pool
/// transition. A missing or malformed carrier cannot fabricate a note and
/// cannot prevent the canonical ASQ8/ASR8 lane append from entering ASL2.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PairForestCiphertextDeliveryFailureV2 {
    Missing,
    Invalid,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FinalizedPairForestCiphertextDeliveryV2 {
    Unrecoverable(PairForestCiphertextDeliveryFailureV2),
    Verified {
        instruction_index: u16,
        authority: [u8; 32],
        carrier: crate::tx_v1_ciphertext_carrier_v2::TxV1CiphertextCarrierV2,
    },
}

/// Exact externally authenticated fields needed to turn one deployed Pool V2
/// terminal into a canonical wallet event. `instruction_index` is the index in
/// `transaction.message.instructions`; the instruction must be last so no
/// later top-level program can overwrite transaction-global return data.
///
/// The finalized root page may be fetched after the entire block. Its history
/// entry at the exact ASR8 sequence, rather than its latest root, authenticates
/// this transaction's after-root even when later appends share the block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedPairForestTerminalObservationV2 {
    pub asserted_commitment: ForestRpcCommitmentV2,
    pub accounts_asserted_commitment: ForestRpcCommitmentV2,
    pub block: FinalizedBlockV1,
    pub account_context_slot: u64,
    /// Exact index in the finalized block's transaction array. This is ledger
    /// order; signature byte ordering is deliberately not used as a proxy.
    pub transaction_index: u32,
    pub transaction_signature: [u8; 64],
    pub transaction_succeeded: bool,
    pub instruction_index: u16,
    pub top_level_instruction_count: u16,
    pub instruction_program: [u8; 32],
    pub instruction_bytes: Vec<u8>,
    pub ciphertext_delivery: FinalizedPairForestCiphertextDeliveryV2,
    pub return_data_program: [u8; 32],
    pub return_data: Vec<u8>,
    pub root_page: FinalizedForestRootPageV2,
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

fn validate_terminal_root_page_v2(
    state: &LaneForestDurableStateV2,
    lane_id: LaneIdV2,
    root_sequence: u64,
    expected_root: aspis_statement::Digest,
    page: &FinalizedForestRootPageV2,
) -> Result<(), LaneForestRpcErrorV2> {
    if page.lane_id != lane_id {
        return Err(LaneForestRpcErrorV2::WrongRootPage);
    }
    require_program_account_v2(&page.account, *state.program_id())?;
    if page.account.data.len() != POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES {
        return Err(LaneForestRpcErrorV2::WrongRootPage);
    }
    let cursor = canonical_lane_root_page_cursor_v2(
        *state.program_id(),
        state.master().address,
        lane_id,
        root_sequence,
    )?;
    let (lane, _) = state.lane(lane_id);
    let header = validate_root_history_page_bytes_v1(&page.account.data)?;
    if page.page_number != cursor.page_number
        || page.account.address != cursor.address
        || header.pool != lane.address
        || header.page_number != cursor.page_number
        || read_root_history_page_root_v1(&page.account.data, root_sequence)? != expected_root
    {
        return Err(LaneForestRpcErrorV2::WrongRootPage);
    }
    Ok(())
}

fn terminal_public_matches_master_v2(
    state: &LaneForestDurableStateV2,
    public: &PoolV1PairForestTerminalPaymentV1,
) -> bool {
    let identity = &state.master().value.identity;
    match public {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => {
            public.pool == state.master().address
                && public.deployment_domain == identity.deployment_domain
                && public.asset_id == identity.asset_id
        }
        PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => {
            public.pool == state.master().address
                && public.deployment_domain == identity.deployment_domain
                && public.asset_id == identity.asset_id
        }
    }
}

fn scanner_event_from_terminal_v2(
    state: &LaneForestDurableStateV2,
    observation: &FinalizedPairForestTerminalObservationV2,
) -> Result<(DepositEventIdV1, PairForestProgramEventV2), LaneForestRpcErrorV2> {
    if observation.asserted_commitment != ForestRpcCommitmentV2::Finalized
        || observation.accounts_asserted_commitment != ForestRpcCommitmentV2::Finalized
    {
        return Err(LaneForestRpcErrorV2::NotFinalized);
    }
    if observation.account_context_slot < observation.block.point().slot() {
        return Err(LaneForestRpcErrorV2::ContextTooOld);
    }
    if !observation.transaction_succeeded {
        return Err(LaneForestRpcErrorV2::TransactionFailed);
    }
    if observation.top_level_instruction_count == 0
        || observation
            .instruction_index
            .checked_add(1)
            .is_none_or(|next| next != observation.top_level_instruction_count)
    {
        return Err(LaneForestRpcErrorV2::WrongInstructionPosition);
    }
    if observation.instruction_program != *state.program_id() {
        return Err(LaneForestRpcErrorV2::WrongProgram);
    }
    if observation.return_data_program != *state.program_id() {
        return Err(LaneForestRpcErrorV2::WrongReturnDataProgram);
    }
    let request = decode_pool_v1_pair_forest_terminal_request_v1(&observation.instruction_bytes)
        .map_err(|_| LaneForestRpcErrorV2::InvalidEvent)?;
    let (recipient_ciphertext, change_ciphertext) = match &observation.ciphertext_delivery {
        FinalizedPairForestCiphertextDeliveryV2::Unrecoverable(_) => (None, None),
        FinalizedPairForestCiphertextDeliveryV2::Verified {
            instruction_index,
            authority,
            carrier,
        } => {
            if *authority == [0u8; 32]
                || instruction_index
                    .checked_add(1)
                    .is_none_or(|next| next != observation.instruction_index)
            {
                return Err(LaneForestRpcErrorV2::InvalidEvent);
            }
            carrier
                .validate_terminal_v2(
                    &observation.instruction_bytes,
                    *carrier.proof_account_v2(),
                    *instruction_index,
                    observation.instruction_index,
                )
                .map_err(|_| LaneForestRpcErrorV2::InvalidEvent)?;
            (
                carrier.recipient_ciphertext_v2().copied(),
                Some(*carrier.change_ciphertext_v2()),
            )
        }
    };
    let result = decode_pool_v1_pair_forest_terminal_result_v1(&observation.return_data)
        .map_err(|_| LaneForestRpcErrorV2::InvalidEvent)?;
    if request.pool_program != *state.program_id()
        || !terminal_public_matches_master_v2(state, &request.public)
        || result.transition_kind != request.public.transition_kind()
        || result.master_account != state.master().address
        || result.nullifier != *request.public.nullifier()
    {
        return Err(LaneForestRpcErrorV2::TerminalResultMismatch);
    }
    let lane_id = LaneIdV2::new(result.output_lane)
        .map_err(|_| LaneForestRpcErrorV2::TerminalResultMismatch)?;
    let (lane, _) = state.lane(lane_id);
    if result.selected_lane_account != lane.address {
        return Err(LaneForestRpcErrorV2::TerminalResultMismatch);
    }
    let pair_leaf_index = result
        .verified_afterstate
        .next_pair_index
        .checked_sub(1)
        .ok_or(LaneForestRpcErrorV2::TerminalResultMismatch)?;
    let kind = match request.public {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => {
            if result.transition_kind != PoolV1TransitionKind::PrivateTransfer {
                return Err(LaneForestRpcErrorV2::TerminalResultMismatch);
            }
            PairForestProgramEventKindV2::PrivateTransfer {
                nullifier: encode_digest_canonical(&public.nullifier),
                recipient_commitment: encode_digest_canonical(&public.recipient_commitment),
                change_commitment: encode_digest_canonical(&public.change_commitment),
                recipient_encrypted_note: recipient_ciphertext,
                change_encrypted_note: change_ciphertext,
            }
        }
        PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => {
            if result.transition_kind != PoolV1TransitionKind::Withdrawal {
                return Err(LaneForestRpcErrorV2::TerminalResultMismatch);
            }
            PairForestProgramEventKindV2::Withdrawal {
                nullifier: encode_digest_canonical(&public.nullifier),
                change_commitment: encode_digest_canonical(&public.change_commitment),
                destination_token_account: public.destination_token_account,
                amount: public.amount,
                encrypted_note: change_ciphertext,
            }
        }
    };
    let event_id = DepositEventIdV1::new(
        observation.block.point(),
        observation.transaction_signature,
        observation.instruction_index,
        0,
    )
    .map_err(|_| LaneForestRpcErrorV2::InvalidEvent)?;
    Ok((
        event_id,
        PairForestProgramEventV2 {
            master: state.master().address,
            pair_leaf_index,
            root_sequence: result.verified_afterstate.next_pair_index,
            after_lane_root: encode_digest_canonical(&result.verified_afterstate.next_root),
            kind,
        },
    ))
}

/// Derive one canonical ASL2 append event from the literal deployed terminal
/// path. No program log or caller-supplied `ASFE` bytes are trusted.
pub fn derive_finalized_pair_forest_terminal_event_v2(
    state: &LaneForestDurableStateV2,
    observation: &FinalizedPairForestTerminalObservationV2,
) -> Result<ForestFinalizedAppendEventV2, LaneForestRpcErrorV2> {
    let head = state.finalized_head_v2();
    let point = observation.block.point();
    if head.is_some_and(|head| {
        point.slot() < head.slot()
            || (point.slot() == head.slot() && point.block_hash() != head.block_hash())
    }) {
        return Err(LaneForestRpcErrorV2::FinalizedRollback);
    }
    if head.is_some_and(|head| point != head && observation.block.parent() != head) {
        return Err(LaneForestRpcErrorV2::InvalidChainLink);
    }
    let result = decode_pool_v1_pair_forest_terminal_result_v1(&observation.return_data)
        .map_err(|_| LaneForestRpcErrorV2::InvalidEvent)?;
    let lane_id = LaneIdV2::new(result.output_lane)
        .map_err(|_| LaneForestRpcErrorV2::TerminalResultMismatch)?;
    let (event_id, scanner_event) = scanner_event_from_terminal_v2(state, observation)?;
    let event = if let Some(retained) = state.retained_event_v2(event_id) {
        if !retained_event_matches_program_v2(retained, event_id, &scanner_event)? {
            return Err(LaneForestRpcErrorV2::ReplayMismatch);
        }
        retained.clone()
    } else {
        durable_event_from_program_v2(state, event_id, scanner_event)?.0
    };
    let after = decode_pool_v1_pair_forest_lane_state_v1(
        &event.after_lane_image,
        &POOL_V1_PAIR_EMPTY_ROOTS,
    )
    .map_err(LaneForestDurableErrorV2::from)?;
    if after.tree.next_leaf_index != result.verified_afterstate.next_pair_index
        || after.tree.root != result.verified_afterstate.next_root
        || after.tree.frontier != result.verified_afterstate.next_frontier
        || event.lane_id != lane_id
        || event.after_lane_address != result.selected_lane_account
    {
        return Err(LaneForestRpcErrorV2::TerminalResultMismatch);
    }
    validate_terminal_root_page_v2(
        state,
        lane_id,
        event.root_sequence,
        after.tree.root,
        &observation.root_page,
    )?;
    Ok(event)
}

/// Construct the exact ASL2 intent from a derived deployed terminal event.
/// Local note/spend bindings remain separately authenticated by the ASL2
/// coordinator; absent terminal ciphertext cannot create a wallet note.
pub fn derive_finalized_pair_forest_terminal_intent_v2(
    state: &LaneForestWalletCommittedStateV2,
    observation: &FinalizedPairForestTerminalObservationV2,
    notes: Vec<LaneForestWalletNoteBindingV2>,
    spends: Vec<LaneForestWalletSpendBindingV2>,
    checkpoint: Option<LaneForestWalletCheckpointBindingV2>,
) -> Result<LaneForestWalletTxnIntentV2, LaneForestRpcErrorV2> {
    let event = derive_finalized_pair_forest_terminal_event_v2(state.lane_state(), observation)?;
    Ok(LaneForestWalletTxnIntentV2::new_ordered_v2(
        observation.block,
        event,
        FinalizedLedgerPositionV2::new_v2(observation.transaction_index),
        *state.note_cipher_id(),
        notes,
        spends,
        checkpoint,
        None,
    )?)
}

fn recovered_carrier_note_bindings_v2(
    rng: &mut impl CryptoRng,
    lane_state: &LaneForestDurableStateV2,
    note_cipher_id: [u8; 32],
    event: &ForestFinalizedAppendEventV2,
    viewing_secret: &ViewingSecretKeyV1,
    local_keys: &impl LocalNullifierKeyStoreV1,
    cipher: &NoteStoreCipherV1,
) -> Result<Vec<LaneForestWalletNoteBindingV2>, LaneForestRpcErrorV2> {
    if note_cipher_id != cipher.cipher_id() {
        return Err(LaneForestRpcErrorV2::Wallet(
            LaneForestWalletTxnErrorV2::InvalidNoteCipher,
        ));
    }
    let deployment_domain = lane_state.master().value.identity.deployment_domain;
    let mut outputs = Vec::with_capacity(2);
    match &event.kind {
        ForestFinalizedAppendKindV2::PrivateTransfer {
            recipient_event_id,
            change_event_id,
            recipient_commitment,
            change_commitment,
            recipient_encrypted_note,
            change_encrypted_note,
            ..
        } => {
            if let Some(payload) = recipient_encrypted_note {
                outputs.push((*recipient_event_id, *recipient_commitment, payload));
            }
            if let Some(payload) = change_encrypted_note {
                outputs.push((*change_event_id, *change_commitment, payload));
            }
        }
        ForestFinalizedAppendKindV2::Withdrawal {
            event_id,
            change_commitment,
            encrypted_note,
            ..
        } => {
            if let Some(payload) = encrypted_note {
                outputs.push((*event_id, *change_commitment, payload));
            }
        }
        ForestFinalizedAppendKindV2::Deposit { .. } => {
            return Err(LaneForestRpcErrorV2::InvalidEvent)
        }
    }
    let mut notes = Vec::with_capacity(outputs.len());
    for (event_id, commitment, payload) in outputs {
        let context = crate::NoteContextV1::new(
            event.master,
            deployment_domain,
            event.pair_leaf_index,
            commitment,
        )?;
        let note = match scan_note_v1(viewing_secret, &context, payload) {
            Ok(ScanResultV1::NotForViewingKey) => continue,
            Ok(ScanResultV1::RecoveredView(note)) => note,
            Err(PoolV1WalletError::InvalidViewingKey) => {
                return Err(LaneForestRpcErrorV2::NoteEnvelope(
                    PoolV1WalletError::InvalidViewingKey,
                ));
            }
            // Once ASC8 framing and signature/context binding have passed,
            // malformed plaintext or commitment mismatch is sender-controlled
            // delivery metadata. It cannot create a note and must not stall
            // the independently authenticated Pool append.
            Err(_) => continue,
        };
        // A viewing key alone yields a view-only record. Spendability is
        // promoted only if the protected local key service returns a matching
        // nullifier key for this exact decrypted owner digest.
        let access = local_keys
            .nullifier_key_for_owner_v1(note.owner_key())
            .map(|key| note_matches_spending_key_v1(&note, key.as_bytes()))
            .transpose()?
            .unwrap_or(false)
            .then_some(SealedNoteAccessV1::Spendable)
            .unwrap_or(SealedNoteAccessV1::ViewOnly);
        let sealed = seal_recovered_note_v1(rng, cipher, event_id, access, &note)?;
        notes.push(LaneForestWalletNoteBindingV2::from_sealed_recovered_note_v2(&sealed)?);
    }
    Ok(notes)
}

/// Construct the production ASL2 intent directly from the quorum-authenticated
/// ASC8→ASQ8→ASR8 path. Ciphertexts are decrypted with the local viewing key,
/// every recovered plaintext recomputes its public commitment inside
/// `scan_note_v1`, and the resulting note-store envelopes enter the same ASL2
/// transaction as the finalized append.
#[allow(clippy::too_many_arguments)]
pub fn derive_finalized_pair_forest_terminal_intent_with_carrier_notes_v2(
    rng: &mut impl CryptoRng,
    state: &LaneForestWalletCommittedStateV2,
    observation: &FinalizedPairForestTerminalObservationV2,
    viewing_secret: &ViewingSecretKeyV1,
    local_keys: &impl LocalNullifierKeyStoreV1,
    cipher: &NoteStoreCipherV1,
    spends: Vec<LaneForestWalletSpendBindingV2>,
    checkpoint: Option<LaneForestWalletCheckpointBindingV2>,
) -> Result<LaneForestWalletTxnIntentV2, LaneForestRpcErrorV2> {
    let event = derive_finalized_pair_forest_terminal_event_v2(state.lane_state(), observation)?;
    let notes = recovered_carrier_note_bindings_v2(
        rng,
        state.lane_state(),
        *state.note_cipher_id(),
        &event,
        viewing_secret,
        local_keys,
        cipher,
    )?;
    Ok(LaneForestWalletTxnIntentV2::new_ordered_v2(
        observation.block,
        event,
        FinalizedLedgerPositionV2::new_v2(observation.transaction_index),
        *state.note_cipher_id(),
        notes,
        spends,
        checkpoint,
        None,
    )?)
}

fn retained_event_matches_program_v2(
    retained: &ForestFinalizedAppendEventV2,
    event_id: DepositEventIdV1,
    event: &PairForestProgramEventV2,
) -> Result<bool, LaneForestRpcErrorV2> {
    let (first_id, second_id) = retained.event_ids();
    if first_id != event_id
        || matches!(
            event.kind,
            PairForestProgramEventKindV2::PrivateTransfer { .. }
        ) && second_id != Some(second_event_id_v2(event_id)?)
    {
        return Ok(false);
    }
    let after = decode_pool_v1_pair_forest_lane_state_v1(
        &retained.after_lane_image,
        &POOL_V1_PAIR_EMPTY_ROOTS,
    )
    .map_err(LaneForestDurableErrorV2::from)?;
    let retained_kind = match &retained.kind {
        ForestFinalizedAppendKindV2::Deposit {
            commitment,
            encrypted_note,
            ..
        } => PairForestProgramEventKindV2::Deposit {
            commitment: *commitment,
            encrypted_note: *encrypted_note,
        },
        ForestFinalizedAppendKindV2::PrivateTransfer {
            nullifier,
            recipient_commitment,
            change_commitment,
            recipient_encrypted_note,
            change_encrypted_note,
            ..
        } => PairForestProgramEventKindV2::PrivateTransfer {
            nullifier: *nullifier,
            recipient_commitment: *recipient_commitment,
            change_commitment: *change_commitment,
            recipient_encrypted_note: *recipient_encrypted_note,
            change_encrypted_note: *change_encrypted_note,
        },
        ForestFinalizedAppendKindV2::Withdrawal {
            nullifier,
            change_commitment,
            destination_token_account,
            amount,
            encrypted_note,
            ..
        } => PairForestProgramEventKindV2::Withdrawal {
            nullifier: *nullifier,
            change_commitment: *change_commitment,
            destination_token_account: *destination_token_account,
            amount: *amount,
            encrypted_note: *encrypted_note,
        },
    };
    Ok(event
        == &PairForestProgramEventV2 {
            master: retained.master,
            pair_leaf_index: retained.pair_leaf_index,
            root_sequence: retained.root_sequence,
            after_lane_root: encode_digest_canonical(&after.tree.root),
            kind: retained_kind,
        })
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
    if !replay {
        if let Some(head) = candidate.finalized_head_v2() {
            if batch.parent != head {
                // Every event retained by this adapter was admitted only at
                // finalized commitment. Rewinding it would lose finalized
                // notes and could resurrect finalized spends in a companion
                // store. Tentative confirmed observations belong in the V2
                // transaction coordinator and may be reorged there instead.
                return Err(LaneForestRpcErrorV2::FinalizedRollback);
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
            let Some(retained) = candidate.retained_event_v2(*event_id) else {
                return Err(LaneForestRpcErrorV2::ReplayMismatch);
            };
            if !retained_event_matches_program_v2(retained, *event_id, event)? {
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
        rolled_back_checkpoint_sequence: None,
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
        encode_pool_v1_pair_forest_terminal_request_v1,
        encode_pool_v1_pair_forest_terminal_result_v1, IncrementalMerkleTreeV1, PoolIdentityV1,
        PoolV1PairForestCheckpointV1, PoolV1PairForestMasterV1, PoolV1PairForestTerminalPaymentV1,
        PoolV1PairForestTerminalRequestV1, PoolV1PairForestTerminalResultV1,
        PoolV1PairVerifiedAfterstateV1, PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1,
        RootHistoryPageV1, VerifierPolicyV1, POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
        POOL_V1_PAIR_TREE_DEPTH,
    };
    use core::convert::Infallible;
    use hpke::rand_core::{TryCryptoRng, TryRng};
    use solana_program::pubkey::Pubkey;

    use crate::{
        derive_viewing_keypair_v1, encrypt_note_v1,
        lane_forest_v2::lane_forest_global_root_v2,
        note_store_crypto::{open_note_opening_v1, NullifierKeyMaterialV1},
        recompute_note_commitment_v1,
        tx_v1_ciphertext_carrier_v2::{
            structurally_valid_test_note_envelope_v2, TxV1CiphertextCarrierV2,
        },
        NoteContextV1, NoteOpeningV1,
    };

    struct FixedTestRng(u8);

    impl TryRng for FixedTestRng {
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

    impl TryCryptoRng for FixedTestRng {}

    struct NoLocalKeys;

    impl LocalNullifierKeyStoreV1 for NoLocalKeys {
        fn nullifier_key_for_owner_v1(&self, _: &[u8; 32]) -> Option<NullifierKeyMaterialV1> {
            None
        }
    }

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

    #[allow(clippy::too_many_arguments)]
    fn terminal_observation_with_outputs(
        program: Pubkey,
        state: &LaneForestDurableStateV2,
        chain_point: FinalizedChainPointV1,
        signature: [u8; 64],
        recipient: aspis_statement::Digest,
        change: aspis_statement::Digest,
        recipient_ciphertext: [u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES],
        change_ciphertext: [u8; POOL_V1_NOTE_ENCRYPTED_PAYLOAD_BYTES],
    ) -> FinalizedPairForestTerminalObservationV2 {
        let nullifier = digest(0);
        let public = PoolV1PrivateTransferPublicV1 {
            pool: state.master().address,
            deployment_domain: state.master().value.identity.deployment_domain,
            anchor_sequence: 0,
            anchor_root: digest(830),
            nullifier,
            asset_id: state.master().value.identity.asset_id,
            recipient_commitment: recipient,
            change_commitment: change,
        };
        let request = PoolV1PairForestTerminalRequestV1 {
            verifier_profile: [0x91; 32],
            verifier_release: [0x92; 32],
            pool_program: program.to_bytes(),
            public: PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public),
        };
        let ciphertext_carrier = TxV1CiphertextCarrierV2::from_terminal_v2(
            &request,
            [0xa4; 32],
            1,
            2,
            Some(recipient_ciphertext),
            change_ciphertext,
        )
        .unwrap();
        let lane_id = LaneIdV2::new(encode_digest_canonical(&nullifier)[0] & 7).unwrap();
        let (lane, _) = state.lane(lane_id);
        let pair_leaf = PoolV1PairLeafWitnessV1::two_outputs(recipient, change)
            .unwrap()
            .leaf_digest()
            .unwrap();
        let next = lane
            .value
            .tree
            .append_one_with_empty_roots(pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
            .unwrap()
            .0;
        let result = PoolV1PairForestTerminalResultV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            master_account: state.master().address,
            selected_lane_account: lane.address,
            output_lane: lane_id.as_u8(),
            nullifier,
            verified_afterstate: PoolV1PairVerifiedAfterstateV1 {
                next_pair_index: next.next_leaf_index,
                next_root: next.root,
                next_frontier: next.frontier,
            },
        };
        let mut root_page = RootHistoryPageV1::genesis(
            lane.address,
            POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
        );
        root_page.push(next.next_leaf_index, next.root).unwrap();
        let cursor = canonical_lane_root_page_cursor_v2(
            program.to_bytes(),
            state.master().address,
            lane_id,
            next.next_leaf_index,
        )
        .unwrap();
        FinalizedPairForestTerminalObservationV2 {
            asserted_commitment: ForestRpcCommitmentV2::Finalized,
            accounts_asserted_commitment: ForestRpcCommitmentV2::Finalized,
            block: FinalizedBlockV1::new(chain_point, point(chain_point.slot() - 1)).unwrap(),
            account_context_slot: chain_point.slot(),
            transaction_index: 0,
            transaction_signature: signature,
            transaction_succeeded: true,
            instruction_index: 2,
            top_level_instruction_count: 3,
            instruction_program: program.to_bytes(),
            instruction_bytes: encode_pool_v1_pair_forest_terminal_request_v1(&request)
                .unwrap()
                .to_vec(),
            ciphertext_delivery: FinalizedPairForestCiphertextDeliveryV2::Verified {
                instruction_index: 1,
                authority: [0xa3; 32],
                carrier: ciphertext_carrier,
            },
            return_data_program: program.to_bytes(),
            return_data: encode_pool_v1_pair_forest_terminal_result_v1(&result)
                .unwrap()
                .to_vec(),
            root_page: FinalizedForestRootPageV2 {
                lane_id,
                page_number: cursor.page_number,
                account: FinalizedForestAccountV2 {
                    address: cursor.address,
                    owner: program.to_bytes(),
                    executable: false,
                    data: root_page.encode().unwrap().to_vec(),
                },
            },
        }
    }

    fn terminal_observation(
        program: Pubkey,
        state: &LaneForestDurableStateV2,
        chain_point: FinalizedChainPointV1,
        signature: [u8; 64],
    ) -> FinalizedPairForestTerminalObservationV2 {
        terminal_observation_with_outputs(
            program,
            state,
            chain_point,
            signature,
            digest(810),
            digest(820),
            structurally_valid_test_note_envelope_v2(0xa5),
            structurally_valid_test_note_envelope_v2(0xa6),
        )
    }

    fn withdrawal_observation(
        program: Pubkey,
        state: &LaneForestDurableStateV2,
        chain_point: FinalizedChainPointV1,
        signature: [u8; 64],
    ) -> FinalizedPairForestTerminalObservationV2 {
        let nullifier = digest(1);
        let change = digest(910);
        let destination = [0x93; 32];
        let amount = 77;
        let public = PoolV1WithdrawalPublicV1 {
            pool: state.master().address,
            deployment_domain: state.master().value.identity.deployment_domain,
            anchor_sequence: 0,
            anchor_root: digest(930),
            nullifier,
            asset_id: state.master().value.identity.asset_id,
            amount,
            destination_token_account: destination,
            change_commitment: change,
        };
        let request = PoolV1PairForestTerminalRequestV1 {
            verifier_profile: [0x91; 32],
            verifier_release: [0x92; 32],
            pool_program: program.to_bytes(),
            public: PoolV1PairForestTerminalPaymentV1::Withdrawal(public),
        };
        let ciphertext_carrier = TxV1CiphertextCarrierV2::from_terminal_v2(
            &request,
            [0xa4; 32],
            1,
            2,
            None,
            structurally_valid_test_note_envelope_v2(0xa6),
        )
        .unwrap();
        let lane_id = LaneIdV2::new(encode_digest_canonical(&nullifier)[0] & 7).unwrap();
        let (lane, _) = state.lane(lane_id);
        let pair_leaf = PoolV1PairLeafWitnessV1::single_output(change)
            .unwrap()
            .leaf_digest()
            .unwrap();
        let next = lane
            .value
            .tree
            .append_one_with_empty_roots(pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
            .unwrap()
            .0;
        let result = PoolV1PairForestTerminalResultV1 {
            transition_kind: PoolV1TransitionKind::Withdrawal,
            master_account: state.master().address,
            selected_lane_account: lane.address,
            output_lane: lane_id.as_u8(),
            nullifier,
            verified_afterstate: PoolV1PairVerifiedAfterstateV1 {
                next_pair_index: next.next_leaf_index,
                next_root: next.root,
                next_frontier: next.frontier,
            },
        };
        let mut page = RootHistoryPageV1::genesis(
            lane.address,
            POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
        );
        page.push(next.next_leaf_index, next.root).unwrap();
        let cursor = canonical_lane_root_page_cursor_v2(
            program.to_bytes(),
            state.master().address,
            lane_id,
            next.next_leaf_index,
        )
        .unwrap();
        FinalizedPairForestTerminalObservationV2 {
            asserted_commitment: ForestRpcCommitmentV2::Finalized,
            accounts_asserted_commitment: ForestRpcCommitmentV2::Finalized,
            block: FinalizedBlockV1::new(chain_point, point(chain_point.slot() - 1)).unwrap(),
            account_context_slot: chain_point.slot(),
            transaction_index: 0,
            transaction_signature: signature,
            transaction_succeeded: true,
            instruction_index: 2,
            top_level_instruction_count: 3,
            instruction_program: program.to_bytes(),
            instruction_bytes: encode_pool_v1_pair_forest_terminal_request_v1(&request)
                .unwrap()
                .to_vec(),
            ciphertext_delivery: FinalizedPairForestCiphertextDeliveryV2::Verified {
                instruction_index: 1,
                authority: [0xa3; 32],
                carrier: ciphertext_carrier,
            },
            return_data_program: program.to_bytes(),
            return_data: encode_pool_v1_pair_forest_terminal_result_v1(&result)
                .unwrap()
                .to_vec(),
            root_page: FinalizedForestRootPageV2 {
                lane_id,
                page_number: cursor.page_number,
                account: FinalizedForestAccountV2 {
                    address: cursor.address,
                    owner: program.to_bytes(),
                    executable: false,
                    data: page.encode().unwrap().to_vec(),
                },
            },
        }
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
    fn compact_scanner_event_abi_round_trips_all_variants_and_rejects_drift() {
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
            assert_eq!(&encoded[..4], b"ASFE");
            assert_ne!(&encoded[..4], b"ASF8");
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
    fn deployed_terminal_source_derives_exact_event_and_fails_closed() {
        let (program, initial) = fixture();
        let chain_point = point(40);
        let observation = terminal_observation(program, &initial, chain_point, [0x44; 64]);
        let event = derive_finalized_pair_forest_terminal_event_v2(&initial, &observation).unwrap();
        let (first, second) = event.event_ids();
        assert_eq!(first.point(), chain_point);
        assert_eq!(first.transaction_signature(), &[0x44; 64]);
        assert_eq!(first.instruction_index(), 2);
        assert_eq!(first.event_index(), 0);
        assert_eq!(second.unwrap().event_index(), 1);
        assert!(matches!(
            event.kind,
            ForestFinalizedAppendKindV2::PrivateTransfer {
                recipient_encrypted_note: Some(_),
                change_encrypted_note: Some(_),
                ..
            }
        ));

        let mut omitted_delivery = observation.clone();
        omitted_delivery.ciphertext_delivery =
            FinalizedPairForestCiphertextDeliveryV2::Unrecoverable(
                PairForestCiphertextDeliveryFailureV2::Missing,
            );
        let omitted_event =
            derive_finalized_pair_forest_terminal_event_v2(&initial, &omitted_delivery).unwrap();
        assert!(matches!(
            omitted_event.kind,
            ForestFinalizedAppendKindV2::PrivateTransfer {
                recipient_encrypted_note: None,
                change_encrypted_note: None,
                ..
            }
        ));
        assert_eq!(omitted_event.after_lane_image, event.after_lane_image);

        let mut not_finalized = observation.clone();
        not_finalized.asserted_commitment = ForestRpcCommitmentV2::Confirmed;
        assert_eq!(
            derive_finalized_pair_forest_terminal_event_v2(&initial, &not_finalized),
            Err(LaneForestRpcErrorV2::NotFinalized)
        );
        let mut failed = observation.clone();
        failed.transaction_succeeded = false;
        assert_eq!(
            derive_finalized_pair_forest_terminal_event_v2(&initial, &failed),
            Err(LaneForestRpcErrorV2::TransactionFailed)
        );
        let mut stale_accounts = observation.clone();
        stale_accounts.account_context_slot = chain_point.slot() - 1;
        assert_eq!(
            derive_finalized_pair_forest_terminal_event_v2(&initial, &stale_accounts),
            Err(LaneForestRpcErrorV2::ContextTooOld)
        );
        let mut wrong_program = observation.clone();
        wrong_program.instruction_program = [0x54; 32];
        assert_eq!(
            derive_finalized_pair_forest_terminal_event_v2(&initial, &wrong_program),
            Err(LaneForestRpcErrorV2::WrongProgram)
        );
        let mut zero_signature = observation.clone();
        zero_signature.transaction_signature = [0u8; 64];
        assert_eq!(
            derive_finalized_pair_forest_terminal_event_v2(&initial, &zero_signature),
            Err(LaneForestRpcErrorV2::InvalidEvent)
        );
        let mut overwritten_return = observation.clone();
        overwritten_return.top_level_instruction_count = 4;
        assert_eq!(
            derive_finalized_pair_forest_terminal_event_v2(&initial, &overwritten_return),
            Err(LaneForestRpcErrorV2::WrongInstructionPosition)
        );
        let mut wrong_return_program = observation.clone();
        wrong_return_program.return_data_program = [0x55; 32];
        assert_eq!(
            derive_finalized_pair_forest_terminal_event_v2(&initial, &wrong_return_program),
            Err(LaneForestRpcErrorV2::WrongReturnDataProgram)
        );
        let mut mutated_result = observation.clone();
        mutated_result.return_data[40] ^= 1;
        assert!(derive_finalized_pair_forest_terminal_event_v2(&initial, &mutated_result).is_err());
        let mut wrong_page = observation.clone();
        wrong_page.root_page.account.owner = [0x66; 32];
        assert_eq!(
            derive_finalized_pair_forest_terminal_event_v2(&initial, &wrong_page),
            Err(LaneForestRpcErrorV2::WrongAccountOwner)
        );
        let mut wrong_page_address = observation.clone();
        wrong_page_address.root_page.account.address = [0x67; 32];
        assert_eq!(
            derive_finalized_pair_forest_terminal_event_v2(&initial, &wrong_page_address),
            Err(LaneForestRpcErrorV2::WrongRootPage)
        );

        let withdrawal = derive_finalized_pair_forest_terminal_event_v2(
            &initial,
            &withdrawal_observation(program, &initial, point(41), [0x45; 64]),
        )
        .unwrap();
        assert!(matches!(
            withdrawal.kind,
            ForestFinalizedAppendKindV2::Withdrawal {
                destination_token_account,
                amount: 77,
                encrypted_note: Some(_),
                ..
            } if destination_token_account == [0x93; 32]
        ));
    }

    #[test]
    fn carrier_aead_recovers_each_wallet_without_allowing_bad_delivery_to_stall_state() {
        let (program, initial) = fixture();
        let (recipient_secret, recipient_public) = derive_viewing_keypair_v1(&[0x31; 32]).unwrap();
        let (change_secret, change_public) = derive_viewing_keypair_v1(&[0x32; 32]).unwrap();
        let recipient_note = NoteOpeningV1::new(
            encode_digest_canonical(&digest(1_010)),
            70,
            initial.master().value.identity.asset_id.0,
            encode_digest_canonical(&digest(1_011)),
        )
        .unwrap();
        let change_note = NoteOpeningV1::new(
            encode_digest_canonical(&digest(1_020)),
            30,
            initial.master().value.identity.asset_id.0,
            encode_digest_canonical(&digest(1_021)),
        )
        .unwrap();
        let recipient_commitment = recompute_note_commitment_v1(&recipient_note).unwrap();
        let change_commitment = recompute_note_commitment_v1(&change_note).unwrap();
        let recipient_digest = decode_digest_canonical(&recipient_commitment).unwrap();
        let change_digest = decode_digest_canonical(&change_commitment).unwrap();
        let recipient_context = NoteContextV1::new(
            initial.master().address,
            initial.master().value.identity.deployment_domain,
            0,
            recipient_commitment,
        )
        .unwrap();
        let change_context = NoteContextV1::new(
            initial.master().address,
            initial.master().value.identity.deployment_domain,
            0,
            change_commitment,
        )
        .unwrap();
        let recipient_payload = encrypt_note_v1(
            &mut FixedTestRng(0x40),
            &recipient_public,
            &recipient_context,
            &recipient_note,
        )
        .unwrap();
        let change_payload = encrypt_note_v1(
            &mut FixedTestRng(0x80),
            &change_public,
            &change_context,
            &change_note,
        )
        .unwrap();
        let observation = terminal_observation_with_outputs(
            program,
            &initial,
            point(42),
            [0x46; 64],
            recipient_digest,
            change_digest,
            recipient_payload,
            change_payload,
        );
        let event = derive_finalized_pair_forest_terminal_event_v2(&initial, &observation).unwrap();
        let recipient_cipher = NoteStoreCipherV1::from_key_bytes([0x51; 32]).unwrap();
        let change_cipher = NoteStoreCipherV1::from_key_bytes([0x52; 32]).unwrap();
        let recipient_notes = recovered_carrier_note_bindings_v2(
            &mut FixedTestRng(0xa0),
            &initial,
            recipient_cipher.cipher_id(),
            &event,
            &recipient_secret,
            &NoLocalKeys,
            &recipient_cipher,
        )
        .unwrap();
        let change_notes = recovered_carrier_note_bindings_v2(
            &mut FixedTestRng(0xb0),
            &initial,
            change_cipher.cipher_id(),
            &event,
            &change_secret,
            &NoLocalKeys,
            &change_cipher,
        )
        .unwrap();
        assert_eq!(recipient_notes.len(), 1);
        assert_eq!(change_notes.len(), 1);
        assert_eq!(recipient_notes[0].access(), SealedNoteAccessV1::ViewOnly);
        assert_eq!(change_notes[0].access(), SealedNoteAccessV1::ViewOnly);
        assert_eq!(recipient_notes[0].event_id().event_index(), 0);
        assert_eq!(change_notes[0].event_id().event_index(), 1);
        let recovered_recipient = open_note_opening_v1(
            &recipient_cipher,
            recipient_notes[0].event_id(),
            recipient_notes[0].access(),
            recipient_notes[0].sealed_note(),
        )
        .unwrap();
        let recovered_change = open_note_opening_v1(
            &change_cipher,
            change_notes[0].event_id(),
            change_notes[0].access(),
            change_notes[0].sealed_note(),
        )
        .unwrap();
        assert_eq!(
            recompute_note_commitment_v1(&recovered_recipient).unwrap(),
            recipient_commitment
        );
        assert_eq!(
            recompute_note_commitment_v1(&recovered_change).unwrap(),
            change_commitment
        );

        // Swapping two canonical ciphertext slots preserves the proved
        // commitments and lane transition, but both AEAD AAD checks fail, so
        // neither wallet creates a note.
        let swapped = terminal_observation_with_outputs(
            program,
            &initial,
            point(42),
            [0x47; 64],
            recipient_digest,
            change_digest,
            change_payload,
            recipient_payload,
        );
        let swapped_event =
            derive_finalized_pair_forest_terminal_event_v2(&initial, &swapped).unwrap();
        assert_eq!(swapped_event.after_lane_image, event.after_lane_image);
        for (secret, cipher, seed) in [
            (&recipient_secret, &recipient_cipher, 0xc0),
            (&change_secret, &change_cipher, 0xd0),
        ] {
            assert!(recovered_carrier_note_bindings_v2(
                &mut FixedTestRng(seed),
                &initial,
                cipher.cipher_id(),
                &swapped_event,
                secret,
                &NoLocalKeys,
                cipher,
            )
            .unwrap()
            .is_empty());
        }

        // A missing carrier is recorded as unrecoverable delivery while the
        // exact same authenticated append remains ingestible into ASL2.
        let mut omitted = observation;
        omitted.ciphertext_delivery = FinalizedPairForestCiphertextDeliveryV2::Unrecoverable(
            PairForestCiphertextDeliveryFailureV2::Missing,
        );
        let omitted_event = derive_finalized_pair_forest_terminal_event_v2(&initial, &omitted)
            .expect("delivery omission cannot invalidate Pool state");
        assert_eq!(omitted_event.after_lane_image, event.after_lane_image);
        assert!(recovered_carrier_note_bindings_v2(
            &mut FixedTestRng(0xe0),
            &initial,
            recipient_cipher.cipher_id(),
            &omitted_event,
            &recipient_secret,
            &NoLocalKeys,
            &recipient_cipher,
        )
        .unwrap()
        .is_empty());
    }

    #[test]
    fn deployed_terminal_source_replays_exactly_and_rejects_finalized_forks() {
        let (program, initial) = fixture();
        let chain_point = point(50);
        let observation = terminal_observation(program, &initial, chain_point, [0x54; 64]);
        let event = derive_finalized_pair_forest_terminal_event_v2(&initial, &observation).unwrap();
        let mut advanced = initial.clone();
        advanced
            .ingest_finalized_append_v2(event.clone(), None)
            .unwrap();
        advanced.set_finalized_head_v2(chain_point);
        assert_eq!(
            derive_finalized_pair_forest_terminal_event_v2(&advanced, &observation),
            Ok(event)
        );

        let mut same_slot_fork = observation.clone();
        same_slot_fork.block = FinalizedBlockV1::new(
            FinalizedChainPointV1::new(50, [0xf0; 32]).unwrap(),
            point(49),
        )
        .unwrap();
        assert_eq!(
            derive_finalized_pair_forest_terminal_event_v2(&advanced, &same_slot_fork),
            Err(LaneForestRpcErrorV2::FinalizedRollback)
        );
        let mut wrong_parent = observation.clone();
        wrong_parent.block = FinalizedBlockV1::new(point(51), point(48)).unwrap();
        wrong_parent.account_context_slot = 51;
        wrong_parent.transaction_signature = [0x55; 64];
        assert_eq!(
            derive_finalized_pair_forest_terminal_event_v2(&advanced, &wrong_parent),
            Err(LaneForestRpcErrorV2::InvalidChainLink)
        );
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
            let mut conflicting_replay = batch.clone();
            let mut conflicting_event = event.clone();
            conflicting_event.kind = PairForestProgramEventKindV2::Deposit {
                commitment: encode_digest_canonical(&digest(81)),
                encrypted_note: None,
            };
            conflicting_replay.observations[0].event_bytes =
                encode_pair_forest_program_event_v2(&conflicting_event).unwrap();
            assert!(matches!(
                ingest_finalized_forest_rpc_batch_v2(&mut wallet, &conflicting_replay, None,),
                Err(LaneForestRpcErrorV2::ReplayMismatch)
            ));
            assert_eq!(wallet.state(), &before);

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
    fn retained_checkpoint_fork_cannot_rollback_finalized_lanes() {
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
            assert!(matches!(
                ingest_finalized_forest_rpc_batch_v2(&mut wallet, &fork_batch, None),
                Err(LaneForestRpcErrorV2::FinalizedRollback)
            ));
            assert_eq!(wallet.state(), &stale_state);
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
        cleanup(&path);
    }
}
