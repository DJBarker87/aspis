//! Exact Pool V1 deposit-record ingestion and a versioned scan-state image.
//!
//! This module deliberately treats RPC/indexer input as untrusted. Callers
//! must first establish that a block is finalized and that the record came
//! from the expected Pool program/instruction. The state then checks the
//! finalized parent chain, exact receipt framing, configured Pool identities,
//! append position, root sequence, encrypted-note context and locally known
//! owner key before advancing its cursor.
//!
//! The durable encoder accepts only public scan state: Pool/chain metadata and
//! event fingerprints. Ingestion borrows a viewing secret and may return a
//! note opening, but neither is retained. The image never serializes a viewing
//! secret, note opening, owner key, nullifier key or spending key.

use aspis_core::field::P;
use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{
        decode_deposit_receipt_v1, encode_deposit_receipt_v1, validate_deposit_event_v1,
        DepositEventV1, DepositReceiptV1, PoolV1DepositFormatError, POOL_V1_DEPOSIT_RECEIPT_BYTES,
        POOL_V1_DEPOSIT_RETURN_MAX_BYTES, POOL_V1_LEAF_CAPACITY,
    },
};
use sha2::{Digest as _, Sha256};
use subtle::ConstantTimeEq;

use crate::{
    scan_note_v1, NoteContextV1, NoteOpeningV1, PoolV1WalletError, ScanResultV1, ViewingSecretKeyV1,
};

pub const POOL_V1_SCAN_STATE_MAGIC: [u8; 4] = *b"ASWS";
pub const POOL_V1_SCAN_STATE_VERSION: u8 = 1;
pub const POOL_V1_SCAN_STATE_DIGEST_ENCODING_VERSION: u8 = 1;
pub const POOL_V1_SCAN_STATE_HEADER_BYTES: usize = 344;
pub const POOL_V1_SCAN_STATE_BLOCK_BYTES: usize = 128;
pub const POOL_V1_SCAN_STATE_EVENT_BYTES: usize = 212;

pub const POOL_V1_DEPOSIT_EVENT_FINGERPRINT_DOMAIN: &[u8] =
    b"aspis:pool-v1:wallet:deposit-event-record-fingerprint:sha256:v1";
pub const POOL_V1_PUBLIC_OUTPUT_FINGERPRINT_DOMAIN: &[u8] =
    b"aspis:pool-v1:wallet:authenticated-public-output-fingerprint:sha256:v1";
pub const POOL_V1_SCAN_STATE_CHECKSUM_DOMAIN: &[u8] =
    b"aspis:pool-v1:wallet:scan-state-checksum:sha256:v1";

const STATE_POOL_OFFSET: usize = 8;
const STATE_DEPLOYMENT_DOMAIN_OFFSET: usize = 40;
const STATE_ASSET_MINT_OFFSET: usize = 72;
const STATE_VAULT_OFFSET: usize = 104;
const STATE_ASSET_ID_OFFSET: usize = 136;
const STATE_ANCHOR_SLOT_OFFSET: usize = 144;
const STATE_ANCHOR_HASH_OFFSET: usize = 152;
const STATE_ANCHOR_NEXT_LEAF_OFFSET: usize = 184;
const STATE_ANCHOR_ROOT_OFFSET: usize = 192;
const STATE_HEAD_SLOT_OFFSET: usize = 224;
const STATE_HEAD_HASH_OFFSET: usize = 232;
const STATE_NEXT_LEAF_OFFSET: usize = 264;
const STATE_ROOT_OFFSET: usize = 272;
const STATE_BLOCK_COUNT_OFFSET: usize = 304;
const STATE_EVENT_COUNT_OFFSET: usize = 308;
const STATE_CHECKSUM_OFFSET: usize = 312;

const BLOCK_SLOT_OFFSET: usize = 0;
const BLOCK_HASH_OFFSET: usize = 8;
const BLOCK_PARENT_SLOT_OFFSET: usize = 40;
const BLOCK_PARENT_HASH_OFFSET: usize = 48;
const BLOCK_NEXT_LEAF_BEFORE_OFFSET: usize = 80;
const BLOCK_ROOT_BEFORE_OFFSET: usize = 88;
const BLOCK_EVENT_COUNT_BEFORE_OFFSET: usize = 120;

const EVENT_SLOT_OFFSET: usize = 0;
const EVENT_BLOCK_HASH_OFFSET: usize = 8;
const EVENT_SIGNATURE_OFFSET: usize = 40;
const EVENT_INSTRUCTION_INDEX_OFFSET: usize = 104;
const EVENT_INDEX_OFFSET: usize = 106;
const EVENT_LEAF_INDEX_OFFSET: usize = 108;
const EVENT_FINGERPRINT_OFFSET: usize = 116;
const EVENT_COMMITMENT_OFFSET: usize = 148;
const EVENT_ROOT_OFFSET: usize = 180;

/// Errors in the exact concatenated `receipt || encrypted_payload` record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DepositEventRecordErrorV1 {
    WrongLength,
    DepositFormat(PoolV1DepositFormatError),
}

/// Encode the exact wallet/indexer record: the canonical 224-byte Pool V1
/// receipt followed immediately by the receipt-declared opaque payload.
pub fn encode_deposit_event_record_v1(
    event: &DepositEventV1<'_>,
) -> Result<Vec<u8>, DepositEventRecordErrorV1> {
    validate_deposit_event_v1(event).map_err(DepositEventRecordErrorV1::DepositFormat)?;
    let receipt = encode_deposit_receipt_v1(&event.receipt)
        .map_err(DepositEventRecordErrorV1::DepositFormat)?;
    let expected_length = POOL_V1_DEPOSIT_RECEIPT_BYTES
        .checked_add(event.encrypted_note_payload.len())
        .ok_or(DepositEventRecordErrorV1::WrongLength)?;
    if expected_length > POOL_V1_DEPOSIT_RETURN_MAX_BYTES {
        return Err(DepositEventRecordErrorV1::WrongLength);
    }
    let mut output = Vec::with_capacity(expected_length);
    output.extend_from_slice(&receipt);
    output.extend_from_slice(event.encrypted_note_payload);
    Ok(output)
}

/// Decode one exact wallet/indexer record. Trailing bytes are not tolerated:
/// the total length must equal the payload length committed by the receipt.
pub fn decode_deposit_event_record_v1(
    bytes: &[u8],
) -> Result<DepositEventV1<'_>, DepositEventRecordErrorV1> {
    if bytes.len() < POOL_V1_DEPOSIT_RECEIPT_BYTES || bytes.len() > POOL_V1_DEPOSIT_RETURN_MAX_BYTES
    {
        return Err(DepositEventRecordErrorV1::WrongLength);
    }
    let receipt = decode_deposit_receipt_v1(&bytes[..POOL_V1_DEPOSIT_RECEIPT_BYTES])
        .map_err(DepositEventRecordErrorV1::DepositFormat)?;
    let event = DepositEventV1 {
        receipt,
        encrypted_note_payload: &bytes[POOL_V1_DEPOSIT_RECEIPT_BYTES..],
    };
    validate_deposit_event_v1(&event).map_err(DepositEventRecordErrorV1::DepositFormat)?;
    Ok(event)
}

/// Immutable public identity of the Pool scanned by one cursor.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DepositScanIdentityV1 {
    pool: [u8; 32],
    deployment_domain: [u8; 32],
    asset_mint: [u8; 32],
    vault_token_account: [u8; 32],
    asset_id: u32,
}

impl DepositScanIdentityV1 {
    pub fn new(
        pool: [u8; 32],
        deployment_domain: [u8; 32],
        asset_mint: [u8; 32],
        vault_token_account: [u8; 32],
        asset_id: u32,
    ) -> Result<Self, ScanStateErrorV1> {
        if pool == [0u8; 32]
            || deployment_domain == [0u8; 32]
            || asset_mint == [0u8; 32]
            || vault_token_account == [0u8; 32]
            || asset_id >= P
        {
            return Err(ScanStateErrorV1::InvalidIdentity);
        }
        Ok(Self {
            pool,
            deployment_domain,
            asset_mint,
            vault_token_account,
            asset_id,
        })
    }

    pub fn pool(&self) -> &[u8; 32] {
        &self.pool
    }

    pub fn deployment_domain(&self) -> &[u8; 32] {
        &self.deployment_domain
    }

    pub fn asset_mint(&self) -> &[u8; 32] {
        &self.asset_mint
    }

    pub fn vault_token_account(&self) -> &[u8; 32] {
        &self.vault_token_account
    }

    pub fn asset_id(&self) -> u32 {
        self.asset_id
    }
}

/// A block point whose finality was established outside this crate.
/// `ScanStateV1` can enforce linkage and rollback, but cannot query or prove
/// Solana RPC commitment itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FinalizedChainPointV1 {
    slot: u64,
    block_hash: [u8; 32],
}

impl FinalizedChainPointV1 {
    pub fn new(slot: u64, block_hash: [u8; 32]) -> Result<Self, ScanStateErrorV1> {
        if block_hash == [0u8; 32] {
            return Err(ScanStateErrorV1::InvalidChainPoint);
        }
        Ok(Self { slot, block_hash })
    }

    pub fn slot(&self) -> u64 {
        self.slot
    }

    pub fn block_hash(&self) -> &[u8; 32] {
        &self.block_hash
    }
}

/// One externally-finalized block plus its exact parent point. Solana may skip
/// slot numbers; only `parent_slot < slot` and exact parent equality matter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedBlockV1 {
    point: FinalizedChainPointV1,
    parent: FinalizedChainPointV1,
}

impl FinalizedBlockV1 {
    pub fn new(
        point: FinalizedChainPointV1,
        parent: FinalizedChainPointV1,
    ) -> Result<Self, ScanStateErrorV1> {
        if parent.slot >= point.slot {
            return Err(ScanStateErrorV1::InvalidChainPoint);
        }
        Ok(Self { point, parent })
    }

    pub fn point(&self) -> FinalizedChainPointV1 {
        self.point
    }

    pub fn parent(&self) -> FinalizedChainPointV1 {
        self.parent
    }
}

/// Stable event identity assigned by an authenticated transaction parser.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DepositEventIdV1 {
    point: FinalizedChainPointV1,
    transaction_signature: [u8; 64],
    instruction_index: u16,
    event_index: u16,
}

impl DepositEventIdV1 {
    pub fn new(
        point: FinalizedChainPointV1,
        transaction_signature: [u8; 64],
        instruction_index: u16,
        event_index: u16,
    ) -> Result<Self, ScanStateErrorV1> {
        if transaction_signature == [0u8; 64] {
            return Err(ScanStateErrorV1::InvalidEventIdentity);
        }
        Ok(Self {
            point,
            transaction_signature,
            instruction_index,
            event_index,
        })
    }

    pub fn point(&self) -> FinalizedChainPointV1 {
        self.point
    }

    pub fn transaction_signature(&self) -> &[u8; 64] {
        &self.transaction_signature
    }

    pub fn instruction_index(&self) -> u16 {
        self.instruction_index
    }

    pub fn event_index(&self) -> u16 {
        self.event_index
    }
}

/// One authenticated, externally-finalized deposit observation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedDepositRecordV1<'a> {
    pub id: DepositEventIdV1,
    pub record_bytes: &'a [u8],
}

/// One append output whose exact top-level Pool instruction, successful ASTR
/// receipt and historical root were authenticated by the finalized indexer.
/// No ciphertext or note opening is implied: private-transfer delivery is a
/// separate, recipient-authenticated wallet channel.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedPublicOutputRecordV1<'a> {
    pub id: DepositEventIdV1,
    pub pool: [u8; 32],
    pub leaf_index: u64,
    pub root_sequence: u64,
    pub note_commitment: [u8; 32],
    pub root: [u8; 32],
    pub authenticated_transport: &'a [u8],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PublicOutputScanOutcomeV1 {
    Duplicate,
    Advanced,
}

impl<'a> FinalizedDepositRecordV1<'a> {
    pub fn new(id: DepositEventIdV1, record_bytes: &'a [u8]) -> Self {
        Self { id, record_bytes }
    }
}

/// A spend-key store exposes only lookup by the already-public owner-key
/// digest. Implementations derive/index owner keys when importing local
/// secrets; no nullifier/spending-key byte enters this scanning API.
pub trait LocalOwnerKeyStoreV1 {
    fn contains_owner_key_v1(&self, owner_key: &[u8; 32]) -> bool;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LocalNoteOwnershipV1 {
    ViewOnly,
    Spendable,
}

/// Classify a recovered opening against the local owner-key index. Wallets may
/// call this again for securely stored view-only notes after importing a new
/// spend key; only the public owner key crosses the key-store boundary.
pub fn classify_local_note_ownership_v1(
    note: &NoteOpeningV1,
    local_keys: &impl LocalOwnerKeyStoreV1,
) -> LocalNoteOwnershipV1 {
    if local_keys.contains_owner_key_v1(note.owner_key()) {
        LocalNoteOwnershipV1::Spendable
    } else {
        LocalNoteOwnershipV1::ViewOnly
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RecoveredNoteConsistencyErrorV1 {
    AmountMismatch,
    AssetIdMismatch,
}

/// Recipient classification for one accepted chain event. All non-duplicate
/// variants have advanced the append cursor exactly once.
pub enum DepositScanOutcomeV1 {
    Duplicate,
    NotForViewingKey,
    /// The Pool permits opaque delivery payloads. Bad or non-v1 ciphertext
    /// is skipped after the receipt advances the global append cursor, which
    /// prevents an arbitrary depositor from permanently stalling a wallet.
    InvalidEncryptedPayload(PoolV1WalletError),
    /// HPKE and note-commitment checks passed, but the decrypted public fields
    /// disagreed with the configured/receipt fields. This should be
    /// cryptographically unreachable absent a commitment collision or bad
    /// configuration, so the opening is dropped and zeroized.
    InconsistentRecoveredNote(RecoveredNoteConsistencyErrorV1),
    /// Decrypted and commitment-checked, but no local owner-key match exists.
    ViewOnly(NoteOpeningV1),
    /// Decrypted, commitment-checked and explicitly matched to a locally
    /// indexed owner key. The spending/nullifier secret remains in the store.
    Spendable(NoteOpeningV1),
}

impl core::fmt::Debug for DepositScanOutcomeV1 {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Duplicate => formatter.write_str("Duplicate"),
            Self::NotForViewingKey => formatter.write_str("NotForViewingKey"),
            Self::InvalidEncryptedPayload(error) => formatter
                .debug_tuple("InvalidEncryptedPayload")
                .field(error)
                .finish(),
            Self::InconsistentRecoveredNote(error) => formatter
                .debug_tuple("InconsistentRecoveredNote")
                .field(error)
                .finish(),
            Self::ViewOnly(_) => formatter.write_str("ViewOnly([REDACTED])"),
            Self::Spendable(_) => formatter.write_str("Spendable([REDACTED])"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FinalizedBlockAdvanceV1 {
    Advanced,
    AlreadyCurrent,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RollbackSummaryV1 {
    pub removed_events: Vec<DepositEventIdV1>,
    pub next_leaf_index: u64,
    pub root: [u8; 32],
    pub head: FinalizedChainPointV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PruneSummaryV1 {
    pub pruned_block_count: usize,
    pub pruned_events: Vec<DepositEventIdV1>,
    pub anchor: FinalizedChainPointV1,
    pub next_leaf_index: u64,
    pub root: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScanStateErrorV1 {
    InvalidIdentity,
    InvalidChainPoint,
    InvalidEventIdentity,
    InvalidAnchor,
    WrongStateLength,
    WrongStateMagic,
    WrongStateVersion,
    NonZeroReserved,
    NonCanonicalDigest,
    CountOverflow,
    ChecksumMismatch,
    StateInvariant,
    ChainDiscontinuity,
    ReorgDetected,
    NoRetainedAncestor,
    NoAdvancedFinalizedBlock,
    EventOutsideCurrentBlock,
    EventIdentityConflict,
    DepositRecord(DepositEventRecordErrorV1),
    PoolMismatch,
    AssetMintMismatch,
    VaultMismatch,
    UnexpectedLeafIndex,
    TreeFull,
    InvalidNoteContext,
    InvalidPublicOutput,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct BlockCheckpointV1 {
    block: FinalizedBlockV1,
    next_leaf_index_before: u64,
    root_before: [u8; 32],
    processed_event_count_before: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ProcessedDepositEventV1 {
    id: DepositEventIdV1,
    leaf_index: u64,
    fingerprint: [u8; 32],
    note_commitment: [u8; 32],
    root: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ScanMigrationBlockV1 {
    pub block: FinalizedBlockV1,
    pub events: Vec<ScanMigrationEventV1>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ScanMigrationEventV1 {
    pub event_id: DepositEventIdV1,
    pub leaf_index: u64,
    pub note_commitment: [u8; 32],
    pub root: [u8; 32],
}

/// Serializable scan cursor with retained block checkpoints and event
/// fingerprints for idempotence. Persist the result of
/// [`encode_scan_state_v1`] atomically with any secure note-store update.
/// The state intentionally contains no decrypted note material or secret key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScanStateV1 {
    identity: DepositScanIdentityV1,
    anchor: FinalizedChainPointV1,
    anchor_next_leaf_index: u64,
    anchor_root: [u8; 32],
    next_leaf_index: u64,
    root: [u8; 32],
    blocks: Vec<BlockCheckpointV1>,
    processed_events: Vec<ProcessedDepositEventV1>,
}

impl ScanStateV1 {
    /// Create a cursor anchored *after* all events through `anchor`. Therefore
    /// the first accepted event must be in a later linked finalized block and
    /// have `leaf_index == next_leaf_index`.
    pub fn new(
        identity: DepositScanIdentityV1,
        anchor: FinalizedChainPointV1,
        next_leaf_index: u64,
        root: [u8; 32],
    ) -> Result<Self, ScanStateErrorV1> {
        if next_leaf_index > POOL_V1_LEAF_CAPACITY || decode_digest_canonical(&root).is_err() {
            return Err(ScanStateErrorV1::InvalidAnchor);
        }
        Ok(Self {
            identity,
            anchor,
            anchor_next_leaf_index: next_leaf_index,
            anchor_root: root,
            next_leaf_index,
            root,
            blocks: Vec::new(),
            processed_events: Vec::new(),
        })
    }

    pub fn identity(&self) -> &DepositScanIdentityV1 {
        &self.identity
    }

    pub fn anchor(&self) -> FinalizedChainPointV1 {
        self.anchor
    }

    pub fn head(&self) -> FinalizedChainPointV1 {
        self.blocks
            .last()
            .map_or(self.anchor, |checkpoint| checkpoint.block.point)
    }

    pub fn next_leaf_index(&self) -> u64 {
        self.next_leaf_index
    }

    pub fn root_sequence(&self) -> u64 {
        self.next_leaf_index
    }

    pub fn root(&self) -> &[u8; 32] {
        &self.root
    }

    pub fn retained_block_count(&self) -> usize {
        self.blocks.len()
    }

    pub fn retained_event_count(&self) -> usize {
        self.processed_events.len()
    }

    /// Whether `point` remains inside the durable rollback window. This is a
    /// read-only chain-membership query for indexers deciding whether an
    /// incoming finalized block is a direct child, a stale replay or a fork
    /// whose parent can be rolled back to.
    pub fn retains_chain_point_v1(&self, point: FinalizedChainPointV1) -> bool {
        point == self.anchor
            || self
                .blocks
                .iter()
                .any(|checkpoint| checkpoint.block.point == point)
    }

    /// Stable event ids retained for one block, in scan order. A finalized
    /// indexer uses this to require that replaying the current block presents
    /// the exact same event set rather than a truncated RPC response.
    pub fn retained_event_ids_in_block_v1(
        &self,
        point: FinalizedChainPointV1,
    ) -> Vec<DepositEventIdV1> {
        self.processed_events
            .iter()
            .filter(|event| event.id.point == point)
            .map(|event| event.id)
            .collect()
    }

    /// Canonical immutable view used only to prove exact ASDW/ASWJ agreement
    /// before a one-way V2 ownership transfer.
    pub(crate) fn migration_blocks_v1(&self) -> Vec<ScanMigrationBlockV1> {
        self.blocks
            .iter()
            .map(|checkpoint| ScanMigrationBlockV1 {
                block: checkpoint.block,
                events: self
                    .processed_events
                    .iter()
                    .filter(|event| event.id.point == checkpoint.block.point)
                    .map(|event| ScanMigrationEventV1 {
                        event_id: event.id,
                        leaf_index: event.leaf_index,
                        note_commitment: event.note_commitment,
                        root: event.root,
                    })
                    .collect(),
            })
            .collect()
    }

    /// Advance to one externally-finalized block. Replaying the current point
    /// is idempotent only if both point and parent are identical. A conflicting
    /// point never rewrites state; callers must explicitly roll back to a
    /// retained common ancestor first.
    pub fn advance_finalized_block_v1(
        &mut self,
        block: FinalizedBlockV1,
    ) -> Result<FinalizedBlockAdvanceV1, ScanStateErrorV1> {
        let head = self.head();
        if block.point == head {
            let expected_parent = self.blocks.last().map(|checkpoint| checkpoint.block.parent);
            return if expected_parent == Some(block.parent) {
                Ok(FinalizedBlockAdvanceV1::AlreadyCurrent)
            } else {
                Err(ScanStateErrorV1::ReorgDetected)
            };
        }
        if block.point.slot <= head.slot {
            return Err(ScanStateErrorV1::ReorgDetected);
        }
        if block.parent != head {
            return Err(ScanStateErrorV1::ChainDiscontinuity);
        }
        let processed_event_count_before = u32::try_from(self.processed_events.len())
            .map_err(|_| ScanStateErrorV1::CountOverflow)?;
        self.blocks.push(BlockCheckpointV1 {
            block,
            next_leaf_index_before: self.next_leaf_index,
            root_before: self.root,
            processed_event_count_before,
        });
        Ok(FinalizedBlockAdvanceV1::Advanced)
    }

    /// Roll back all retained blocks after `ancestor`, restoring the cursor
    /// and root that followed the ancestor. Removed event ids let a caller
    /// transactionally invalidate separately encrypted note records. Passing
    /// the current head is a no-op.
    pub fn rollback_to_v1(
        &mut self,
        ancestor: FinalizedChainPointV1,
    ) -> Result<RollbackSummaryV1, ScanStateErrorV1> {
        let keep_block_count = if ancestor == self.anchor {
            0
        } else {
            self.blocks
                .iter()
                .position(|checkpoint| checkpoint.block.point == ancestor)
                .map(|index| index + 1)
                .ok_or(ScanStateErrorV1::NoRetainedAncestor)?
        };

        if keep_block_count == self.blocks.len() {
            return Ok(RollbackSummaryV1 {
                removed_events: Vec::new(),
                next_leaf_index: self.next_leaf_index,
                root: self.root,
                head: self.head(),
            });
        }

        let first_removed = self.blocks[keep_block_count];
        let event_count = usize::try_from(first_removed.processed_event_count_before)
            .map_err(|_| ScanStateErrorV1::StateInvariant)?;
        if event_count > self.processed_events.len() {
            return Err(ScanStateErrorV1::StateInvariant);
        }
        let removed_events = self.processed_events[event_count..]
            .iter()
            .map(|event| event.id)
            .collect();
        self.processed_events.truncate(event_count);
        self.next_leaf_index = first_removed.next_leaf_index_before;
        self.root = first_removed.root_before;
        self.blocks.truncate(keep_block_count);

        Ok(RollbackSummaryV1 {
            removed_events,
            next_leaf_index: self.next_leaf_index,
            root: self.root,
            head: self.head(),
        })
    }

    /// Make a retained block the new durable anchor and discard rollback
    /// checkpoints through it. This bounds state growth when every finalized
    /// Solana block is tracked. Call it only after the corresponding note and
    /// dedup records are durably committed elsewhere; rollback before the new
    /// anchor then intentionally requires an external backfill.
    pub fn prune_finalized_history_through_v1(
        &mut self,
        ancestor: FinalizedChainPointV1,
    ) -> Result<PruneSummaryV1, ScanStateErrorV1> {
        if ancestor == self.anchor {
            return Ok(PruneSummaryV1 {
                pruned_block_count: 0,
                pruned_events: Vec::new(),
                anchor: self.anchor,
                next_leaf_index: self.anchor_next_leaf_index,
                root: self.anchor_root,
            });
        }
        let ancestor_index = self
            .blocks
            .iter()
            .position(|checkpoint| checkpoint.block.point == ancestor)
            .ok_or(ScanStateErrorV1::NoRetainedAncestor)?;
        let retained_start = ancestor_index + 1;
        let (anchor_next_leaf_index, anchor_root, pruned_event_count) =
            match self.blocks.get(retained_start) {
                Some(next_checkpoint) => (
                    next_checkpoint.next_leaf_index_before,
                    next_checkpoint.root_before,
                    usize::try_from(next_checkpoint.processed_event_count_before)
                        .map_err(|_| ScanStateErrorV1::StateInvariant)?,
                ),
                None => (self.next_leaf_index, self.root, self.processed_events.len()),
            };
        if pruned_event_count > self.processed_events.len() {
            return Err(ScanStateErrorV1::StateInvariant);
        }
        let pruned_event_count_u32 =
            u32::try_from(pruned_event_count).map_err(|_| ScanStateErrorV1::StateInvariant)?;
        if self.blocks[retained_start..]
            .iter()
            .any(|checkpoint| checkpoint.processed_event_count_before < pruned_event_count_u32)
        {
            return Err(ScanStateErrorV1::StateInvariant);
        }
        let pruned_events = self.processed_events[..pruned_event_count]
            .iter()
            .map(|event| event.id)
            .collect();

        self.blocks.drain(..retained_start);
        self.processed_events.drain(..pruned_event_count);
        for checkpoint in &mut self.blocks {
            checkpoint.processed_event_count_before -= pruned_event_count_u32;
        }
        self.anchor = ancestor;
        self.anchor_next_leaf_index = anchor_next_leaf_index;
        self.anchor_root = anchor_root;
        validate_state_invariants_v1(self)?;

        Ok(PruneSummaryV1 {
            pruned_block_count: retained_start,
            pruned_events,
            anchor: self.anchor,
            next_leaf_index: self.anchor_next_leaf_index,
            root: self.anchor_root,
        })
    }

    /// Accept one exact finalized deposit event and scan its encrypted
    /// delivery payload. Receipt/identity/order failures leave state unchanged.
    /// Once the public receipt is valid, an unrelated or malformed opaque
    /// payload still advances the global leaf cursor exactly once.
    pub fn ingest_finalized_deposit_v1(
        &mut self,
        observation: FinalizedDepositRecordV1<'_>,
        viewing_secret: &ViewingSecretKeyV1,
        local_keys: &impl LocalOwnerKeyStoreV1,
    ) -> Result<DepositScanOutcomeV1, ScanStateErrorV1> {
        let fingerprint = deposit_event_fingerprint_v1(observation.record_bytes)?;
        if let Some(previous) = self
            .processed_events
            .iter()
            .find(|event| event.id == observation.id)
        {
            return if bool::from(previous.fingerprint.ct_eq(&fingerprint)) {
                Ok(DepositScanOutcomeV1::Duplicate)
            } else {
                Err(ScanStateErrorV1::EventIdentityConflict)
            };
        }

        let current_block = self
            .blocks
            .last()
            .ok_or(ScanStateErrorV1::NoAdvancedFinalizedBlock)?;
        if observation.id.point != current_block.block.point {
            return Err(ScanStateErrorV1::EventOutsideCurrentBlock);
        }

        let event = decode_deposit_event_record_v1(observation.record_bytes)
            .map_err(ScanStateErrorV1::DepositRecord)?;
        self.validate_receipt_for_cursor(&event.receipt)?;

        let note_commitment = encode_digest_canonical(&event.receipt.note_commitment);
        let context = NoteContextV1::new(
            self.identity.pool,
            self.identity.deployment_domain,
            event.receipt.leaf_index,
            note_commitment,
        )
        .map_err(|_| ScanStateErrorV1::InvalidNoteContext)?;

        let outcome = match scan_note_v1(viewing_secret, &context, event.encrypted_note_payload) {
            Err(error) => DepositScanOutcomeV1::InvalidEncryptedPayload(error),
            Ok(ScanResultV1::NotForViewingKey) => DepositScanOutcomeV1::NotForViewingKey,
            Ok(ScanResultV1::RecoveredView(note)) => {
                if note.value() != event.receipt.amount {
                    DepositScanOutcomeV1::InconsistentRecoveredNote(
                        RecoveredNoteConsistencyErrorV1::AmountMismatch,
                    )
                } else if note.asset_id() != self.identity.asset_id {
                    DepositScanOutcomeV1::InconsistentRecoveredNote(
                        RecoveredNoteConsistencyErrorV1::AssetIdMismatch,
                    )
                } else {
                    match classify_local_note_ownership_v1(&note, local_keys) {
                        LocalNoteOwnershipV1::ViewOnly => DepositScanOutcomeV1::ViewOnly(note),
                        LocalNoteOwnershipV1::Spendable => DepositScanOutcomeV1::Spendable(note),
                    }
                }
            }
        };

        let next_leaf_index = self
            .next_leaf_index
            .checked_add(1)
            .ok_or(ScanStateErrorV1::TreeFull)?;
        let root = encode_digest_canonical(&event.receipt.root);
        self.processed_events.push(ProcessedDepositEventV1 {
            id: observation.id,
            leaf_index: event.receipt.leaf_index,
            fingerprint,
            note_commitment,
            root,
        });
        self.next_leaf_index = next_leaf_index;
        self.root = root;
        Ok(outcome)
    }

    /// Advance over one non-deposit Pool output after exact instruction,
    /// receipt and root-page authentication. The durable image retains only
    /// public commitment/root metadata and a domain-separated fingerprint.
    pub fn ingest_finalized_public_output_v1(
        &mut self,
        observation: FinalizedPublicOutputRecordV1<'_>,
    ) -> Result<PublicOutputScanOutcomeV1, ScanStateErrorV1> {
        let fingerprint = public_output_fingerprint_v1(
            observation.id.event_index,
            observation.authenticated_transport,
        )?;
        if let Some(previous) = self
            .processed_events
            .iter()
            .find(|event| event.id == observation.id)
        {
            return if bool::from(previous.fingerprint.ct_eq(&fingerprint)) {
                Ok(PublicOutputScanOutcomeV1::Duplicate)
            } else {
                Err(ScanStateErrorV1::EventIdentityConflict)
            };
        }
        let current_block = self
            .blocks
            .last()
            .ok_or(ScanStateErrorV1::NoAdvancedFinalizedBlock)?;
        if observation.id.point != current_block.block.point {
            return Err(ScanStateErrorV1::EventOutsideCurrentBlock);
        }
        if observation.pool != self.identity.pool {
            return Err(ScanStateErrorV1::PoolMismatch);
        }
        if self.next_leaf_index >= POOL_V1_LEAF_CAPACITY {
            return Err(ScanStateErrorV1::TreeFull);
        }
        if observation.leaf_index != self.next_leaf_index
            || observation.root_sequence != observation.leaf_index.saturating_add(1)
        {
            return Err(ScanStateErrorV1::UnexpectedLeafIndex);
        }
        if observation.authenticated_transport.is_empty()
            || decode_digest_canonical(&observation.note_commitment).is_err()
            || decode_digest_canonical(&observation.root).is_err()
        {
            return Err(ScanStateErrorV1::InvalidPublicOutput);
        }
        let next_leaf_index = self
            .next_leaf_index
            .checked_add(1)
            .ok_or(ScanStateErrorV1::TreeFull)?;
        self.processed_events.push(ProcessedDepositEventV1 {
            id: observation.id,
            leaf_index: observation.leaf_index,
            fingerprint,
            note_commitment: observation.note_commitment,
            root: observation.root,
        });
        self.next_leaf_index = next_leaf_index;
        self.root = observation.root;
        Ok(PublicOutputScanOutcomeV1::Advanced)
    }

    fn validate_receipt_for_cursor(
        &self,
        receipt: &DepositReceiptV1,
    ) -> Result<(), ScanStateErrorV1> {
        if receipt.pool != self.identity.pool {
            return Err(ScanStateErrorV1::PoolMismatch);
        }
        if receipt.asset_mint != self.identity.asset_mint {
            return Err(ScanStateErrorV1::AssetMintMismatch);
        }
        if receipt.vault_token_account != self.identity.vault_token_account {
            return Err(ScanStateErrorV1::VaultMismatch);
        }
        if self.next_leaf_index >= POOL_V1_LEAF_CAPACITY {
            return Err(ScanStateErrorV1::TreeFull);
        }
        if receipt.leaf_index != self.next_leaf_index
            || receipt.root_sequence != self.next_leaf_index + 1
        {
            return Err(ScanStateErrorV1::UnexpectedLeafIndex);
        }
        Ok(())
    }
}

fn deposit_event_fingerprint_v1(bytes: &[u8]) -> Result<[u8; 32], ScanStateErrorV1> {
    if bytes.len() < POOL_V1_DEPOSIT_RECEIPT_BYTES || bytes.len() > POOL_V1_DEPOSIT_RETURN_MAX_BYTES
    {
        return Err(ScanStateErrorV1::DepositRecord(
            DepositEventRecordErrorV1::WrongLength,
        ));
    }
    let length = u32::try_from(bytes.len()).map_err(|_| ScanStateErrorV1::CountOverflow)?;
    let mut hasher = Sha256::new();
    hasher.update(POOL_V1_DEPOSIT_EVENT_FINGERPRINT_DOMAIN);
    hasher.update(length.to_le_bytes());
    hasher.update(bytes);
    Ok(hasher.finalize().into())
}

fn public_output_fingerprint_v1(
    event_index: u16,
    bytes: &[u8],
) -> Result<[u8; 32], ScanStateErrorV1> {
    let length = u32::try_from(bytes.len()).map_err(|_| ScanStateErrorV1::CountOverflow)?;
    let mut hasher = Sha256::new();
    hasher.update(POOL_V1_PUBLIC_OUTPUT_FINGERPRINT_DOMAIN);
    hasher.update(event_index.to_le_bytes());
    hasher.update(length.to_le_bytes());
    hasher.update(bytes);
    Ok(hasher.finalize().into())
}

/// Encode the complete public scan cursor as one canonical, versioned image.
/// This function has no key/note argument and the image contains no decrypted
/// material. The caller supplies atomic/fsync semantics appropriate to its
/// database or file system.
pub fn encode_scan_state_v1(state: &ScanStateV1) -> Result<Vec<u8>, ScanStateErrorV1> {
    validate_state_invariants_v1(state)?;
    let block_count =
        u32::try_from(state.blocks.len()).map_err(|_| ScanStateErrorV1::CountOverflow)?;
    let event_count =
        u32::try_from(state.processed_events.len()).map_err(|_| ScanStateErrorV1::CountOverflow)?;
    let total_length = state_image_length_v1(state.blocks.len(), state.processed_events.len())?;
    let mut output = vec![0u8; total_length];

    output[..4].copy_from_slice(&POOL_V1_SCAN_STATE_MAGIC);
    output[4] = POOL_V1_SCAN_STATE_VERSION;
    output[5] = POOL_V1_SCAN_STATE_DIGEST_ENCODING_VERSION;
    output[STATE_POOL_OFFSET..STATE_DEPLOYMENT_DOMAIN_OFFSET].copy_from_slice(&state.identity.pool);
    output[STATE_DEPLOYMENT_DOMAIN_OFFSET..STATE_ASSET_MINT_OFFSET]
        .copy_from_slice(&state.identity.deployment_domain);
    output[STATE_ASSET_MINT_OFFSET..STATE_VAULT_OFFSET].copy_from_slice(&state.identity.asset_mint);
    output[STATE_VAULT_OFFSET..STATE_ASSET_ID_OFFSET]
        .copy_from_slice(&state.identity.vault_token_account);
    output[STATE_ASSET_ID_OFFSET..140].copy_from_slice(&state.identity.asset_id.to_le_bytes());
    output[STATE_ANCHOR_SLOT_OFFSET..STATE_ANCHOR_HASH_OFFSET]
        .copy_from_slice(&state.anchor.slot.to_le_bytes());
    output[STATE_ANCHOR_HASH_OFFSET..STATE_ANCHOR_NEXT_LEAF_OFFSET]
        .copy_from_slice(&state.anchor.block_hash);
    output[STATE_ANCHOR_NEXT_LEAF_OFFSET..STATE_ANCHOR_ROOT_OFFSET]
        .copy_from_slice(&state.anchor_next_leaf_index.to_le_bytes());
    output[STATE_ANCHOR_ROOT_OFFSET..STATE_HEAD_SLOT_OFFSET].copy_from_slice(&state.anchor_root);
    let head = state.head();
    output[STATE_HEAD_SLOT_OFFSET..STATE_HEAD_HASH_OFFSET]
        .copy_from_slice(&head.slot.to_le_bytes());
    output[STATE_HEAD_HASH_OFFSET..STATE_NEXT_LEAF_OFFSET].copy_from_slice(&head.block_hash);
    output[STATE_NEXT_LEAF_OFFSET..STATE_ROOT_OFFSET]
        .copy_from_slice(&state.next_leaf_index.to_le_bytes());
    output[STATE_ROOT_OFFSET..STATE_BLOCK_COUNT_OFFSET].copy_from_slice(&state.root);
    output[STATE_BLOCK_COUNT_OFFSET..STATE_EVENT_COUNT_OFFSET]
        .copy_from_slice(&block_count.to_le_bytes());
    output[STATE_EVENT_COUNT_OFFSET..STATE_CHECKSUM_OFFSET]
        .copy_from_slice(&event_count.to_le_bytes());

    let mut offset = POOL_V1_SCAN_STATE_HEADER_BYTES;
    for checkpoint in &state.blocks {
        let bytes = &mut output[offset..offset + POOL_V1_SCAN_STATE_BLOCK_BYTES];
        bytes[BLOCK_SLOT_OFFSET..BLOCK_HASH_OFFSET]
            .copy_from_slice(&checkpoint.block.point.slot.to_le_bytes());
        bytes[BLOCK_HASH_OFFSET..BLOCK_PARENT_SLOT_OFFSET]
            .copy_from_slice(&checkpoint.block.point.block_hash);
        bytes[BLOCK_PARENT_SLOT_OFFSET..BLOCK_PARENT_HASH_OFFSET]
            .copy_from_slice(&checkpoint.block.parent.slot.to_le_bytes());
        bytes[BLOCK_PARENT_HASH_OFFSET..BLOCK_NEXT_LEAF_BEFORE_OFFSET]
            .copy_from_slice(&checkpoint.block.parent.block_hash);
        bytes[BLOCK_NEXT_LEAF_BEFORE_OFFSET..BLOCK_ROOT_BEFORE_OFFSET]
            .copy_from_slice(&checkpoint.next_leaf_index_before.to_le_bytes());
        bytes[BLOCK_ROOT_BEFORE_OFFSET..BLOCK_EVENT_COUNT_BEFORE_OFFSET]
            .copy_from_slice(&checkpoint.root_before);
        bytes[BLOCK_EVENT_COUNT_BEFORE_OFFSET..124]
            .copy_from_slice(&checkpoint.processed_event_count_before.to_le_bytes());
        offset += POOL_V1_SCAN_STATE_BLOCK_BYTES;
    }
    for event in &state.processed_events {
        let bytes = &mut output[offset..offset + POOL_V1_SCAN_STATE_EVENT_BYTES];
        bytes[EVENT_SLOT_OFFSET..EVENT_BLOCK_HASH_OFFSET]
            .copy_from_slice(&event.id.point.slot.to_le_bytes());
        bytes[EVENT_BLOCK_HASH_OFFSET..EVENT_SIGNATURE_OFFSET]
            .copy_from_slice(&event.id.point.block_hash);
        bytes[EVENT_SIGNATURE_OFFSET..EVENT_INSTRUCTION_INDEX_OFFSET]
            .copy_from_slice(&event.id.transaction_signature);
        bytes[EVENT_INSTRUCTION_INDEX_OFFSET..EVENT_INDEX_OFFSET]
            .copy_from_slice(&event.id.instruction_index.to_le_bytes());
        bytes[EVENT_INDEX_OFFSET..EVENT_LEAF_INDEX_OFFSET]
            .copy_from_slice(&event.id.event_index.to_le_bytes());
        bytes[EVENT_LEAF_INDEX_OFFSET..EVENT_FINGERPRINT_OFFSET]
            .copy_from_slice(&event.leaf_index.to_le_bytes());
        bytes[EVENT_FINGERPRINT_OFFSET..EVENT_COMMITMENT_OFFSET]
            .copy_from_slice(&event.fingerprint);
        bytes[EVENT_COMMITMENT_OFFSET..EVENT_ROOT_OFFSET].copy_from_slice(&event.note_commitment);
        bytes[EVENT_ROOT_OFFSET..].copy_from_slice(&event.root);
        offset += POOL_V1_SCAN_STATE_EVENT_BYTES;
    }
    debug_assert_eq!(offset, output.len());
    let checksum = scan_state_checksum_v1(&output)?;
    output[STATE_CHECKSUM_OFFSET..POOL_V1_SCAN_STATE_HEADER_BYTES].copy_from_slice(&checksum);
    Ok(output)
}

/// Decode and fully validate a canonical scan-state image. Counts, exact
/// length, reserved bytes, digest encodings, block linkage, event uniqueness,
/// leaf order, checkpoint snapshots, head, root and cursor are all checked.
pub fn decode_scan_state_v1(bytes: &[u8]) -> Result<ScanStateV1, ScanStateErrorV1> {
    if bytes.len() < POOL_V1_SCAN_STATE_HEADER_BYTES {
        return Err(ScanStateErrorV1::WrongStateLength);
    }
    if bytes[..4] != POOL_V1_SCAN_STATE_MAGIC {
        return Err(ScanStateErrorV1::WrongStateMagic);
    }
    if bytes[4] != POOL_V1_SCAN_STATE_VERSION
        || bytes[5] != POOL_V1_SCAN_STATE_DIGEST_ENCODING_VERSION
    {
        return Err(ScanStateErrorV1::WrongStateVersion);
    }
    if bytes[6..8] != [0u8; 2] || bytes[140..144] != [0u8; 4] {
        return Err(ScanStateErrorV1::NonZeroReserved);
    }

    let block_count = read_u32(bytes, STATE_BLOCK_COUNT_OFFSET)? as usize;
    let event_count = read_u32(bytes, STATE_EVENT_COUNT_OFFSET)? as usize;
    if state_image_length_v1(block_count, event_count)? != bytes.len() {
        return Err(ScanStateErrorV1::WrongStateLength);
    }
    let encoded_checksum: [u8; 32] = read_array(bytes, STATE_CHECKSUM_OFFSET)?;
    let expected_checksum = scan_state_checksum_v1(bytes)?;
    if !bool::from(encoded_checksum.ct_eq(&expected_checksum)) {
        return Err(ScanStateErrorV1::ChecksumMismatch);
    }

    let identity = DepositScanIdentityV1::new(
        read_array(bytes, STATE_POOL_OFFSET)?,
        read_array(bytes, STATE_DEPLOYMENT_DOMAIN_OFFSET)?,
        read_array(bytes, STATE_ASSET_MINT_OFFSET)?,
        read_array(bytes, STATE_VAULT_OFFSET)?,
        read_u32(bytes, STATE_ASSET_ID_OFFSET)?,
    )?;
    let anchor = FinalizedChainPointV1::new(
        read_u64(bytes, STATE_ANCHOR_SLOT_OFFSET)?,
        read_array(bytes, STATE_ANCHOR_HASH_OFFSET)?,
    )?;
    let anchor_next_leaf_index = read_u64(bytes, STATE_ANCHOR_NEXT_LEAF_OFFSET)?;
    let anchor_root = read_array(bytes, STATE_ANCHOR_ROOT_OFFSET)?;
    let encoded_head = FinalizedChainPointV1::new(
        read_u64(bytes, STATE_HEAD_SLOT_OFFSET)?,
        read_array(bytes, STATE_HEAD_HASH_OFFSET)?,
    )?;
    let next_leaf_index = read_u64(bytes, STATE_NEXT_LEAF_OFFSET)?;
    let root = read_array(bytes, STATE_ROOT_OFFSET)?;

    let mut offset = POOL_V1_SCAN_STATE_HEADER_BYTES;
    let mut blocks = Vec::new();
    blocks
        .try_reserve_exact(block_count)
        .map_err(|_| ScanStateErrorV1::CountOverflow)?;
    for _ in 0..block_count {
        let entry = &bytes[offset..offset + POOL_V1_SCAN_STATE_BLOCK_BYTES];
        if entry[124..128] != [0u8; 4] {
            return Err(ScanStateErrorV1::NonZeroReserved);
        }
        let point = FinalizedChainPointV1::new(
            read_u64(entry, BLOCK_SLOT_OFFSET)?,
            read_array(entry, BLOCK_HASH_OFFSET)?,
        )?;
        let parent = FinalizedChainPointV1::new(
            read_u64(entry, BLOCK_PARENT_SLOT_OFFSET)?,
            read_array(entry, BLOCK_PARENT_HASH_OFFSET)?,
        )?;
        let block = FinalizedBlockV1::new(point, parent)?;
        blocks.push(BlockCheckpointV1 {
            block,
            next_leaf_index_before: read_u64(entry, BLOCK_NEXT_LEAF_BEFORE_OFFSET)?,
            root_before: read_array(entry, BLOCK_ROOT_BEFORE_OFFSET)?,
            processed_event_count_before: read_u32(entry, BLOCK_EVENT_COUNT_BEFORE_OFFSET)?,
        });
        offset += POOL_V1_SCAN_STATE_BLOCK_BYTES;
    }

    let mut processed_events = Vec::new();
    processed_events
        .try_reserve_exact(event_count)
        .map_err(|_| ScanStateErrorV1::CountOverflow)?;
    for _ in 0..event_count {
        let entry = &bytes[offset..offset + POOL_V1_SCAN_STATE_EVENT_BYTES];
        let point = FinalizedChainPointV1::new(
            read_u64(entry, EVENT_SLOT_OFFSET)?,
            read_array(entry, EVENT_BLOCK_HASH_OFFSET)?,
        )?;
        let id = DepositEventIdV1::new(
            point,
            read_array(entry, EVENT_SIGNATURE_OFFSET)?,
            read_u16(entry, EVENT_INSTRUCTION_INDEX_OFFSET)?,
            read_u16(entry, EVENT_INDEX_OFFSET)?,
        )?;
        processed_events.push(ProcessedDepositEventV1 {
            id,
            leaf_index: read_u64(entry, EVENT_LEAF_INDEX_OFFSET)?,
            fingerprint: read_array(entry, EVENT_FINGERPRINT_OFFSET)?,
            note_commitment: read_array(entry, EVENT_COMMITMENT_OFFSET)?,
            root: read_array(entry, EVENT_ROOT_OFFSET)?,
        });
        offset += POOL_V1_SCAN_STATE_EVENT_BYTES;
    }

    let state = ScanStateV1 {
        identity,
        anchor,
        anchor_next_leaf_index,
        anchor_root,
        next_leaf_index,
        root,
        blocks,
        processed_events,
    };
    validate_state_invariants_v1(&state)?;
    if state.head() != encoded_head {
        return Err(ScanStateErrorV1::StateInvariant);
    }
    Ok(state)
}

fn state_image_length_v1(
    block_count: usize,
    event_count: usize,
) -> Result<usize, ScanStateErrorV1> {
    POOL_V1_SCAN_STATE_HEADER_BYTES
        .checked_add(
            block_count
                .checked_mul(POOL_V1_SCAN_STATE_BLOCK_BYTES)
                .ok_or(ScanStateErrorV1::CountOverflow)?,
        )
        .and_then(|length| {
            event_count
                .checked_mul(POOL_V1_SCAN_STATE_EVENT_BYTES)
                .and_then(|event_bytes| length.checked_add(event_bytes))
        })
        .ok_or(ScanStateErrorV1::CountOverflow)
}

fn scan_state_checksum_v1(bytes: &[u8]) -> Result<[u8; 32], ScanStateErrorV1> {
    let length = u64::try_from(bytes.len()).map_err(|_| ScanStateErrorV1::CountOverflow)?;
    let mut hasher = Sha256::new();
    hasher.update(POOL_V1_SCAN_STATE_CHECKSUM_DOMAIN);
    hasher.update(length.to_le_bytes());
    if bytes.len() >= POOL_V1_SCAN_STATE_HEADER_BYTES {
        hasher.update(&bytes[..STATE_CHECKSUM_OFFSET]);
        hasher.update([0u8; 32]);
        hasher.update(&bytes[POOL_V1_SCAN_STATE_HEADER_BYTES..]);
    } else {
        hasher.update(bytes);
    }
    Ok(hasher.finalize().into())
}

fn validate_state_invariants_v1(state: &ScanStateV1) -> Result<(), ScanStateErrorV1> {
    use std::collections::HashSet;

    if state.anchor_next_leaf_index > POOL_V1_LEAF_CAPACITY
        || decode_digest_canonical(&state.anchor_root).is_err()
        || state.next_leaf_index > POOL_V1_LEAF_CAPACITY
        || decode_digest_canonical(&state.root).is_err()
    {
        return Err(ScanStateErrorV1::StateInvariant);
    }
    if state.blocks.is_empty() && !state.processed_events.is_empty() {
        return Err(ScanStateErrorV1::StateInvariant);
    }

    let mut point = state.anchor;
    let mut next_leaf_index = state.anchor_next_leaf_index;
    let mut root = state.anchor_root;
    let mut event_offset = 0usize;
    let mut identities = HashSet::with_capacity(state.processed_events.len());

    for (block_index, checkpoint) in state.blocks.iter().enumerate() {
        if checkpoint.block.parent != point
            || checkpoint.block.point.slot <= checkpoint.block.parent.slot
            || checkpoint.next_leaf_index_before != next_leaf_index
            || checkpoint.root_before != root
            || usize::try_from(checkpoint.processed_event_count_before).ok() != Some(event_offset)
            || decode_digest_canonical(&checkpoint.root_before).is_err()
        {
            return Err(ScanStateErrorV1::StateInvariant);
        }

        let next_event_offset = match state.blocks.get(block_index + 1) {
            Some(next_checkpoint) => usize::try_from(next_checkpoint.processed_event_count_before)
                .map_err(|_| ScanStateErrorV1::StateInvariant)?,
            None => state.processed_events.len(),
        };
        if next_event_offset < event_offset || next_event_offset > state.processed_events.len() {
            return Err(ScanStateErrorV1::StateInvariant);
        }
        for event in &state.processed_events[event_offset..next_event_offset] {
            if event.id.point != checkpoint.block.point
                || event.leaf_index != next_leaf_index
                || next_leaf_index >= POOL_V1_LEAF_CAPACITY
                || decode_digest_canonical(&event.note_commitment).is_err()
                || decode_digest_canonical(&event.root).is_err()
                || !identities.insert(event.id)
            {
                return Err(ScanStateErrorV1::StateInvariant);
            }
            next_leaf_index = next_leaf_index
                .checked_add(1)
                .ok_or(ScanStateErrorV1::StateInvariant)?;
            root = event.root;
        }
        event_offset = next_event_offset;
        point = checkpoint.block.point;
    }

    if event_offset != state.processed_events.len()
        || next_leaf_index != state.next_leaf_index
        || root != state.root
    {
        return Err(ScanStateErrorV1::StateInvariant);
    }
    Ok(())
}

fn read_u16(bytes: &[u8], offset: usize) -> Result<u16, ScanStateErrorV1> {
    Ok(u16::from_le_bytes(read_array(bytes, offset)?))
}

fn read_u32(bytes: &[u8], offset: usize) -> Result<u32, ScanStateErrorV1> {
    Ok(u32::from_le_bytes(read_array(bytes, offset)?))
}

fn read_u64(bytes: &[u8], offset: usize) -> Result<u64, ScanStateErrorV1> {
    Ok(u64::from_le_bytes(read_array(bytes, offset)?))
}

fn read_array<const N: usize>(bytes: &[u8], offset: usize) -> Result<[u8; N], ScanStateErrorV1> {
    bytes
        .get(
            offset
                ..offset
                    .checked_add(N)
                    .ok_or(ScanStateErrorV1::WrongStateLength)?,
        )
        .ok_or(ScanStateErrorV1::WrongStateLength)?
        .try_into()
        .map_err(|_| ScanStateErrorV1::WrongStateLength)
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_statement::{derive_owner_key, pool_v1::POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES};
    use core::convert::Infallible;
    use hpke::rand_core::{TryCryptoRng, TryRng};

    use crate::{
        derive_viewing_keypair_v1, encrypt_note_v1, recompute_note_commitment_v1,
        ViewingPublicKeyV1,
    };

    struct FixedTestRng {
        next: u8,
    }

    impl FixedTestRng {
        fn new(next: u8) -> Self {
            Self { next }
        }
    }

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
                *byte = self.next;
                self.next = self.next.wrapping_add(1);
            }
            Ok(())
        }
    }

    impl TryCryptoRng for FixedTestRng {}

    #[derive(Default)]
    struct OwnerKeyStore {
        owner_keys: Vec<[u8; 32]>,
    }

    impl LocalOwnerKeyStoreV1 for OwnerKeyStore {
        fn contains_owner_key_v1(&self, owner_key: &[u8; 32]) -> bool {
            self.owner_keys
                .iter()
                .any(|candidate| bool::from(candidate.ct_eq(owner_key)))
        }
    }

    fn digest_bytes(seed: u32) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        for index in 0..8 {
            bytes[index * 4..index * 4 + 4]
                .copy_from_slice(&(seed + index as u32 * 17).to_le_bytes());
        }
        bytes
    }

    fn identity() -> DepositScanIdentityV1 {
        DepositScanIdentityV1::new([0x11; 32], [0x22; 32], [0x33; 32], [0x44; 32], 9).unwrap()
    }

    fn point(slot: u64, byte: u8) -> FinalizedChainPointV1 {
        FinalizedChainPointV1::new(slot, [byte; 32]).unwrap()
    }

    fn block(parent: FinalizedChainPointV1, slot: u64, byte: u8) -> FinalizedBlockV1 {
        FinalizedBlockV1::new(point(slot, byte), parent).unwrap()
    }

    fn state() -> ScanStateV1 {
        ScanStateV1::new(identity(), point(100, 0xa0), 7, digest_bytes(700)).unwrap()
    }

    fn event_id(
        point: FinalizedChainPointV1,
        signature_byte: u8,
        event_index: u16,
    ) -> DepositEventIdV1 {
        DepositEventIdV1::new(point, [signature_byte; 64], 2, event_index).unwrap()
    }

    fn owner_key(nullifier_key_bytes: &[u8; 32]) -> [u8; 32] {
        let nullifier_key = decode_digest_canonical(nullifier_key_bytes).unwrap();
        encode_digest_canonical(&derive_owner_key(&nullifier_key))
    }

    fn encrypted_record(
        viewing_public: &ViewingPublicKeyV1,
        owner_key: [u8; 32],
        leaf_index: u64,
        root: [u8; 32],
        rng_byte: u8,
    ) -> Vec<u8> {
        let note =
            NoteOpeningV1::new(owner_key, 77, 9, digest_bytes(900 + leaf_index as u32)).unwrap();
        let commitment = recompute_note_commitment_v1(&note).unwrap();
        let context = NoteContextV1::new(
            *identity().pool(),
            *identity().deployment_domain(),
            leaf_index,
            commitment,
        )
        .unwrap();
        let payload = encrypt_note_v1(
            &mut FixedTestRng::new(rng_byte),
            viewing_public,
            &context,
            &note,
        )
        .unwrap();
        assert!(payload.len() <= POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES);
        let receipt = DepositReceiptV1 {
            pool: *identity().pool(),
            asset_mint: *identity().asset_mint(),
            source_token_account: [0x55; 32],
            vault_token_account: *identity().vault_token_account(),
            amount: 77,
            encrypted_note_payload_bytes: payload.len() as u16,
            note_commitment: decode_digest_canonical(&commitment).unwrap(),
            leaf_index,
            root_sequence: leaf_index + 1,
            root: decode_digest_canonical(&root).unwrap(),
        };
        encode_deposit_event_record_v1(&DepositEventV1 {
            receipt,
            encrypted_note_payload: &payload,
        })
        .unwrap()
    }

    fn opaque_record(leaf_index: u64, root: [u8; 32], payload: &[u8]) -> Vec<u8> {
        let receipt = DepositReceiptV1 {
            pool: *identity().pool(),
            asset_mint: *identity().asset_mint(),
            source_token_account: [0x55; 32],
            vault_token_account: *identity().vault_token_account(),
            amount: 77,
            encrypted_note_payload_bytes: payload.len() as u16,
            note_commitment: decode_digest_canonical(&digest_bytes(500 + leaf_index as u32))
                .unwrap(),
            leaf_index,
            root_sequence: leaf_index + 1,
            root: decode_digest_canonical(&root).unwrap(),
        };
        encode_deposit_event_record_v1(&DepositEventV1 {
            receipt,
            encrypted_note_payload: payload,
        })
        .unwrap()
    }

    #[test]
    fn exact_deposit_record_rejects_truncation_trailing_bytes_and_reserved_bits() {
        let record = opaque_record(7, digest_bytes(701), &[1, 2, 3, 4]);
        let decoded = decode_deposit_event_record_v1(&record).unwrap();
        assert_eq!(decoded.receipt.leaf_index, 7);
        assert_eq!(decoded.encrypted_note_payload, [1, 2, 3, 4]);
        assert_eq!(encode_deposit_event_record_v1(&decoded).unwrap(), record);

        assert_eq!(
            decode_deposit_event_record_v1(&record[..POOL_V1_DEPOSIT_RECEIPT_BYTES - 1]),
            Err(DepositEventRecordErrorV1::WrongLength)
        );
        let mut trailing = record.clone();
        trailing.push(5);
        assert_eq!(
            decode_deposit_event_record_v1(&trailing),
            Err(DepositEventRecordErrorV1::DepositFormat(
                PoolV1DepositFormatError::InvalidPayloadLength
            ))
        );
        let mut reserved = record;
        reserved[5] = 1;
        assert_eq!(
            decode_deposit_event_record_v1(&reserved),
            Err(DepositEventRecordErrorV1::DepositFormat(
                PoolV1DepositFormatError::NonZeroReserved
            ))
        );
    }

    #[test]
    fn owned_event_is_spendable_durable_idempotent_and_secret_free() {
        let nullifier_key_bytes = digest_bytes(100);
        let owner_key = owner_key(&nullifier_key_bytes);
        assert_ne!(owner_key, nullifier_key_bytes);
        let (viewing_secret, viewing_public) = derive_viewing_keypair_v1(&[0x42; 32]).unwrap();
        let keys = OwnerKeyStore {
            owner_keys: vec![owner_key],
        };
        let mut state = state();
        let finalized = block(state.head(), 101, 0xa1);
        assert_eq!(
            state.advance_finalized_block_v1(finalized),
            Ok(FinalizedBlockAdvanceV1::Advanced)
        );
        let record = encrypted_record(&viewing_public, owner_key, 7, digest_bytes(701), 0x80);
        let id = event_id(finalized.point(), 0x61, 0);
        let observation = FinalizedDepositRecordV1::new(id, &record);
        let note = match state
            .ingest_finalized_deposit_v1(observation, &viewing_secret, &keys)
            .unwrap()
        {
            DepositScanOutcomeV1::Spendable(note) => note,
            other => panic!("expected spendable note, got {other:?}"),
        };
        assert_eq!(note.owner_key(), &owner_key);
        assert_eq!(note.value(), 77);
        assert_eq!(note.asset_id(), 9);
        assert_eq!(state.next_leaf_index(), 8);
        assert_eq!(state.root(), &digest_bytes(701));

        let encoded = encode_scan_state_v1(&state).unwrap();
        assert_eq!(
            encoded.len(),
            POOL_V1_SCAN_STATE_HEADER_BYTES
                + POOL_V1_SCAN_STATE_BLOCK_BYTES
                + POOL_V1_SCAN_STATE_EVENT_BYTES
        );
        assert!(!encoded
            .windows(nullifier_key_bytes.len())
            .any(|window| window == nullifier_key_bytes));
        assert!(!encoded
            .windows(owner_key.len())
            .any(|window| window == owner_key));

        let mut restored = decode_scan_state_v1(&encoded).unwrap();
        assert_eq!(restored, state);
        assert!(matches!(
            restored
                .ingest_finalized_deposit_v1(observation, &viewing_secret, &keys)
                .unwrap(),
            DepositScanOutcomeV1::Duplicate
        ));
        assert_eq!(restored.next_leaf_index(), 8);

        let mut changed_record = record;
        *changed_record.last_mut().unwrap() ^= 1;
        assert!(matches!(
            restored.ingest_finalized_deposit_v1(
                FinalizedDepositRecordV1::new(id, &changed_record),
                &viewing_secret,
                &keys,
            ),
            Err(ScanStateErrorV1::EventIdentityConflict)
        ));

        let mut corrupt = encoded;
        corrupt[STATE_ROOT_OFFSET] ^= 1;
        assert_eq!(
            decode_scan_state_v1(&corrupt),
            Err(ScanStateErrorV1::ChecksumMismatch)
        );
    }

    #[test]
    fn local_owner_key_match_promotes_view_only_without_exposing_a_secret() {
        let nullifier_key_bytes = digest_bytes(100);
        let owner_key = owner_key(&nullifier_key_bytes);
        let (viewing_secret, viewing_public) = derive_viewing_keypair_v1(&[0x42; 32]).unwrap();
        let record = encrypted_record(&viewing_public, owner_key, 7, digest_bytes(701), 0x80);

        let mut view_state = state();
        let view_block = block(view_state.head(), 101, 0xa1);
        view_state.advance_finalized_block_v1(view_block).unwrap();
        let view = view_state
            .ingest_finalized_deposit_v1(
                FinalizedDepositRecordV1::new(event_id(view_block.point(), 0x61, 0), &record),
                &viewing_secret,
                &OwnerKeyStore::default(),
            )
            .unwrap();
        let view_note = match view {
            DepositScanOutcomeV1::ViewOnly(note) => note,
            other => panic!("expected view-only note, got {other:?}"),
        };
        assert_eq!(
            classify_local_note_ownership_v1(&view_note, &OwnerKeyStore::default()),
            LocalNoteOwnershipV1::ViewOnly
        );
        assert_eq!(
            classify_local_note_ownership_v1(
                &view_note,
                &OwnerKeyStore {
                    owner_keys: vec![owner_key],
                },
            ),
            LocalNoteOwnershipV1::Spendable
        );

        let mut owned_state = state();
        let owned_block = block(owned_state.head(), 101, 0xa1);
        owned_state.advance_finalized_block_v1(owned_block).unwrap();
        let owned = owned_state
            .ingest_finalized_deposit_v1(
                FinalizedDepositRecordV1::new(event_id(owned_block.point(), 0x61, 0), &record),
                &viewing_secret,
                &OwnerKeyStore {
                    owner_keys: vec![owner_key],
                },
            )
            .unwrap();
        assert!(matches!(owned, DepositScanOutcomeV1::Spendable(_)));
    }

    #[test]
    fn opaque_or_other_recipient_payload_advances_without_stalling_the_cursor() {
        let (viewing_secret, _) = derive_viewing_keypair_v1(&[0x42; 32]).unwrap();
        let (_, other_public) = derive_viewing_keypair_v1(&[0x24; 32]).unwrap();
        let mut state = state();
        let finalized = block(state.head(), 101, 0xa1);
        state.advance_finalized_block_v1(finalized).unwrap();

        let empty_record = opaque_record(7, digest_bytes(701), &[]);
        assert!(matches!(
            state
                .ingest_finalized_deposit_v1(
                    FinalizedDepositRecordV1::new(
                        event_id(finalized.point(), 0x61, 0),
                        &empty_record,
                    ),
                    &viewing_secret,
                    &OwnerKeyStore::default(),
                )
                .unwrap(),
            DepositScanOutcomeV1::InvalidEncryptedPayload(PoolV1WalletError::WrongEnvelopeLength)
        ));
        assert_eq!(state.next_leaf_index(), 8);

        let other_record = encrypted_record(
            &other_public,
            owner_key(&digest_bytes(101)),
            8,
            digest_bytes(702),
            0x90,
        );
        assert!(matches!(
            state
                .ingest_finalized_deposit_v1(
                    FinalizedDepositRecordV1::new(
                        event_id(finalized.point(), 0x62, 1),
                        &other_record,
                    ),
                    &viewing_secret,
                    &OwnerKeyStore::default(),
                )
                .unwrap(),
            DepositScanOutcomeV1::NotForViewingKey
        ));
        assert_eq!(state.next_leaf_index(), 9);
        assert_eq!(state.root(), &digest_bytes(702));
    }

    #[test]
    fn identity_and_leaf_inconsistency_fail_without_mutating_cursor() {
        let (viewing_secret, _) = derive_viewing_keypair_v1(&[0x42; 32]).unwrap();
        let keys = OwnerKeyStore::default();
        let mut state = state();
        let finalized = block(state.head(), 101, 0xa1);
        state.advance_finalized_block_v1(finalized).unwrap();
        let baseline = state.clone();

        let wrong_leaf = opaque_record(8, digest_bytes(701), &[]);
        assert!(matches!(
            state.ingest_finalized_deposit_v1(
                FinalizedDepositRecordV1::new(event_id(finalized.point(), 0x61, 0), &wrong_leaf,),
                &viewing_secret,
                &keys,
            ),
            Err(ScanStateErrorV1::UnexpectedLeafIndex)
        ));
        assert_eq!(state, baseline);

        for expected_error in [
            ScanStateErrorV1::PoolMismatch,
            ScanStateErrorV1::AssetMintMismatch,
            ScanStateErrorV1::VaultMismatch,
        ] {
            let mut decoded =
                decode_deposit_event_record_v1(&opaque_record(7, digest_bytes(701), &[]))
                    .unwrap()
                    .receipt;
            match expected_error {
                ScanStateErrorV1::PoolMismatch => decoded.pool = [0x71; 32],
                ScanStateErrorV1::AssetMintMismatch => decoded.asset_mint = [0x72; 32],
                ScanStateErrorV1::VaultMismatch => decoded.vault_token_account = [0x73; 32],
                _ => unreachable!(),
            }
            let record = encode_deposit_event_record_v1(&DepositEventV1 {
                receipt: decoded,
                encrypted_note_payload: &[],
            })
            .unwrap();
            let result = state.ingest_finalized_deposit_v1(
                FinalizedDepositRecordV1::new(
                    event_id(finalized.point(), 0x70 + decoded.pool[0], 0),
                    &record,
                ),
                &viewing_secret,
                &keys,
            );
            match result {
                Err(error) => assert_eq!(error, expected_error),
                Ok(outcome) => panic!("expected {expected_error:?}, got {outcome:?}"),
            }
            assert_eq!(state, baseline);
        }
    }

    #[test]
    fn explicit_rollback_restores_cursor_then_accepts_a_canonical_replacement() {
        let (viewing_secret, _) = derive_viewing_keypair_v1(&[0x42; 32]).unwrap();
        let keys = OwnerKeyStore::default();
        let mut state = state();
        let first_block = block(state.head(), 101, 0xa1);
        state.advance_finalized_block_v1(first_block).unwrap();
        let first_record = opaque_record(7, digest_bytes(701), &[]);
        let first_id = event_id(first_block.point(), 0x61, 0);
        state
            .ingest_finalized_deposit_v1(
                FinalizedDepositRecordV1::new(first_id, &first_record),
                &viewing_secret,
                &keys,
            )
            .unwrap();

        let second_block = block(state.head(), 103, 0xa2);
        state.advance_finalized_block_v1(second_block).unwrap();
        let second_record = opaque_record(8, digest_bytes(702), &[]);
        let second_id = event_id(second_block.point(), 0x62, 0);
        state
            .ingest_finalized_deposit_v1(
                FinalizedDepositRecordV1::new(second_id, &second_record),
                &viewing_secret,
                &keys,
            )
            .unwrap();

        let conflicting = block(first_block.point(), 103, 0xb2);
        assert_eq!(
            state.advance_finalized_block_v1(conflicting),
            Err(ScanStateErrorV1::ReorgDetected)
        );
        let rollback = state.rollback_to_v1(first_block.point()).unwrap();
        assert_eq!(rollback.removed_events, vec![second_id]);
        assert_eq!(rollback.next_leaf_index, 8);
        assert_eq!(rollback.root, digest_bytes(701));
        assert_eq!(rollback.head, first_block.point());

        assert_eq!(
            state.advance_finalized_block_v1(conflicting),
            Ok(FinalizedBlockAdvanceV1::Advanced)
        );
        let replacement_record = opaque_record(8, digest_bytes(703), &[]);
        let replacement_id = event_id(conflicting.point(), 0x63, 0);
        state
            .ingest_finalized_deposit_v1(
                FinalizedDepositRecordV1::new(replacement_id, &replacement_record),
                &viewing_secret,
                &keys,
            )
            .unwrap();
        assert_eq!(state.next_leaf_index(), 9);
        assert_eq!(state.root(), &digest_bytes(703));

        let mut pruned = state.clone();
        let prune = pruned
            .prune_finalized_history_through_v1(first_block.point())
            .unwrap();
        assert_eq!(prune.pruned_block_count, 1);
        assert_eq!(prune.pruned_events, vec![first_id]);
        assert_eq!(prune.anchor, first_block.point());
        assert_eq!(prune.next_leaf_index, 8);
        assert_eq!(prune.root, digest_bytes(701));
        assert_eq!(pruned.retained_block_count(), 1);
        assert_eq!(pruned.retained_event_count(), 1);
        assert_eq!(
            decode_scan_state_v1(&encode_scan_state_v1(&pruned).unwrap()).unwrap(),
            pruned
        );
        let pruned_rollback = pruned.rollback_to_v1(pruned.anchor()).unwrap();
        assert_eq!(pruned_rollback.removed_events, vec![replacement_id]);
        assert_eq!(pruned_rollback.next_leaf_index, 8);

        assert!(matches!(
            state.ingest_finalized_deposit_v1(
                FinalizedDepositRecordV1::new(second_id, &second_record),
                &viewing_secret,
                &keys,
            ),
            Err(ScanStateErrorV1::EventOutsideCurrentBlock)
        ));
        let bad_parent = FinalizedBlockV1::new(point(105, 0xa5), state.anchor()).unwrap();
        assert_eq!(
            state.advance_finalized_block_v1(bad_parent),
            Err(ScanStateErrorV1::ChainDiscontinuity)
        );

        let rollback = state.rollback_to_v1(state.anchor()).unwrap();
        assert_eq!(rollback.removed_events, vec![first_id, replacement_id]);
        assert_eq!(rollback.next_leaf_index, 7);
        assert_eq!(rollback.root, digest_bytes(700));
        assert_eq!(
            decode_scan_state_v1(&encode_scan_state_v1(&state).unwrap()).unwrap(),
            state
        );
    }

    #[test]
    fn state_image_is_strictly_versioned_checksummed_and_invariant_checked() {
        let state = state();
        let encoded = encode_scan_state_v1(&state).unwrap();
        assert_eq!(encoded.len(), POOL_V1_SCAN_STATE_HEADER_BYTES);
        assert_eq!(decode_scan_state_v1(&encoded), Ok(state));

        assert_eq!(
            decode_scan_state_v1(&encoded[..encoded.len() - 1]),
            Err(ScanStateErrorV1::WrongStateLength)
        );
        let mut changed = encoded.clone();
        changed[0] ^= 1;
        assert_eq!(
            decode_scan_state_v1(&changed),
            Err(ScanStateErrorV1::WrongStateMagic)
        );
        let mut changed = encoded.clone();
        changed[4] = 2;
        assert_eq!(
            decode_scan_state_v1(&changed),
            Err(ScanStateErrorV1::WrongStateVersion)
        );
        let mut changed = encoded.clone();
        changed[6] = 1;
        assert_eq!(
            decode_scan_state_v1(&changed),
            Err(ScanStateErrorV1::NonZeroReserved)
        );

        let mut inconsistent = encoded;
        inconsistent[STATE_NEXT_LEAF_OFFSET..STATE_ROOT_OFFSET]
            .copy_from_slice(&8u64.to_le_bytes());
        let checksum = scan_state_checksum_v1(&inconsistent).unwrap();
        inconsistent[STATE_CHECKSUM_OFFSET..POOL_V1_SCAN_STATE_HEADER_BYTES]
            .copy_from_slice(&checksum);
        assert_eq!(
            decode_scan_state_v1(&inconsistent),
            Err(ScanStateErrorV1::StateInvariant)
        );
    }
}
