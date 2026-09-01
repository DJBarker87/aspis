//! Crash-safe authenticated witness journal.
//!
//! The anchor stores one complete, externally authenticated wallet witness
//! state. Each retained finalized block stores only its ordered public append
//! evidence plus the locally selected event IDs. Restart deterministically
//! replays that journal and refuses to open unless the result equals the
//! durable scan cursor's exact head, sequence and root. Rollback truncates the
//! journal before applying the replacement block, so no inverse Merkle update
//! or indexer-supplied witness is trusted.

use std::{collections::HashSet, path::Path};

use aspis_statement::encode_digest_canonical;
use sha2::{Digest as _, Sha256};

use crate::{
    durable_state::{check_legacy_writer_authority_v2, AtomicStateFileV1, DurableStateErrorV1},
    finalized_indexer::{FinalizedAppendEvidenceV1, FinalizedBlockIngestResultV1},
    scan_state::{
        DepositEventIdV1, DepositScanIdentityV1, FinalizedBlockAdvanceV1, FinalizedChainPointV1,
        PruneSummaryV1, ScanStateV1,
    },
    witness_state::{
        decode_wallet_witness_state_v1, encode_wallet_witness_state_v1, WalletWitnessStateV1,
        WitnessStateErrorV1,
    },
};

const WITNESS_JOURNAL_MAGIC_V1: [u8; 4] = *b"ASWJ";
const WITNESS_JOURNAL_VERSION_V1: u8 = 1;
const WITNESS_JOURNAL_HEADER_BYTES_V1: usize = 120;
const WITNESS_BLOCK_HEADER_BYTES_V1: usize = 96;
const WITNESS_APPEND_RECORD_BYTES_V1: usize = 192;
const WITNESS_JOURNAL_CHECKSUM_OFFSET_V1: usize = 88;
const MAX_WITNESS_JOURNAL_BYTES_V1: usize = 64 * 1024 * 1024;
const MAX_RETAINED_WITNESS_BLOCKS_V1: usize = 1_000_000;
const MAX_RETAINED_WITNESS_APPENDS_V1: usize = 1_048_576;
const WITNESS_JOURNAL_CHECKSUM_DOMAIN_V1: &[u8] =
    b"aspis:pool-v1:durable-wallet-witness-journal:sha256:v1";
const WITNESS_IDENTITY_DOMAIN_V1: &[u8] =
    b"aspis:pool-v1:durable-wallet-witness-identity:sha256:v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DurableWitnessErrorV1 {
    Durable(DurableStateErrorV1),
    Witness(WitnessStateErrorV1),
    InvalidInitialState,
    IdentityMismatch,
    ScanStateMismatch,
    WrongLength,
    WrongMagic,
    WrongVersion,
    NonZeroReserved,
    ChecksumMismatch,
    CountOverflow,
    InvalidBlockJournal,
    InvalidRollback,
    InvalidTrackSelection,
}

impl From<DurableStateErrorV1> for DurableWitnessErrorV1 {
    fn from(error: DurableStateErrorV1) -> Self {
        Self::Durable(error)
    }
}

impl From<WitnessStateErrorV1> for DurableWitnessErrorV1 {
    fn from(error: WitnessStateErrorV1) -> Self {
        Self::Witness(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RetainedWitnessBlockV1 {
    point: FinalizedChainPointV1,
    parent: FinalizedChainPointV1,
    appends: Vec<FinalizedAppendEvidenceV1>,
    tracked: Vec<DepositEventIdV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct WitnessMigrationBlockV1 {
    pub point: FinalizedChainPointV1,
    pub parent: FinalizedChainPointV1,
    pub appends: Vec<FinalizedAppendEvidenceV1>,
    pub tracked: Vec<DepositEventIdV1>,
}

pub struct DurableWalletWitnessStateV1 {
    file: AtomicStateFileV1,
    identity_digest: [u8; 32],
    anchor_point: FinalizedChainPointV1,
    anchor_state: WalletWitnessStateV1,
    blocks: Vec<RetainedWitnessBlockV1>,
    current_state: WalletWitnessStateV1,
}

impl DurableWalletWitnessStateV1 {
    /// Open an existing journal and bind it to the exact durable scan state,
    /// or create a new anchor when the supplied scan state retains no blocks.
    pub fn open_or_create_v1(
        path: impl AsRef<Path>,
        scan_state: &ScanStateV1,
        initial_witness_state: WalletWitnessStateV1,
    ) -> Result<Self, DurableWitnessErrorV1> {
        check_legacy_writer_authority_v2(path.as_ref())?;
        let identity_digest = witness_identity_digest_v1(scan_state.identity());
        let file = AtomicStateFileV1::acquire(path.as_ref())?;
        check_legacy_writer_authority_v2(path.as_ref())?;
        if let Some(bytes) = file.read_optional()? {
            let (stored_identity, anchor_point, anchor_state, blocks) =
                decode_witness_journal_v1(&bytes)?;
            if stored_identity != identity_digest {
                return Err(DurableWitnessErrorV1::IdentityMismatch);
            }
            let current_state = replay_blocks_v1(&anchor_state, &blocks)?;
            validate_against_scan_v1(
                identity_digest,
                scan_state,
                anchor_point,
                &blocks,
                &current_state,
            )?;
            return Ok(Self {
                file,
                identity_digest,
                anchor_point,
                anchor_state,
                blocks,
                current_state,
            });
        }
        if scan_state.retained_block_count() != 0
            || initial_witness_state.tree().next_leaf_index != scan_state.next_leaf_index()
            || encode_digest_canonical(&initial_witness_state.tree().root) != *scan_state.root()
        {
            return Err(DurableWitnessErrorV1::InvalidInitialState);
        }
        let anchor_point = scan_state.anchor();
        let bytes =
            encode_witness_journal_v1(identity_digest, anchor_point, &initial_witness_state, &[])?;
        file.replace(&bytes)?;
        Ok(Self {
            file,
            identity_digest,
            anchor_point,
            anchor_state: initial_witness_state.clone(),
            blocks: Vec::new(),
            current_state: initial_witness_state,
        })
    }

    pub fn current_state(&self) -> &WalletWitnessStateV1 {
        &self.current_state
    }

    pub fn anchor_point(&self) -> FinalizedChainPointV1 {
        self.anchor_point
    }

    pub fn retained_block_count(&self) -> usize {
        self.blocks.len()
    }

    pub(crate) fn migration_blocks_v1(&self) -> Vec<WitnessMigrationBlockV1> {
        self.blocks
            .iter()
            .map(|block| WitnessMigrationBlockV1 {
                point: block.point,
                parent: block.parent,
                appends: block.appends.clone(),
                tracked: block.tracked.clone(),
            })
            .collect()
    }

    pub(crate) fn migration_source_image_v1(&self) -> Result<Vec<u8>, DurableWitnessErrorV1> {
        self.file
            .read_optional()?
            .ok_or(DurableWitnessErrorV1::InvalidBlockJournal)
    }

    pub(crate) fn migration_source_path_v1(&self) -> &Path {
        self.file.path_v1()
    }

    /// Commit the same finalized transition as the scan cursor. All replay,
    /// rollback and root checks occur on clones before the atomic rename.
    pub fn commit_finalized_ingest_v1(
        &mut self,
        previous_scan_state: &ScanStateV1,
        candidate_scan_state: &ScanStateV1,
        result: &FinalizedBlockIngestResultV1,
        track_event_ids: &[DepositEventIdV1],
    ) -> Result<(), DurableWitnessErrorV1> {
        validate_against_scan_v1(
            self.identity_digest,
            previous_scan_state,
            self.anchor_point,
            &self.blocks,
            &self.current_state,
        )?;
        if witness_identity_digest_v1(candidate_scan_state.identity()) != self.identity_digest {
            return Err(DurableWitnessErrorV1::IdentityMismatch);
        }

        let mut blocks = self.blocks.clone();
        let mut current = self.current_state.clone();
        if let Some(rollback) = &result.rollback {
            let keep = if rollback.head == self.anchor_point {
                0
            } else {
                blocks
                    .iter()
                    .position(|block| block.point == rollback.head)
                    .map(|index| index + 1)
                    .ok_or(DurableWitnessErrorV1::InvalidRollback)?
            };
            let removed_ids: Vec<_> = blocks[keep..]
                .iter()
                .flat_map(|block| block.appends.iter().map(|append| append.event_id))
                .collect();
            if removed_ids != rollback.removed_events {
                return Err(DurableWitnessErrorV1::InvalidRollback);
            }
            blocks.truncate(keep);
            current = replay_blocks_v1(&self.anchor_state, &blocks)?;
        }

        match result.advance {
            FinalizedBlockAdvanceV1::AlreadyCurrent => {
                if result.rollback.is_some()
                    || candidate_scan_state != previous_scan_state
                    || !track_event_ids.is_empty()
                {
                    return Err(DurableWitnessErrorV1::InvalidBlockJournal);
                }
                let last = blocks
                    .last()
                    .ok_or(DurableWitnessErrorV1::InvalidBlockJournal)?;
                if last.point != candidate_scan_state.head()
                    || last.appends != result.append_evidence
                {
                    return Err(DurableWitnessErrorV1::InvalidBlockJournal);
                }
                return Ok(());
            }
            FinalizedBlockAdvanceV1::Advanced => {}
        }

        let parent = blocks.last().map_or(self.anchor_point, |block| block.point);
        if candidate_scan_state.head() == parent {
            return Err(DurableWitnessErrorV1::InvalidBlockJournal);
        }
        if result
            .append_evidence
            .iter()
            .any(|append| append.event_id.point() != candidate_scan_state.head())
        {
            return Err(DurableWitnessErrorV1::InvalidBlockJournal);
        }
        let selected: HashSet<_> = track_event_ids.iter().copied().collect();
        if selected.len() != track_event_ids.len()
            || track_event_ids.iter().any(|event_id| {
                !result
                    .append_evidence
                    .iter()
                    .any(|append| append.event_id == *event_id)
            })
        {
            return Err(DurableWitnessErrorV1::InvalidTrackSelection);
        }
        current.apply_finalized_appends_v1(&result.append_evidence, track_event_ids)?;
        if current.tree().next_leaf_index != candidate_scan_state.next_leaf_index()
            || encode_digest_canonical(&current.tree().root) != *candidate_scan_state.root()
        {
            return Err(DurableWitnessErrorV1::ScanStateMismatch);
        }
        blocks.push(RetainedWitnessBlockV1 {
            point: candidate_scan_state.head(),
            parent,
            appends: result.append_evidence.clone(),
            tracked: track_event_ids.to_vec(),
        });
        if blocks.len() > MAX_RETAINED_WITNESS_BLOCKS_V1 {
            return Err(DurableWitnessErrorV1::CountOverflow);
        }
        validate_against_scan_v1(
            self.identity_digest,
            candidate_scan_state,
            self.anchor_point,
            &blocks,
            &current,
        )?;
        let bytes = encode_witness_journal_v1(
            self.identity_digest,
            self.anchor_point,
            &self.anchor_state,
            &blocks,
        )?;
        self.file.replace(&bytes)?;
        self.blocks = blocks;
        self.current_state = current;
        Ok(())
    }

    /// Mirror a successful scan-cursor prune. The witness state after the
    /// chosen ancestor becomes the new complete anchor and the retained suffix
    /// remains replayable byte-for-byte.
    pub fn prune_finalized_history_through_v1(
        &mut self,
        candidate_scan_state: &ScanStateV1,
        summary: &PruneSummaryV1,
    ) -> Result<(), DurableWitnessErrorV1> {
        if summary.anchor != candidate_scan_state.anchor()
            || witness_identity_digest_v1(candidate_scan_state.identity()) != self.identity_digest
        {
            return Err(DurableWitnessErrorV1::ScanStateMismatch);
        }
        let cut = self
            .blocks
            .iter()
            .position(|block| block.point == summary.anchor)
            .map(|index| index + 1)
            .ok_or(DurableWitnessErrorV1::InvalidRollback)?;
        let expected_pruned: Vec<_> = self.blocks[..cut]
            .iter()
            .flat_map(|block| block.appends.iter().map(|append| append.event_id))
            .collect();
        if expected_pruned != summary.pruned_events {
            return Err(DurableWitnessErrorV1::InvalidRollback);
        }
        let anchor_state = replay_blocks_v1(&self.anchor_state, &self.blocks[..cut])?;
        let blocks = self.blocks[cut..].to_vec();
        let current_state = replay_blocks_v1(&anchor_state, &blocks)?;
        validate_against_scan_v1(
            self.identity_digest,
            candidate_scan_state,
            summary.anchor,
            &blocks,
            &current_state,
        )?;
        let bytes = encode_witness_journal_v1(
            self.identity_digest,
            summary.anchor,
            &anchor_state,
            &blocks,
        )?;
        self.file.replace(&bytes)?;
        self.anchor_point = summary.anchor;
        self.anchor_state = anchor_state;
        self.blocks = blocks;
        self.current_state = current_state;
        Ok(())
    }
}

fn validate_against_scan_v1(
    identity_digest: [u8; 32],
    scan_state: &ScanStateV1,
    anchor_point: FinalizedChainPointV1,
    blocks: &[RetainedWitnessBlockV1],
    current_state: &WalletWitnessStateV1,
) -> Result<(), DurableWitnessErrorV1> {
    if witness_identity_digest_v1(scan_state.identity()) != identity_digest
        || scan_state.anchor() != anchor_point
        || scan_state.retained_block_count() != blocks.len()
        || blocks.last().map_or(anchor_point, |block| block.point) != scan_state.head()
        || current_state.tree().next_leaf_index != scan_state.next_leaf_index()
        || encode_digest_canonical(&current_state.tree().root) != *scan_state.root()
    {
        return Err(DurableWitnessErrorV1::ScanStateMismatch);
    }
    let mut expected_parent = anchor_point;
    for block in blocks {
        if block.parent != expected_parent || block.point.slot() <= block.parent.slot() {
            return Err(DurableWitnessErrorV1::InvalidBlockJournal);
        }
        expected_parent = block.point;
    }
    Ok(())
}

fn replay_blocks_v1(
    anchor: &WalletWitnessStateV1,
    blocks: &[RetainedWitnessBlockV1],
) -> Result<WalletWitnessStateV1, DurableWitnessErrorV1> {
    let mut state = anchor.clone();
    let mut expected_parent = None;
    for block in blocks {
        if expected_parent.is_some_and(|parent| block.parent != parent) {
            return Err(DurableWitnessErrorV1::InvalidBlockJournal);
        }
        state.apply_finalized_appends_v1(&block.appends, &block.tracked)?;
        expected_parent = Some(block.point);
    }
    Ok(state)
}

fn witness_identity_digest_v1(identity: &DepositScanIdentityV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(WITNESS_IDENTITY_DOMAIN_V1);
    hasher.update(identity.pool());
    hasher.update(identity.deployment_domain());
    hasher.update(identity.asset_mint());
    hasher.update(identity.vault_token_account());
    hasher.update(identity.asset_id().to_le_bytes());
    hasher.finalize().into()
}

fn encode_witness_journal_v1(
    identity_digest: [u8; 32],
    anchor_point: FinalizedChainPointV1,
    anchor_state: &WalletWitnessStateV1,
    blocks: &[RetainedWitnessBlockV1],
) -> Result<Vec<u8>, DurableWitnessErrorV1> {
    if blocks.len() > MAX_RETAINED_WITNESS_BLOCKS_V1 {
        return Err(DurableWitnessErrorV1::CountOverflow);
    }
    let anchor = encode_wallet_witness_state_v1(anchor_state)?;
    let append_count = blocks.iter().try_fold(0usize, |total, block| {
        total
            .checked_add(block.appends.len())
            .ok_or(DurableWitnessErrorV1::CountOverflow)
    })?;
    if append_count > MAX_RETAINED_WITNESS_APPENDS_V1 {
        return Err(DurableWitnessErrorV1::CountOverflow);
    }
    let blocks_bytes = blocks.iter().try_fold(0usize, |total, block| {
        let tracked: HashSet<_> = block.tracked.iter().copied().collect();
        if tracked.len() != block.tracked.len()
            || block
                .tracked
                .iter()
                .any(|id| !block.appends.iter().any(|append| append.event_id == *id))
        {
            return Err(DurableWitnessErrorV1::InvalidTrackSelection);
        }
        total
            .checked_add(WITNESS_BLOCK_HEADER_BYTES_V1)
            .and_then(|value| {
                block
                    .appends
                    .len()
                    .checked_mul(WITNESS_APPEND_RECORD_BYTES_V1)
                    .and_then(|records| value.checked_add(records))
            })
            .ok_or(DurableWitnessErrorV1::CountOverflow)
    })?;
    let length = WITNESS_JOURNAL_HEADER_BYTES_V1
        .checked_add(anchor.len())
        .and_then(|value| value.checked_add(blocks_bytes))
        .ok_or(DurableWitnessErrorV1::CountOverflow)?;
    if length > MAX_WITNESS_JOURNAL_BYTES_V1 {
        return Err(DurableWitnessErrorV1::CountOverflow);
    }
    let mut bytes = vec![0u8; length];
    bytes[..4].copy_from_slice(&WITNESS_JOURNAL_MAGIC_V1);
    bytes[4] = WITNESS_JOURNAL_VERSION_V1;
    bytes[8..40].copy_from_slice(&identity_digest);
    encode_chain_point_v1(anchor_point, &mut bytes[40..80]);
    bytes[80..84].copy_from_slice(
        &u32::try_from(anchor.len())
            .map_err(|_| DurableWitnessErrorV1::CountOverflow)?
            .to_le_bytes(),
    );
    bytes[84..88].copy_from_slice(
        &u32::try_from(blocks.len())
            .map_err(|_| DurableWitnessErrorV1::CountOverflow)?
            .to_le_bytes(),
    );
    let mut offset = WITNESS_JOURNAL_HEADER_BYTES_V1;
    bytes[offset..offset + anchor.len()].copy_from_slice(&anchor);
    offset += anchor.len();
    for block in blocks {
        let header = &mut bytes[offset..offset + WITNESS_BLOCK_HEADER_BYTES_V1];
        header[..4].copy_from_slice(b"ASWB");
        header[4] = WITNESS_JOURNAL_VERSION_V1;
        encode_chain_point_v1(block.point, &mut header[8..48]);
        encode_chain_point_v1(block.parent, &mut header[48..88]);
        header[88..92].copy_from_slice(
            &u32::try_from(block.appends.len())
                .map_err(|_| DurableWitnessErrorV1::CountOverflow)?
                .to_le_bytes(),
        );
        offset += WITNESS_BLOCK_HEADER_BYTES_V1;
        let tracked: HashSet<_> = block.tracked.iter().copied().collect();
        for append in &block.appends {
            let record = &mut bytes[offset..offset + WITNESS_APPEND_RECORD_BYTES_V1];
            record[..108].copy_from_slice(&encode_event_id_v1(append.event_id));
            record[108..116].copy_from_slice(&append.leaf_index.to_le_bytes());
            record[116..124].copy_from_slice(&append.root_sequence.to_le_bytes());
            record[124..156].copy_from_slice(&append.note_commitment);
            record[156..188].copy_from_slice(&append.root);
            record[188] = u8::from(tracked.contains(&append.event_id));
            offset += WITNESS_APPEND_RECORD_BYTES_V1;
        }
    }
    let checksum = witness_journal_checksum_v1(&bytes)?;
    bytes[WITNESS_JOURNAL_CHECKSUM_OFFSET_V1..WITNESS_JOURNAL_CHECKSUM_OFFSET_V1 + 32]
        .copy_from_slice(&checksum);
    Ok(bytes)
}

fn decode_witness_journal_v1(
    bytes: &[u8],
) -> Result<
    (
        [u8; 32],
        FinalizedChainPointV1,
        WalletWitnessStateV1,
        Vec<RetainedWitnessBlockV1>,
    ),
    DurableWitnessErrorV1,
> {
    if bytes.len() < WITNESS_JOURNAL_HEADER_BYTES_V1 || bytes.len() > MAX_WITNESS_JOURNAL_BYTES_V1 {
        return Err(DurableWitnessErrorV1::WrongLength);
    }
    if bytes[..4] != WITNESS_JOURNAL_MAGIC_V1 {
        return Err(DurableWitnessErrorV1::WrongMagic);
    }
    if bytes[4] != WITNESS_JOURNAL_VERSION_V1 {
        return Err(DurableWitnessErrorV1::WrongVersion);
    }
    if bytes[5..8].iter().any(|byte| *byte != 0) {
        return Err(DurableWitnessErrorV1::NonZeroReserved);
    }
    let encoded_checksum: [u8; 32] = bytes[88..120].try_into().unwrap();
    if encoded_checksum != witness_journal_checksum_v1(bytes)? {
        return Err(DurableWitnessErrorV1::ChecksumMismatch);
    }
    let identity_digest = bytes[8..40].try_into().unwrap();
    let anchor_point = decode_chain_point_v1(&bytes[40..80])?;
    let anchor_length = u32::from_le_bytes(bytes[80..84].try_into().unwrap()) as usize;
    let block_count = u32::from_le_bytes(bytes[84..88].try_into().unwrap()) as usize;
    if block_count > MAX_RETAINED_WITNESS_BLOCKS_V1 {
        return Err(DurableWitnessErrorV1::CountOverflow);
    }
    let anchor_end = WITNESS_JOURNAL_HEADER_BYTES_V1
        .checked_add(anchor_length)
        .ok_or(DurableWitnessErrorV1::CountOverflow)?;
    let anchor_state = decode_wallet_witness_state_v1(
        bytes
            .get(WITNESS_JOURNAL_HEADER_BYTES_V1..anchor_end)
            .ok_or(DurableWitnessErrorV1::WrongLength)?,
    )?;
    let mut blocks = Vec::with_capacity(block_count);
    let mut offset = anchor_end;
    let mut total_appends = 0usize;
    let mut expected_parent = anchor_point;
    for _ in 0..block_count {
        let header_end = offset
            .checked_add(WITNESS_BLOCK_HEADER_BYTES_V1)
            .ok_or(DurableWitnessErrorV1::CountOverflow)?;
        let header = bytes
            .get(offset..header_end)
            .ok_or(DurableWitnessErrorV1::WrongLength)?;
        if header[..4] != *b"ASWB" || header[4] != WITNESS_JOURNAL_VERSION_V1 {
            return Err(DurableWitnessErrorV1::WrongMagic);
        }
        if header[5..8].iter().any(|byte| *byte != 0)
            || header[92..96].iter().any(|byte| *byte != 0)
        {
            return Err(DurableWitnessErrorV1::NonZeroReserved);
        }
        let point = decode_chain_point_v1(&header[8..48])?;
        let parent = decode_chain_point_v1(&header[48..88])?;
        let count = u32::from_le_bytes(header[88..92].try_into().unwrap()) as usize;
        if parent != expected_parent || point.slot() <= parent.slot() {
            return Err(DurableWitnessErrorV1::InvalidBlockJournal);
        }
        expected_parent = point;
        total_appends = total_appends
            .checked_add(count)
            .ok_or(DurableWitnessErrorV1::CountOverflow)?;
        if total_appends > MAX_RETAINED_WITNESS_APPENDS_V1 {
            return Err(DurableWitnessErrorV1::CountOverflow);
        }
        offset = header_end;
        let mut appends = Vec::with_capacity(count);
        let mut tracked = Vec::new();
        for _ in 0..count {
            let record_end = offset
                .checked_add(WITNESS_APPEND_RECORD_BYTES_V1)
                .ok_or(DurableWitnessErrorV1::CountOverflow)?;
            let record = bytes
                .get(offset..record_end)
                .ok_or(DurableWitnessErrorV1::WrongLength)?;
            if record[189..].iter().any(|byte| *byte != 0) || record[188] > 1 {
                return Err(DurableWitnessErrorV1::NonZeroReserved);
            }
            let event_id = decode_event_id_v1(&record[..108])?;
            if event_id.point() != point {
                return Err(DurableWitnessErrorV1::InvalidBlockJournal);
            }
            appends.push(FinalizedAppendEvidenceV1 {
                event_id,
                leaf_index: u64::from_le_bytes(record[108..116].try_into().unwrap()),
                root_sequence: u64::from_le_bytes(record[116..124].try_into().unwrap()),
                note_commitment: record[124..156].try_into().unwrap(),
                root: record[156..188].try_into().unwrap(),
            });
            if record[188] == 1 {
                tracked.push(event_id);
            }
            offset = record_end;
        }
        blocks.push(RetainedWitnessBlockV1 {
            point,
            parent,
            appends,
            tracked,
        });
    }
    if offset != bytes.len() {
        return Err(DurableWitnessErrorV1::WrongLength);
    }
    Ok((identity_digest, anchor_point, anchor_state, blocks))
}

fn witness_journal_checksum_v1(bytes: &[u8]) -> Result<[u8; 32], DurableWitnessErrorV1> {
    if bytes.len() < WITNESS_JOURNAL_HEADER_BYTES_V1 {
        return Err(DurableWitnessErrorV1::WrongLength);
    }
    let length = u64::try_from(bytes.len()).map_err(|_| DurableWitnessErrorV1::CountOverflow)?;
    let mut hasher = Sha256::new();
    hasher.update(WITNESS_JOURNAL_CHECKSUM_DOMAIN_V1);
    hasher.update(length.to_le_bytes());
    hasher.update(&bytes[..WITNESS_JOURNAL_CHECKSUM_OFFSET_V1]);
    hasher.update([0u8; 32]);
    hasher.update(&bytes[WITNESS_JOURNAL_CHECKSUM_OFFSET_V1 + 32..]);
    Ok(hasher.finalize().into())
}

fn encode_chain_point_v1(point: FinalizedChainPointV1, bytes: &mut [u8]) {
    bytes[..8].copy_from_slice(&point.slot().to_le_bytes());
    bytes[8..40].copy_from_slice(point.block_hash());
}

fn decode_chain_point_v1(bytes: &[u8]) -> Result<FinalizedChainPointV1, DurableWitnessErrorV1> {
    FinalizedChainPointV1::new(
        u64::from_le_bytes(bytes[..8].try_into().unwrap()),
        bytes[8..40].try_into().unwrap(),
    )
    .map_err(|_| DurableWitnessErrorV1::InvalidBlockJournal)
}

fn encode_event_id_v1(event_id: DepositEventIdV1) -> [u8; 108] {
    let mut bytes = [0u8; 108];
    encode_chain_point_v1(event_id.point(), &mut bytes[..40]);
    bytes[40..104].copy_from_slice(event_id.transaction_signature());
    bytes[104..106].copy_from_slice(&event_id.instruction_index().to_le_bytes());
    bytes[106..108].copy_from_slice(&event_id.event_index().to_le_bytes());
    bytes
}

fn decode_event_id_v1(bytes: &[u8]) -> Result<DepositEventIdV1, DurableWitnessErrorV1> {
    DepositEventIdV1::new(
        decode_chain_point_v1(&bytes[..40])?,
        bytes[40..104].try_into().unwrap(),
        u16::from_le_bytes(bytes[104..106].try_into().unwrap()),
        u16::from_le_bytes(bytes[106..108].try_into().unwrap()),
    )
    .map_err(|_| DurableWitnessErrorV1::InvalidBlockJournal)
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };

    use aspis_core::field::M31;
    use aspis_statement::{encode_digest_canonical, pool_v1::IncrementalMerkleTreeV1, Digest};

    use super::*;
    use crate::{
        finalized_indexer::FinalizedBlockIngestResultV1,
        scan_state::{FinalizedBlockV1, FinalizedPublicOutputRecordV1},
    };

    static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    struct TestDirectory(std::path::PathBuf);

    impl TestDirectory {
        fn new() -> Self {
            let serial = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "aspis-durable-witness-{}-{}",
                std::process::id(),
                serial
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }

        fn state_path(&self) -> std::path::PathBuf {
            self.0.join("witness.state")
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32))
    }

    fn identity() -> DepositScanIdentityV1 {
        DepositScanIdentityV1::new([0x11; 32], [0x22; 32], [0x33; 32], [0x44; 32], 9).unwrap()
    }

    fn point(slot: u64, seed: u8) -> FinalizedChainPointV1 {
        FinalizedChainPointV1::new(slot, [seed; 32]).unwrap()
    }

    fn event(point: FinalizedChainPointV1, seed: u8) -> DepositEventIdV1 {
        DepositEventIdV1::new(point, [seed; 64], 0, 0).unwrap()
    }

    fn result(
        rollback: Option<crate::scan_state::RollbackSummaryV1>,
        append: FinalizedAppendEvidenceV1,
    ) -> FinalizedBlockIngestResultV1 {
        FinalizedBlockIngestResultV1 {
            advance: FinalizedBlockAdvanceV1::Advanced,
            rollback,
            deposit_event_ids: Vec::new(),
            deposit_outcomes: Vec::new(),
            transition_outcomes: Vec::new(),
            transition_evidence: Vec::new(),
            initializations: Vec::new(),
            append_evidence: vec![append],
            prepared_settlements: Vec::new(),
            cancelled_settlements: Vec::new(),
            plan_lifecycle: Vec::new(),
            root_evidence: Vec::new(),
            ignored_failed_pool_transactions: 0,
        }
    }

    fn advance_one(
        previous: &ScanStateV1,
        next_point: FinalizedChainPointV1,
        leaf: Digest,
        signature_seed: u8,
    ) -> (ScanStateV1, FinalizedAppendEvidenceV1) {
        let mut candidate = previous.clone();
        candidate
            .advance_finalized_block_v1(FinalizedBlockV1::new(next_point, previous.head()).unwrap())
            .unwrap();
        let tree = IncrementalMerkleTreeV1::from_parts(
            previous.next_leaf_index(),
            aspis_statement::decode_digest_canonical(previous.root()).unwrap(),
            WalletWitnessStateV1::empty().tree().frontier,
        );
        // This focused fixture only advances from the empty anchor or a
        // rollback to that anchor, so the canonical empty frontier is exact.
        let tree = tree.unwrap();
        let (next_tree, receipt) = tree.append_one(leaf).unwrap();
        let event_id = event(next_point, signature_seed);
        let commitment = encode_digest_canonical(&leaf);
        let root = encode_digest_canonical(&next_tree.root);
        candidate
            .ingest_finalized_public_output_v1(FinalizedPublicOutputRecordV1 {
                id: event_id,
                pool: *candidate.identity().pool(),
                leaf_index: receipt.leaf_index,
                root_sequence: receipt.root_sequence,
                note_commitment: commitment,
                root,
                authenticated_transport: &[1],
            })
            .unwrap();
        (
            candidate,
            FinalizedAppendEvidenceV1 {
                event_id,
                leaf_index: receipt.leaf_index,
                root_sequence: receipt.root_sequence,
                note_commitment: commitment,
                root,
            },
        )
    }

    #[test]
    fn witness_journal_restarts_reorgs_prunes_and_detects_corruption() {
        let directory = TestDirectory::new();
        let path = directory.state_path();
        let anchor = point(100, 0xa0);
        let initial_witness = WalletWitnessStateV1::empty();
        let initial_scan = ScanStateV1::new(
            identity(),
            anchor,
            0,
            encode_digest_canonical(&initial_witness.tree().root),
        )
        .unwrap();
        let mut journal = DurableWalletWitnessStateV1::open_or_create_v1(
            &path,
            &initial_scan,
            initial_witness.clone(),
        )
        .unwrap();

        let (first_scan, first_append) =
            advance_one(&initial_scan, point(101, 0xa1), digest(10), 0x51);
        journal
            .commit_finalized_ingest_v1(
                &initial_scan,
                &first_scan,
                &result(None, first_append),
                &[first_append.event_id],
            )
            .unwrap();
        assert_eq!(journal.current_state().tracked().len(), 1);
        drop(journal);

        let mut journal = DurableWalletWitnessStateV1::open_or_create_v1(
            &path,
            &first_scan,
            initial_witness.clone(),
        )
        .unwrap();
        assert_eq!(
            journal.current_state().tracked()[0].event_id(),
            first_append.event_id
        );

        let mut replacement_base = first_scan.clone();
        let rollback = replacement_base.rollback_to_v1(anchor).unwrap();
        let (replacement_scan, replacement_append) =
            advance_one(&replacement_base, point(102, 0xb2), digest(20), 0x52);
        journal
            .commit_finalized_ingest_v1(
                &first_scan,
                &replacement_scan,
                &result(Some(rollback), replacement_append),
                &[replacement_append.event_id],
            )
            .unwrap();
        assert!(journal
            .current_state()
            .witness_v1(first_append.event_id)
            .is_err());
        assert_eq!(
            journal
                .current_state()
                .witness_v1(replacement_append.event_id)
                .unwrap()
                .leaf_index(),
            0
        );

        let mut pruned_scan = replacement_scan.clone();
        let prune = pruned_scan
            .prune_finalized_history_through_v1(replacement_scan.head())
            .unwrap();
        journal
            .prune_finalized_history_through_v1(&pruned_scan, &prune)
            .unwrap();
        assert_eq!(journal.anchor_point(), replacement_scan.head());
        assert_eq!(journal.retained_block_count(), 0);
        drop(journal);

        let journal =
            DurableWalletWitnessStateV1::open_or_create_v1(&path, &pruned_scan, initial_witness)
                .unwrap();
        assert_eq!(journal.current_state().tracked().len(), 1);
        drop(journal);

        let mut bytes = fs::read(&path).unwrap();
        *bytes.last_mut().unwrap() ^= 1;
        fs::write(&path, bytes).unwrap();
        assert_eq!(
            DurableWalletWitnessStateV1::open_or_create_v1(
                &path,
                &pruned_scan,
                WalletWitnessStateV1::empty(),
            )
            .err(),
            Some(DurableWitnessErrorV1::ChecksumMismatch)
        );
    }
}
