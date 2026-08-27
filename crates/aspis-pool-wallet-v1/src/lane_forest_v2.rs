//! Production-inactive eight-lane wallet/indexer plumbing.
//!
//! This module is compiled only with `eight-lane-plumbing-v2`. It does not
//! change Pool accounts, proof bytes, verifier dispatch, or the legacy
//! single-tree wallet APIs. Its types make the proposed forest invariants
//! explicit before any production integration:
//!
//! - root-history pages are identified by `(lane_id, page_number)`;
//! - each lane has an independent tree cursor, frontier and root sequence;
//! - a private transfer appends one pair leaf, never one leaf per output;
//! - a checkpoint authenticates a complete, alias-free set of eight lanes;
//! - checkpoint failure and rollback operate atomically across all lanes.

use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{
        root_history_location, PoolV1PairLeafErrorV1, PoolV1PairLeafWitnessV1, POOL_V1_TREE_DEPTH,
    },
};

use crate::{
    scan_state::DepositEventIdV1,
    witness_state::{WalletWitnessStateV1, WitnessAppendReceiptV1, WitnessStateErrorV1},
};

pub const POOL_V1_LANE_FOREST_VERSION_V2: u8 = 2;
pub const POOL_V1_LANE_COUNT_V2: usize = 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LaneForestErrorV2 {
    InvalidLane,
    NonCanonicalDigest,
    WrongRoutedLane,
    IncompleteLaneSet,
    LaneAlias,
    PageNumberMismatch,
    PageAddressAlias,
    LegacyPageZeroCollision,
    LegacyPerOutputAppend,
    OutputEventMismatch,
    DuplicateAppend,
    CheckpointSequenceMismatch,
    CheckpointLaneSequenceMismatch,
    CheckpointLaneRootMismatch,
    CheckpointNoProgress,
    UnknownCheckpoint,
    InvalidPairLeaf(PoolV1PairLeafErrorV1),
    Witness(WitnessStateErrorV1),
}

impl From<WitnessStateErrorV1> for LaneForestErrorV2 {
    fn from(error: WitnessStateErrorV1) -> Self {
        Self::Witness(error)
    }
}

impl From<PoolV1PairLeafErrorV1> for LaneForestErrorV2 {
    fn from(error: PoolV1PairLeafErrorV1) -> Self {
        Self::InvalidPairLeaf(error)
    }
}

/// Validated forest lane. Raw `u8` values cannot silently alias modulo eight.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LaneIdV2(u8);

impl LaneIdV2 {
    pub fn new(value: u8) -> Result<Self, LaneForestErrorV2> {
        if value >= POOL_V1_LANE_COUNT_V2 as u8 {
            return Err(LaneForestErrorV2::InvalidLane);
        }
        Ok(Self(value))
    }

    pub const fn as_u8(self) -> u8 {
        self.0
    }

    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

fn routed_lane_from_canonical_digest_v2(encoded: [u8; 32]) -> Result<LaneIdV2, LaneForestErrorV2> {
    let digest =
        decode_digest_canonical(&encoded).map_err(|_| LaneForestErrorV2::NonCanonicalDigest)?;
    let canonical = encode_digest_canonical(&digest);
    LaneIdV2::new(canonical[0] & 7)
}

/// Deposit routing is the low three bits of the canonical commitment digest.
pub fn deposit_lane_from_commitment_v2(
    commitment: [u8; 32],
) -> Result<LaneIdV2, LaneForestErrorV2> {
    routed_lane_from_canonical_digest_v2(commitment)
}

/// Private-transfer output routing is the low three bits of the canonical
/// public nullifier digest. It is intentionally independent of the input lane.
pub fn private_transfer_output_lane_v2(nullifier: [u8; 32]) -> Result<LaneIdV2, LaneForestErrorV2> {
    routed_lane_from_canonical_digest_v2(nullifier)
}

/// Root-history identity for the lane forest. A page number without a lane is
/// not a valid V2 key.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LaneRootHistoryPageKeyV2 {
    pub lane_id: LaneIdV2,
    pub page_number: u64,
}

impl LaneRootHistoryPageKeyV2 {
    pub const fn new(lane_id: LaneIdV2, page_number: u64) -> Self {
        Self {
            lane_id,
            page_number,
        }
    }

    pub fn for_root_sequence(lane_id: LaneIdV2, root_sequence: u64) -> Self {
        Self::new(lane_id, root_history_location(root_sequence).page_number)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LaneRootHistoryPageBindingV2 {
    pub key: LaneRootHistoryPageKeyV2,
    pub address: [u8; 32],
}

/// One complete page-number slice across all lanes, sorted by lane ID.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompleteLaneRootPageSetV2 {
    page_number: u64,
    bindings: [LaneRootHistoryPageBindingV2; POOL_V1_LANE_COUNT_V2],
}

impl CompleteLaneRootPageSetV2 {
    pub fn new(
        page_number: u64,
        bindings: Vec<LaneRootHistoryPageBindingV2>,
    ) -> Result<Self, LaneForestErrorV2> {
        if bindings.len() != POOL_V1_LANE_COUNT_V2 {
            return Err(LaneForestErrorV2::IncompleteLaneSet);
        }
        let mut by_lane = [None; POOL_V1_LANE_COUNT_V2];
        for binding in bindings {
            if binding.key.page_number != page_number {
                return Err(LaneForestErrorV2::PageNumberMismatch);
            }
            let index = binding.key.lane_id.index();
            if by_lane[index].replace(binding).is_some() {
                return Err(LaneForestErrorV2::LaneAlias);
            }
        }
        let bindings: [LaneRootHistoryPageBindingV2; POOL_V1_LANE_COUNT_V2] = by_lane
            .map(|entry| entry.ok_or(LaneForestErrorV2::IncompleteLaneSet))
            .into_iter()
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .map_err(|_| LaneForestErrorV2::IncompleteLaneSet)?;
        for index in 0..POOL_V1_LANE_COUNT_V2 {
            if bindings[index].address == [0u8; 32] {
                return Err(LaneForestErrorV2::PageAddressAlias);
            }
            for earlier in &bindings[..index] {
                if earlier.address == bindings[index].address {
                    return Err(if page_number == 0 {
                        LaneForestErrorV2::LegacyPageZeroCollision
                    } else {
                        LaneForestErrorV2::PageAddressAlias
                    });
                }
            }
        }
        Ok(Self {
            page_number,
            bindings,
        })
    }

    pub const fn page_number(&self) -> u64 {
        self.page_number
    }

    pub fn bindings(&self) -> &[LaneRootHistoryPageBindingV2; POOL_V1_LANE_COUNT_V2] {
        &self.bindings
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PairSlotV2 {
    First,
    Second,
}

/// A wallet-visible output mapped to its one underlying pair-leaf witness.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LaneTrackedOutputV2 {
    pub output_event_id: DepositEventIdV1,
    pub witness_event_id: DepositEventIdV1,
    pub lane_id: LaneIdV2,
    pub pair_leaf_index: u64,
    pub slot: PairSlotV2,
    pub commitment: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LaneAppendKindV2 {
    Deposit {
        event_id: DepositEventIdV1,
        commitment: [u8; 32],
        track: bool,
    },
    PrivateTransfer {
        recipient_event_id: DepositEventIdV1,
        change_event_id: DepositEventIdV1,
        recipient_commitment: [u8; 32],
        change_commitment: [u8; 32],
        track_recipient: bool,
        track_change: bool,
    },
}

/// One authenticated finalized lane append. Private transfers always contain
/// both outputs and one pair-leaf digest in this single record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LaneAppendRecordV2 {
    pub lane_id: LaneIdV2,
    pub pair_leaf_index: u64,
    pub root_sequence: u64,
    pub pair_leaf: [u8; 32],
    pub root: [u8; 32],
    kind: LaneAppendKindV2,
}

impl LaneAppendRecordV2 {
    #[allow(clippy::too_many_arguments)]
    pub fn deposit(
        event_id: DepositEventIdV1,
        supplied_lane: LaneIdV2,
        commitment: [u8; 32],
        pair_leaf_index: u64,
        root_sequence: u64,
        root: [u8; 32],
        track: bool,
        observed_append_count: u8,
    ) -> Result<Self, LaneForestErrorV2> {
        if observed_append_count != 1 {
            return Err(LaneForestErrorV2::LegacyPerOutputAppend);
        }
        if deposit_lane_from_commitment_v2(commitment)? != supplied_lane {
            return Err(LaneForestErrorV2::WrongRoutedLane);
        }
        decode_digest_canonical(&root).map_err(|_| LaneForestErrorV2::NonCanonicalDigest)?;
        let commitment_digest = decode_digest_canonical(&commitment)
            .map_err(|_| LaneForestErrorV2::NonCanonicalDigest)?;
        let pair_leaf = encode_digest_canonical(
            &PoolV1PairLeafWitnessV1::single_output(commitment_digest)?.leaf_digest()?,
        );
        Ok(Self {
            lane_id: supplied_lane,
            pair_leaf_index,
            root_sequence,
            pair_leaf,
            root,
            kind: LaneAppendKindV2::Deposit {
                event_id,
                commitment,
                track,
            },
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub fn private_transfer(
        recipient_event_id: DepositEventIdV1,
        change_event_id: DepositEventIdV1,
        supplied_lane: LaneIdV2,
        nullifier: [u8; 32],
        recipient_commitment: [u8; 32],
        change_commitment: [u8; 32],
        pair_leaf_index: u64,
        root_sequence: u64,
        root: [u8; 32],
        track_recipient: bool,
        track_change: bool,
        observed_append_count: u8,
    ) -> Result<Self, LaneForestErrorV2> {
        if observed_append_count != 1 {
            return Err(LaneForestErrorV2::LegacyPerOutputAppend);
        }
        if private_transfer_output_lane_v2(nullifier)? != supplied_lane {
            return Err(LaneForestErrorV2::WrongRoutedLane);
        }
        if !same_private_transfer_event_v2(recipient_event_id, change_event_id) {
            return Err(LaneForestErrorV2::OutputEventMismatch);
        }
        decode_digest_canonical(&root).map_err(|_| LaneForestErrorV2::NonCanonicalDigest)?;
        let recipient = decode_digest_canonical(&recipient_commitment)
            .map_err(|_| LaneForestErrorV2::NonCanonicalDigest)?;
        let change = decode_digest_canonical(&change_commitment)
            .map_err(|_| LaneForestErrorV2::NonCanonicalDigest)?;
        let pair_leaf = encode_digest_canonical(
            &PoolV1PairLeafWitnessV1::two_outputs(recipient, change)?.leaf_digest()?,
        );
        Ok(Self {
            lane_id: supplied_lane,
            pair_leaf_index,
            root_sequence,
            pair_leaf,
            root,
            kind: LaneAppendKindV2::PrivateTransfer {
                recipient_event_id,
                change_event_id,
                recipient_commitment,
                change_commitment,
                track_recipient,
                track_change,
            },
        })
    }

    fn event_ids(&self) -> (DepositEventIdV1, Option<DepositEventIdV1>) {
        match self.kind {
            LaneAppendKindV2::Deposit { event_id, .. } => (event_id, None),
            LaneAppendKindV2::PrivateTransfer {
                recipient_event_id,
                change_event_id,
                ..
            } => (recipient_event_id, Some(change_event_id)),
        }
    }
}

fn same_private_transfer_event_v2(recipient: DepositEventIdV1, change: DepositEventIdV1) -> bool {
    recipient.point() == change.point()
        && recipient.transaction_signature() == change.transaction_signature()
        && recipient.instruction_index() == change.instruction_index()
        && recipient
            .event_index()
            .checked_add(1)
            .is_some_and(|next| next == change.event_index())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LaneScanCursorV2 {
    pub version: u8,
    pub lane_id: LaneIdV2,
    pub next_pair_index: u64,
    pub root_sequence: u64,
    pub root: [u8; 32],
    pub frontier: [[u8; 32]; POOL_V1_TREE_DEPTH],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LaneWitnessStateV2 {
    lane_id: LaneIdV2,
    witness: WalletWitnessStateV1,
    tracked_outputs: Vec<LaneTrackedOutputV2>,
}

impl LaneWitnessStateV2 {
    fn empty(lane_id: LaneIdV2) -> Self {
        Self {
            lane_id,
            witness: WalletWitnessStateV1::empty(),
            tracked_outputs: Vec::new(),
        }
    }

    pub const fn lane_id(&self) -> LaneIdV2 {
        self.lane_id
    }

    pub fn witness(&self) -> &WalletWitnessStateV1 {
        &self.witness
    }

    pub fn tracked_outputs(&self) -> &[LaneTrackedOutputV2] {
        &self.tracked_outputs
    }

    pub fn scan_cursor_v2(&self) -> LaneScanCursorV2 {
        let tree = self.witness.tree();
        LaneScanCursorV2 {
            version: POOL_V1_LANE_FOREST_VERSION_V2,
            lane_id: self.lane_id,
            next_pair_index: tree.next_leaf_index,
            root_sequence: tree.next_leaf_index,
            root: encode_digest_canonical(&tree.root),
            frontier: tree.frontier.map(|node| encode_digest_canonical(&node)),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LaneCheckpointComponentV2 {
    pub lane_id: LaneIdV2,
    pub root_sequence: u64,
    pub root: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LaneForestCheckpointV2 {
    pub version: u8,
    pub checkpoint_sequence: u64,
    pub global_root: [u8; 32],
    components: [LaneCheckpointComponentV2; POOL_V1_LANE_COUNT_V2],
}

impl LaneForestCheckpointV2 {
    pub fn new(
        checkpoint_sequence: u64,
        global_root: [u8; 32],
        components: Vec<LaneCheckpointComponentV2>,
    ) -> Result<Self, LaneForestErrorV2> {
        decode_digest_canonical(&global_root).map_err(|_| LaneForestErrorV2::NonCanonicalDigest)?;
        if components.len() != POOL_V1_LANE_COUNT_V2 {
            return Err(LaneForestErrorV2::IncompleteLaneSet);
        }
        let mut by_lane = [None; POOL_V1_LANE_COUNT_V2];
        for component in components {
            decode_digest_canonical(&component.root)
                .map_err(|_| LaneForestErrorV2::NonCanonicalDigest)?;
            let index = component.lane_id.index();
            if by_lane[index].replace(component).is_some() {
                return Err(LaneForestErrorV2::LaneAlias);
            }
        }
        let components = by_lane
            .map(|entry| entry.ok_or(LaneForestErrorV2::IncompleteLaneSet))
            .into_iter()
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .map_err(|_| LaneForestErrorV2::IncompleteLaneSet)?;
        Ok(Self {
            version: POOL_V1_LANE_FOREST_VERSION_V2,
            checkpoint_sequence,
            global_root,
            components,
        })
    }

    pub fn components(&self) -> &[LaneCheckpointComponentV2; POOL_V1_LANE_COUNT_V2] {
        &self.components
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LaneForestSnapshotV2 {
    checkpoint: LaneForestCheckpointV2,
    lanes: [LaneWitnessStateV2; POOL_V1_LANE_COUNT_V2],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LaneRollbackSummaryV2 {
    pub from_checkpoint_sequence: u64,
    pub to_checkpoint_sequence: u64,
    pub before_lane_sequences: [u64; POOL_V1_LANE_COUNT_V2],
    pub after_lane_sequences: [u64; POOL_V1_LANE_COUNT_V2],
    pub removed_checkpoints: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LaneForestWalletStateV2 {
    version: u8,
    lanes: [LaneWitnessStateV2; POOL_V1_LANE_COUNT_V2],
    checkpoints: Vec<LaneForestSnapshotV2>,
}

impl LaneForestWalletStateV2 {
    pub fn from_genesis_checkpoint_v2(
        checkpoint: LaneForestCheckpointV2,
    ) -> Result<Self, LaneForestErrorV2> {
        if checkpoint.checkpoint_sequence != 0 {
            return Err(LaneForestErrorV2::CheckpointSequenceMismatch);
        }
        let lanes = core::array::from_fn(|index| {
            LaneWitnessStateV2::empty(LaneIdV2::new(index as u8).expect("0..8 lane"))
        });
        validate_checkpoint_against_lanes_v2(&checkpoint, &lanes)?;
        Ok(Self {
            version: POOL_V1_LANE_FOREST_VERSION_V2,
            checkpoints: vec![LaneForestSnapshotV2 {
                checkpoint,
                lanes: lanes.clone(),
            }],
            lanes,
        })
    }

    pub const fn version(&self) -> u8 {
        self.version
    }

    pub fn lane(&self, lane_id: LaneIdV2) -> &LaneWitnessStateV2 {
        &self.lanes[lane_id.index()]
    }

    pub fn lanes(&self) -> &[LaneWitnessStateV2; POOL_V1_LANE_COUNT_V2] {
        &self.lanes
    }

    pub fn current_checkpoint(&self) -> &LaneForestCheckpointV2 {
        &self
            .checkpoints
            .last()
            .expect("genesis checkpoint is retained")
            .checkpoint
    }

    /// Apply authenticated appends and the one checkpoint that commits their
    /// resulting eight-lane state. Work is performed on a complete clone.
    pub fn apply_appends_and_checkpoint_v2(
        &mut self,
        appends: &[LaneAppendRecordV2],
        checkpoint: LaneForestCheckpointV2,
    ) -> Result<Vec<WitnessAppendReceiptV1>, LaneForestErrorV2> {
        let previous = self.current_checkpoint();
        if previous.checkpoint_sequence.checked_add(1) != Some(checkpoint.checkpoint_sequence) {
            return Err(LaneForestErrorV2::CheckpointSequenceMismatch);
        }
        ensure_unique_append_events_v2(&self.lanes, appends)?;

        let mut candidate_lanes = self.lanes.clone();
        let mut receipts = Vec::with_capacity(appends.len());
        for append in appends {
            receipts.push(apply_one_lane_append_v2(&mut candidate_lanes, append)?);
        }
        validate_checkpoint_against_lanes_v2(&checkpoint, &candidate_lanes)?;
        let made_progress = checkpoint
            .components
            .iter()
            .zip(previous.components.iter())
            .try_fold(false, |strict, (next, prior)| {
                if next.root_sequence < prior.root_sequence {
                    Err(LaneForestErrorV2::CheckpointLaneSequenceMismatch)
                } else {
                    Ok(strict || next.root_sequence > prior.root_sequence)
                }
            })?;
        if !made_progress {
            return Err(LaneForestErrorV2::CheckpointNoProgress);
        }

        self.lanes = candidate_lanes;
        self.checkpoints.push(LaneForestSnapshotV2 {
            checkpoint,
            lanes: self.lanes.clone(),
        });
        Ok(receipts)
    }

    /// Restore the complete eight-lane snapshot and discard every later
    /// checkpoint. No lane can be rolled back independently.
    pub fn rollback_to_checkpoint_v2(
        &mut self,
        checkpoint_sequence: u64,
    ) -> Result<LaneRollbackSummaryV2, LaneForestErrorV2> {
        let target = self
            .checkpoints
            .iter()
            .position(|entry| entry.checkpoint.checkpoint_sequence == checkpoint_sequence)
            .ok_or(LaneForestErrorV2::UnknownCheckpoint)?;
        let before_lane_sequences = self.lane_sequences_v2();
        let from_checkpoint_sequence = self.current_checkpoint().checkpoint_sequence;
        let removed_checkpoints = self.checkpoints.len() - target - 1;
        let restored = self.checkpoints[target].lanes.clone();
        self.checkpoints.truncate(target + 1);
        self.lanes = restored;
        Ok(LaneRollbackSummaryV2 {
            from_checkpoint_sequence,
            to_checkpoint_sequence: checkpoint_sequence,
            before_lane_sequences,
            after_lane_sequences: self.lane_sequences_v2(),
            removed_checkpoints,
        })
    }

    pub fn lane_sequences_v2(&self) -> [u64; POOL_V1_LANE_COUNT_V2] {
        self.lanes
            .each_ref()
            .map(|lane| lane.witness.tree().next_leaf_index)
    }
}

fn validate_checkpoint_against_lanes_v2(
    checkpoint: &LaneForestCheckpointV2,
    lanes: &[LaneWitnessStateV2; POOL_V1_LANE_COUNT_V2],
) -> Result<(), LaneForestErrorV2> {
    for (component, lane) in checkpoint.components.iter().zip(lanes.iter()) {
        let cursor = lane.scan_cursor_v2();
        if component.lane_id != lane.lane_id {
            return Err(LaneForestErrorV2::LaneAlias);
        }
        if component.root_sequence != cursor.root_sequence {
            return Err(LaneForestErrorV2::CheckpointLaneSequenceMismatch);
        }
        if component.root != cursor.root {
            return Err(LaneForestErrorV2::CheckpointLaneRootMismatch);
        }
    }
    Ok(())
}

fn ensure_unique_append_events_v2(
    lanes: &[LaneWitnessStateV2; POOL_V1_LANE_COUNT_V2],
    appends: &[LaneAppendRecordV2],
) -> Result<(), LaneForestErrorV2> {
    let mut seen = Vec::new();
    for append in appends {
        let (first, second) = append.event_ids();
        for event_id in core::iter::once(first).chain(second) {
            if seen.contains(&event_id)
                || lanes.iter().any(|lane| {
                    lane.tracked_outputs
                        .iter()
                        .any(|output| output.output_event_id == event_id)
                })
            {
                return Err(LaneForestErrorV2::DuplicateAppend);
            }
            seen.push(event_id);
        }
    }
    Ok(())
}

fn apply_one_lane_append_v2(
    lanes: &mut [LaneWitnessStateV2; POOL_V1_LANE_COUNT_V2],
    append: &LaneAppendRecordV2,
) -> Result<WitnessAppendReceiptV1, LaneForestErrorV2> {
    let lane = &mut lanes[append.lane_id.index()];
    let tracked_event_id = match append.kind {
        LaneAppendKindV2::Deposit {
            event_id, track, ..
        } => track.then_some(event_id),
        LaneAppendKindV2::PrivateTransfer {
            recipient_event_id,
            track_recipient,
            track_change,
            ..
        } => (track_recipient || track_change).then_some(recipient_event_id),
    };
    let receipt = lane.witness.append_authenticated_leaf_v1(
        append.pair_leaf_index,
        append.root_sequence,
        append.pair_leaf,
        append.root,
        tracked_event_id,
    )?;
    match append.kind {
        LaneAppendKindV2::Deposit {
            event_id,
            commitment,
            track,
        } => {
            if track {
                lane.tracked_outputs.push(LaneTrackedOutputV2 {
                    output_event_id: event_id,
                    witness_event_id: event_id,
                    lane_id: append.lane_id,
                    pair_leaf_index: append.pair_leaf_index,
                    slot: PairSlotV2::First,
                    commitment,
                });
            }
        }
        LaneAppendKindV2::PrivateTransfer {
            recipient_event_id,
            change_event_id,
            recipient_commitment,
            change_commitment,
            track_recipient,
            track_change,
        } => {
            if track_recipient {
                lane.tracked_outputs.push(LaneTrackedOutputV2 {
                    output_event_id: recipient_event_id,
                    witness_event_id: recipient_event_id,
                    lane_id: append.lane_id,
                    pair_leaf_index: append.pair_leaf_index,
                    slot: PairSlotV2::First,
                    commitment: recipient_commitment,
                });
            }
            if track_change {
                lane.tracked_outputs.push(LaneTrackedOutputV2 {
                    output_event_id: change_event_id,
                    witness_event_id: recipient_event_id,
                    lane_id: append.lane_id,
                    pair_leaf_index: append.pair_leaf_index,
                    slot: PairSlotV2::Second,
                    commitment: change_commitment,
                });
            }
        }
    }
    Ok(receipt)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scan_state::FinalizedChainPointV1;
    use aspis_core::field::M31;
    use aspis_statement::{pool_v1::IncrementalMerkleTreeV1, Digest};

    fn digest(first: u32, sentinel: u32) -> [u8; 32] {
        let mut value: Digest = [M31::ZERO; 8];
        value[0] = M31(first);
        value[7] = M31(sentinel);
        encode_digest_canonical(&value)
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

    fn genesis_checkpoint() -> LaneForestCheckpointV2 {
        let root = encode_digest_canonical(&IncrementalMerkleTreeV1::empty().root);
        LaneForestCheckpointV2::new(
            0,
            digest(100, 1),
            (0..8)
                .map(|lane| LaneCheckpointComponentV2 {
                    lane_id: LaneIdV2::new(lane).unwrap(),
                    root_sequence: 0,
                    root,
                })
                .collect(),
        )
        .unwrap()
    }

    fn state() -> LaneForestWalletStateV2 {
        LaneForestWalletStateV2::from_genesis_checkpoint_v2(genesis_checkpoint()).unwrap()
    }

    fn next_root(state: &LaneForestWalletStateV2, lane: LaneIdV2, pair_leaf: [u8; 32]) -> [u8; 32] {
        let leaf = decode_digest_canonical(&pair_leaf).unwrap();
        let (next, _) = state.lane(lane).witness().tree().append_one(leaf).unwrap();
        encode_digest_canonical(&next.root)
    }

    fn checkpoint_for_state_after(
        state: &LaneForestWalletStateV2,
        sequence: u64,
        appends: &[LaneAppendRecordV2],
    ) -> LaneForestCheckpointV2 {
        let mut trees: [IncrementalMerkleTreeV1; 8] =
            state.lanes().each_ref().map(|lane| *lane.witness().tree());
        for append in appends {
            let leaf = decode_digest_canonical(&append.pair_leaf).unwrap();
            trees[append.lane_id.index()] =
                trees[append.lane_id.index()].append_one(leaf).unwrap().0;
        }
        LaneForestCheckpointV2::new(
            sequence,
            digest(100 + sequence as u32, 1),
            (0..8)
                .map(|index| LaneCheckpointComponentV2 {
                    lane_id: LaneIdV2::new(index).unwrap(),
                    root_sequence: trees[index as usize].next_leaf_index,
                    root: encode_digest_canonical(&trees[index as usize].root),
                })
                .collect(),
        )
        .unwrap()
    }

    fn deposit_record(
        state: &LaneForestWalletStateV2,
        event_id: DepositEventIdV1,
        commitment: [u8; 32],
        track: bool,
    ) -> LaneAppendRecordV2 {
        let lane = deposit_lane_from_commitment_v2(commitment).unwrap();
        let pair =
            PoolV1PairLeafWitnessV1::single_output(decode_digest_canonical(&commitment).unwrap())
                .unwrap();
        let pair_leaf = encode_digest_canonical(&pair.leaf_digest().unwrap());
        let index = state.lane(lane).witness().tree().next_leaf_index;
        LaneAppendRecordV2::deposit(
            event_id,
            lane,
            commitment,
            index,
            index + 1,
            next_root(state, lane, pair_leaf),
            track,
            1,
        )
        .unwrap()
    }

    #[test]
    fn routing_uses_canonical_low_three_bits_and_rejects_aliases() {
        for expected in 0..8u8 {
            assert_eq!(
                deposit_lane_from_commitment_v2(digest(expected as u32, 1)).unwrap(),
                LaneIdV2::new(expected).unwrap()
            );
            assert_eq!(
                private_transfer_output_lane_v2(digest(expected as u32, 2)).unwrap(),
                LaneIdV2::new(expected).unwrap()
            );
        }
        assert_eq!(LaneIdV2::new(8), Err(LaneForestErrorV2::InvalidLane));
        let mut noncanonical = [0u8; 32];
        noncanonical[..4].copy_from_slice(&0x7fff_ffffu32.to_le_bytes());
        assert_eq!(
            deposit_lane_from_commitment_v2(noncanonical),
            Err(LaneForestErrorV2::NonCanonicalDigest)
        );
    }

    #[test]
    fn history_pages_require_complete_lane_keying_and_distinct_addresses() {
        let bindings = (0..8)
            .rev()
            .map(|lane| LaneRootHistoryPageBindingV2 {
                key: LaneRootHistoryPageKeyV2::new(LaneIdV2::new(lane).unwrap(), 0),
                address: [lane + 1; 32],
            })
            .collect::<Vec<_>>();
        let set = CompleteLaneRootPageSetV2::new(0, bindings.clone()).unwrap();
        assert!(set
            .bindings()
            .iter()
            .enumerate()
            .all(|(lane, binding)| binding.key.lane_id.index() == lane));

        let mut legacy = bindings.clone();
        for binding in &mut legacy {
            binding.address = [99; 32];
        }
        assert_eq!(
            CompleteLaneRootPageSetV2::new(0, legacy),
            Err(LaneForestErrorV2::LegacyPageZeroCollision)
        );
        assert_eq!(
            CompleteLaneRootPageSetV2::new(0, bindings[..7].to_vec()),
            Err(LaneForestErrorV2::IncompleteLaneSet)
        );
        let mut duplicate_lane = bindings;
        duplicate_lane[7].key.lane_id = duplicate_lane[0].key.lane_id;
        assert_eq!(
            CompleteLaneRootPageSetV2::new(0, duplicate_lane),
            Err(LaneForestErrorV2::LaneAlias)
        );
    }

    #[test]
    fn private_transfer_is_one_pair_append_with_two_slot_views() {
        let mut state = state();
        let nullifier = digest(5, 1);
        let lane = private_transfer_output_lane_v2(nullifier).unwrap();
        let recipient = digest(20, 1);
        let change = digest(21, 3);
        let pair = PoolV1PairLeafWitnessV1::two_outputs(
            decode_digest_canonical(&recipient).unwrap(),
            decode_digest_canonical(&change).unwrap(),
        )
        .unwrap();
        let pair_leaf = encode_digest_canonical(&pair.leaf_digest().unwrap());
        let first_id = event(10, 3, 0);
        let second_id = event(10, 3, 1);
        let append = LaneAppendRecordV2::private_transfer(
            first_id,
            second_id,
            lane,
            nullifier,
            recipient,
            change,
            0,
            1,
            next_root(&state, lane, pair_leaf),
            true,
            true,
            1,
        )
        .unwrap();
        assert_eq!(
            LaneAppendRecordV2::private_transfer(
                first_id,
                second_id,
                lane,
                nullifier,
                recipient,
                change,
                0,
                1,
                append.root,
                true,
                true,
                2,
            ),
            Err(LaneForestErrorV2::LegacyPerOutputAppend)
        );
        let checkpoint = checkpoint_for_state_after(&state, 1, &[append]);
        let receipts = state
            .apply_appends_and_checkpoint_v2(&[append], checkpoint)
            .unwrap();
        assert_eq!(receipts.len(), 1);
        assert_eq!(state.lane(lane).scan_cursor_v2().next_pair_index, 1);
        let outputs = state.lane(lane).tracked_outputs();
        assert_eq!(outputs.len(), 2);
        assert_eq!(outputs[0].slot, PairSlotV2::First);
        assert_eq!(outputs[1].slot, PairSlotV2::Second);
        assert_eq!(outputs[0].witness_event_id, outputs[1].witness_event_id);
        assert_eq!(outputs[0].pair_leaf_index, outputs[1].pair_leaf_index);
        assert_eq!(state.lane(lane).witness().tracked().len(), 1);
    }

    #[test]
    fn lanes_advance_independently_and_checkpoint_failure_is_atomic() {
        let mut state = state();
        let before = state.clone();
        let lane_two = deposit_record(&state, event(20, 1, 0), digest(2, 1), true);
        let lane_six = deposit_record(&state, event(20, 2, 0), digest(6, 1), false);
        let appends = [lane_two, lane_six];
        let mut bad = checkpoint_for_state_after(&state, 1, &appends);
        bad.components[2].root_sequence += 1;
        assert_eq!(
            state.apply_appends_and_checkpoint_v2(&appends, bad),
            Err(LaneForestErrorV2::CheckpointLaneSequenceMismatch)
        );
        assert_eq!(state, before);

        let checkpoint = checkpoint_for_state_after(&state, 1, &appends);
        state
            .apply_appends_and_checkpoint_v2(&appends, checkpoint)
            .unwrap();
        assert_eq!(state.lane_sequences_v2(), [0, 0, 1, 0, 0, 0, 1, 0]);
        assert_eq!(
            state
                .lane(LaneIdV2::new(2).unwrap())
                .tracked_outputs()
                .len(),
            1
        );
        assert_eq!(
            state
                .lane(LaneIdV2::new(6).unwrap())
                .tracked_outputs()
                .len(),
            0
        );
    }

    #[test]
    fn rollback_restores_all_eight_lanes_and_tracked_outputs() {
        let mut state = state();
        let initial = state.clone();
        let first = deposit_record(&state, event(30, 1, 0), digest(1, 1), true);
        let checkpoint_one = checkpoint_for_state_after(&state, 1, &[first]);
        state
            .apply_appends_and_checkpoint_v2(&[first], checkpoint_one)
            .unwrap();
        let after_one = state.clone();
        let second = deposit_record(&state, event(31, 1, 0), digest(7, 1), true);
        let checkpoint_two = checkpoint_for_state_after(&state, 2, &[second]);
        state
            .apply_appends_and_checkpoint_v2(&[second], checkpoint_two)
            .unwrap();
        let summary = state.rollback_to_checkpoint_v2(1).unwrap();
        assert_eq!(summary.before_lane_sequences, [0, 1, 0, 0, 0, 0, 0, 1]);
        assert_eq!(summary.after_lane_sequences, [0, 1, 0, 0, 0, 0, 0, 0]);
        assert_eq!(summary.removed_checkpoints, 1);
        assert_eq!(state, after_one);
        state.rollback_to_checkpoint_v2(0).unwrap();
        assert_eq!(state, initial);
    }

    #[test]
    fn wrong_lane_event_pair_and_duplicate_append_fail_closed() {
        let initial_state = state();
        let commitment = digest(3, 1);
        let wrong_lane = LaneIdV2::new(4).unwrap();
        let root = encode_digest_canonical(&initial_state.lane(wrong_lane).witness().tree().root);
        assert_eq!(
            LaneAppendRecordV2::deposit(
                event(40, 1, 0),
                wrong_lane,
                commitment,
                0,
                1,
                root,
                false,
                1,
            ),
            Err(LaneForestErrorV2::WrongRoutedLane)
        );

        let nullifier = digest(4, 1);
        let lane = private_transfer_output_lane_v2(nullifier).unwrap();
        assert_eq!(
            LaneAppendRecordV2::private_transfer(
                event(41, 1, 0),
                event(42, 1, 1),
                lane,
                nullifier,
                digest(10, 1),
                digest(11, 1),
                0,
                1,
                root,
                false,
                false,
                1,
            ),
            Err(LaneForestErrorV2::OutputEventMismatch)
        );

        let mut state = state();
        let duplicate_id = event(43, 1, 0);
        let first = deposit_record(&state, duplicate_id, digest(1, 1), false);
        let second = deposit_record(&state, duplicate_id, digest(2, 1), false);
        let checkpoint = checkpoint_for_state_after(&state, 1, &[first, second]);
        assert_eq!(
            state.apply_appends_and_checkpoint_v2(&[first, second], checkpoint),
            Err(LaneForestErrorV2::DuplicateAppend)
        );
        assert_eq!(state.lane_sequences_v2(), [0; 8]);
    }
}
