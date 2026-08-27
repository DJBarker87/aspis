//! Host-side row and masking inventory for the production-inactive Pool pair
//! profile.
//!
//! This freezes the exact row-level contract which the eventual tuple
//! registry and generated terminal must reproduce.  It is deliberately not a
//! verifier dispatch surface: tuple values, conditional append weights and
//! public-account bindings still have to be compiled and source-bridged
//! before this profile can be enabled.

use alloc::vec::Vec;

use crate::trace_v4::TraceCell;

use super::pair_tree_profile::{
    pool_v1_pair_path_base_row_v1, POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW,
    POOL_V1_PAIR_INPUT_SELECTED_SIDE_COLUMN, POOL_V1_PAIR_OCCUPANCY_COMMITMENT_COLUMN_END,
    POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW, POOL_V1_PAIR_PATH_LOCAL_ROW_OFFSET,
    POOL_V1_PAIR_POSEIDON_BLOCKS, POOL_V1_PAIR_POSEIDON_ROW_END, POOL_V1_PAIR_PRIVATE_DIRECTIONS,
    POOL_V1_PAIR_TRACE_BLOCK_ROWS, POOL_V1_PAIR_TRACE_COLUMNS, POOL_V1_PAIR_TRACE_ROWS,
    POOL_V1_PAIR_VALUE_AUX_ROW_START,
};

pub const POOL_V1_PAIR_RELATION_FREE_PADDING_LOCAL_ROW_START_V1: usize = 13;
pub const POOL_V1_PAIR_COPY_ROW_LINKS_V1: usize = 127;
pub const POOL_V1_PAIR_COPY_ACTIVE_ROWS_V1: usize = 199;
pub const POOL_V1_PAIR_RELATION_FREE_MASK_CELLS_V1: usize = 4_334;
pub const PINNED_POOL_V1_PAIR_COPY_ROW_SCHEDULE_FINGERPRINT_V1: u64 = 0x5b01_a440_7ba9_4fce;
pub const PINNED_POOL_V1_PAIR_COPY_ACTIVE_ROWS_FINGERPRINT_V1: u64 = 0x56e6_c3e3_f386_f273;
pub const PINNED_POOL_V1_PAIR_RELATION_FREE_MASK_FINGERPRINT_V1: u64 = 0x6a86_249a_2d85_591f;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairCopyRowLinkKindV1 {
    SpongeCarry {
        from: u8,
        to: u8,
    },
    OwnerOutput,
    NullifierKey,
    InputSaltHead,
    InputSaltTail,
    PrivatePathCurrent {
        level: u8,
    },
    PrivatePathLeft {
        level: u8,
    },
    PrivatePathRight {
        level: u8,
    },
    ValueSource {
        value: u8,
    },
    ConservationInput,
    ConservationRecipient,
    ConservationChange,
    ConservationPartial,
    InputSecondCommitment,
    InputSelectedSide,
    OutputSecondCommitment,
    OutputPairFirst,
    OutputPairFirstWithdrawal,
    OutputPairSecond,
    /// The two links at each level have complementary public weights
    /// `(1-bit, bit)`. Both rows remain in the fixed active-row inventory.
    AppendCurrentLeft {
        level: u8,
    },
    AppendCurrentRight {
        level: u8,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairCopyRowLinkV1 {
    pub kind: PoolV1PairCopyRowLinkKindV1,
    pub producer_row: u16,
    pub consumer_row: u16,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairHidingLayoutErrorV1 {
    Shape,
    EndpointCapacity { row: u16 },
}

#[inline]
fn link(
    kind: PoolV1PairCopyRowLinkKindV1,
    producer_row: usize,
    consumer_row: usize,
) -> PoolV1PairCopyRowLinkV1 {
    PoolV1PairCopyRowLinkV1 {
        kind,
        producer_row: producer_row as u16,
        consumer_row: consumer_row as u16,
    }
}

/// Exact row endpoints planned for the pair-tree tuple registry.
///
/// In particular, the append path is not represented by a private auxiliary
/// path.  Each level has two fixed row links with complementary public
/// direction weights.  This makes the active-row mask independent of the
/// current append index while preserving the exact late-bound direction.
pub fn build_pool_v1_pair_copy_row_schedule_v1(
) -> Result<Vec<PoolV1PairCopyRowLinkV1>, PoolV1PairHidingLayoutErrorV1> {
    let mut links = Vec::with_capacity(POOL_V1_PAIR_COPY_ROW_LINKS_V1);

    for (from, to) in [
        (1usize, 2usize),
        (2, 3),
        (25, 26),
        (27, 28),
        (28, 29),
        (30, 31),
        (31, 32),
    ] {
        links.push(link(
            PoolV1PairCopyRowLinkKindV1::SpongeCarry {
                from: from as u8,
                to: to as u8,
            },
            from * 16 + 11,
            to * 16,
        ));
    }

    links.push(link(PoolV1PairCopyRowLinkKindV1::OwnerOutput, 11, 28));
    links.push(link(PoolV1PairCopyRowLinkKindV1::NullifierKey, 12, 412));
    links.push(link(PoolV1PairCopyRowLinkKindV1::InputSaltHead, 44, 428));
    links.push(link(PoolV1PairCopyRowLinkKindV1::InputSaltTail, 60, 428));

    for level in 0..POOL_V1_PAIR_PRIVATE_DIRECTIONS {
        let aux =
            pool_v1_pair_path_base_row_v1(level).ok_or(PoolV1PairHidingLayoutErrorV1::Shape)?;
        let previous_output = (3 + level) * 16 + 11;
        let target_block = 4 + level;
        links.push(link(
            PoolV1PairCopyRowLinkKindV1::PrivatePathCurrent { level: level as u8 },
            previous_output,
            aux,
        ));
        links.push(link(
            PoolV1PairCopyRowLinkKindV1::PrivatePathLeft { level: level as u8 },
            aux + 1,
            target_block * 16 + 12,
        ));
        links.push(link(
            PoolV1PairCopyRowLinkKindV1::PrivatePathRight { level: level as u8 },
            aux + 1,
            target_block * 16,
        ));
    }

    for (value, source_row, destination_row) in
        [(0u8, 44usize, 960usize), (1, 460, 962), (2, 508, 964)]
    {
        links.push(link(
            PoolV1PairCopyRowLinkKindV1::ValueSource { value },
            source_row,
            destination_row,
        ));
    }
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::ConservationInput,
        960,
        966,
    ));
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::ConservationRecipient,
        962,
        966,
    ));
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::ConservationChange,
        964,
        967,
    ));
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::ConservationPartial,
        966,
        967,
    ));

    // Historical input-pair occupancy: duplicate the committed right child
    // and private selected-side bit into one row-local certificate.
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::InputSecondCommitment,
        64,
        POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW,
    ));
    let input_selected_side_row =
        pool_v1_pair_path_base_row_v1(0).ok_or(PoolV1PairHidingLayoutErrorV1::Shape)?;
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::InputSelectedSide,
        input_selected_side_row,
        POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW,
    ));

    // Newly appended output pair: the change commitment is certified in its
    // own occupancy row before that same complete digest enters the right
    // child of block 33. The recipient is the always-occupied left child.
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::OutputSecondCommitment,
        32 * 16 + 11,
        POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW,
    ));
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::OutputPairFirst,
        29 * 16 + 11,
        33 * 16 + 12,
    ));
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::OutputPairFirstWithdrawal,
        32 * 16 + 11,
        33 * 16 + 12,
    ));
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::OutputPairSecond,
        POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW,
        33 * 16,
    ));

    for level in 0..20usize {
        let previous_output = (33 + level) * 16 + 11;
        let target_block = 34 + level;
        links.push(link(
            PoolV1PairCopyRowLinkKindV1::AppendCurrentLeft { level: level as u8 },
            previous_output,
            target_block * 16 + 12,
        ));
        links.push(link(
            PoolV1PairCopyRowLinkKindV1::AppendCurrentRight { level: level as u8 },
            previous_output,
            target_block * 16,
        ));
    }

    if links.len() != POOL_V1_PAIR_COPY_ROW_LINKS_V1 {
        return Err(PoolV1PairHidingLayoutErrorV1::Shape);
    }
    endpoint_counts(&links)?;
    Ok(links)
}

fn endpoint_counts(
    links: &[PoolV1PairCopyRowLinkV1],
) -> Result<([u8; 1024], [u8; 1024]), PoolV1PairHidingLayoutErrorV1> {
    let mut producers = [0u8; 1024];
    let mut consumers = [0u8; 1024];
    for link in links {
        for (row, counts) in [
            (usize::from(link.producer_row), &mut producers),
            (usize::from(link.consumer_row), &mut consumers),
        ] {
            if row >= POOL_V1_PAIR_TRACE_ROWS || counts[row] >= 2 {
                return Err(PoolV1PairHidingLayoutErrorV1::EndpointCapacity { row: row as u16 });
            }
            counts[row] += 1;
        }
    }
    Ok((producers, consumers))
}

pub fn pool_v1_pair_copy_active_rows_v1() -> Result<Vec<u16>, PoolV1PairHidingLayoutErrorV1> {
    let links = build_pool_v1_pair_copy_row_schedule_v1()?;
    let mut rows = links
        .iter()
        .flat_map(|link| [link.producer_row, link.consumer_row])
        .collect::<Vec<_>>();
    rows.sort_unstable();
    rows.dedup();
    Ok(rows)
}

pub fn pool_v1_pair_copy_active_row_masks_v1() -> Result<[u16; 64], PoolV1PairHidingLayoutErrorV1> {
    let mut masks = [0u16; 64];
    for row in pool_v1_pair_copy_active_rows_v1()? {
        masks[usize::from(row) >> 4] |= 1 << (usize::from(row) & 15);
    }
    Ok(masks)
}

pub fn pool_v1_pair_copy_inactive_row_masks_v1() -> Result<[u16; 64], PoolV1PairHidingLayoutErrorV1>
{
    Ok(pool_v1_pair_copy_active_row_masks_v1()?.map(|mask| !mask))
}

fn path_aux_cell_is_used(row: usize, column: usize) -> bool {
    for level in 0..POOL_V1_PAIR_PRIVATE_DIRECTIONS {
        let Some(base) = pool_v1_pair_path_base_row_v1(level) else {
            return false;
        };
        if (row == base && column <= 8) || (row == base + 1) || (row == (base ^ 12) && column < 8) {
            return true;
        }
    }
    false
}

fn value_aux_cell_is_used(row: usize, column: usize) -> bool {
    for value in 0..3usize {
        let base = POOL_V1_PAIR_VALUE_AUX_ROW_START + 2 * value;
        if (row == base && column <= 10)
            || (row == base + 1 && column <= 10)
            || (row == (base ^ 12) && column <= 10)
        {
            return true;
        }
    }
    (row == POOL_V1_PAIR_VALUE_AUX_ROW_START + 6 && column < 3)
        || (row == POOL_V1_PAIR_VALUE_AUX_ROW_START + 7 && column < 2)
}

fn occupancy_aux_cell_is_used(row: usize, column: usize) -> bool {
    (row == POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW
        && column <= POOL_V1_PAIR_INPUT_SELECTED_SIDE_COLUMN)
        || (row == POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW
            && column < POOL_V1_PAIR_OCCUPANCY_COMMITMENT_COLUMN_END)
}

pub fn pool_v1_pair_aux_cell_is_relation_used_v1(row: usize, column: usize) -> bool {
    if row < POOL_V1_PAIR_POSEIDON_ROW_END
        || row >= POOL_V1_PAIR_TRACE_ROWS
        || column >= POOL_V1_PAIR_TRACE_COLUMNS
    {
        return false;
    }
    path_aux_cell_is_used(row, column)
        || value_aux_cell_is_used(row, column)
        || occupancy_aux_cell_is_used(row, column)
}

/// Exact relation-free inventory for the proposed row schedule. Every cell
/// is absent from the 54 Poseidon relations, all auxiliary residuals and the
/// fixed row-level copy endpoint schedule.
pub fn pool_v1_pair_relation_free_mask_cells_v1(
) -> Result<Vec<TraceCell>, PoolV1PairHidingLayoutErrorV1> {
    // Building the copy schedule here ensures endpoint capacity and its exact
    // row contract are checked before this inventory is consumed.
    let _ = build_pool_v1_pair_copy_row_schedule_v1()?;
    let mut cells = Vec::new();
    for column in 0..POOL_V1_PAIR_TRACE_COLUMNS {
        for row in 0..POOL_V1_PAIR_TRACE_ROWS {
            let padding = row < POOL_V1_PAIR_POSEIDON_ROW_END
                && row % POOL_V1_PAIR_TRACE_BLOCK_ROWS
                    >= POOL_V1_PAIR_RELATION_FREE_PADDING_LOCAL_ROW_START_V1;
            let undeclared_auxiliary = row >= POOL_V1_PAIR_POSEIDON_ROW_END
                && !pool_v1_pair_aux_cell_is_relation_used_v1(row, column);
            if padding || undeclared_auxiliary {
                cells.push(TraceCell {
                    row: row as u16,
                    column: column as u8,
                });
            }
        }
    }
    Ok(cells)
}

fn fingerprint_bytes<'a>(bytes: impl IntoIterator<Item = &'a u8>) -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    for byte in bytes {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

fn copy_row_link_kind_code_v1(kind: PoolV1PairCopyRowLinkKindV1) -> [u8; 3] {
    match kind {
        PoolV1PairCopyRowLinkKindV1::SpongeCarry { from, to } => [0, from, to],
        PoolV1PairCopyRowLinkKindV1::OwnerOutput => [1, 0, 0],
        PoolV1PairCopyRowLinkKindV1::NullifierKey => [2, 0, 0],
        PoolV1PairCopyRowLinkKindV1::InputSaltHead => [3, 0, 0],
        PoolV1PairCopyRowLinkKindV1::InputSaltTail => [4, 0, 0],
        PoolV1PairCopyRowLinkKindV1::PrivatePathCurrent { level } => [5, level, 0],
        PoolV1PairCopyRowLinkKindV1::PrivatePathLeft { level } => [6, level, 0],
        PoolV1PairCopyRowLinkKindV1::PrivatePathRight { level } => [7, level, 0],
        PoolV1PairCopyRowLinkKindV1::ValueSource { value } => [8, value, 0],
        PoolV1PairCopyRowLinkKindV1::ConservationInput => [9, 0, 0],
        PoolV1PairCopyRowLinkKindV1::ConservationRecipient => [10, 0, 0],
        PoolV1PairCopyRowLinkKindV1::ConservationChange => [11, 0, 0],
        PoolV1PairCopyRowLinkKindV1::ConservationPartial => [12, 0, 0],
        PoolV1PairCopyRowLinkKindV1::InputSecondCommitment => [13, 0, 0],
        PoolV1PairCopyRowLinkKindV1::InputSelectedSide => [14, 0, 0],
        PoolV1PairCopyRowLinkKindV1::OutputSecondCommitment => [15, 0, 0],
        PoolV1PairCopyRowLinkKindV1::OutputPairFirst => [16, 0, 0],
        PoolV1PairCopyRowLinkKindV1::OutputPairFirstWithdrawal => [17, 0, 0],
        PoolV1PairCopyRowLinkKindV1::OutputPairSecond => [18, 0, 0],
        PoolV1PairCopyRowLinkKindV1::AppendCurrentLeft { level } => [19, level, 0],
        PoolV1PairCopyRowLinkKindV1::AppendCurrentRight { level } => [20, level, 0],
    }
}

/// Fingerprint of every ordered copy-link meaning and both row endpoints.
/// This is stronger than the active-row fingerprint consumed by the rank
/// engine: it also detects swaps between producer/consumer roles, levels and
/// complementary append directions.
pub fn pool_v1_pair_copy_row_schedule_fingerprint_v1() -> Result<u64, PoolV1PairHidingLayoutErrorV1>
{
    let bytes = build_pool_v1_pair_copy_row_schedule_v1()?
        .into_iter()
        .flat_map(|link| {
            let kind = copy_row_link_kind_code_v1(link.kind);
            let producer = link.producer_row.to_le_bytes();
            let consumer = link.consumer_row.to_le_bytes();
            [
                kind[0],
                kind[1],
                kind[2],
                producer[0],
                producer[1],
                consumer[0],
                consumer[1],
            ]
        })
        .collect::<Vec<_>>();
    Ok(fingerprint_bytes(bytes.iter()))
}

pub fn pool_v1_pair_relation_free_mask_fingerprint_v1() -> Result<u64, PoolV1PairHidingLayoutErrorV1>
{
    let bytes = pool_v1_pair_relation_free_mask_cells_v1()?
        .into_iter()
        .flat_map(|cell| {
            let row = cell.row.to_le_bytes();
            [row[0], row[1], cell.column]
        })
        .collect::<Vec<_>>();
    Ok(fingerprint_bytes(bytes.iter()))
}

pub fn pool_v1_pair_copy_active_rows_fingerprint_v1() -> Result<u64, PoolV1PairHidingLayoutErrorV1>
{
    let bytes = pool_v1_pair_copy_active_rows_v1()?
        .into_iter()
        .flat_map(u16::to_le_bytes)
        .collect::<Vec<_>>();
    Ok(fingerprint_bytes(bytes.iter()))
}

const _: () = assert!(POOL_V1_PAIR_POSEIDON_BLOCKS == 54);
const _: () = assert!(POOL_V1_PAIR_POSEIDON_ROW_END == 864);
const _: () = assert!(POOL_V1_PAIR_PATH_LOCAL_ROW_OFFSET == 1);

#[cfg(test)]
mod tests {
    use super::*;

    fn contains(cells: &[TraceCell], row: usize, column: usize) -> bool {
        cells
            .binary_search_by_key(&(column as u8, row as u16), |cell| (cell.column, cell.row))
            .is_ok()
    }

    #[test]
    fn exact_row_schedule_has_bounded_endpoint_capacity() {
        let links = build_pool_v1_pair_copy_row_schedule_v1().unwrap();
        assert_eq!(links.len(), POOL_V1_PAIR_COPY_ROW_LINKS_V1);
        let selected_side = links
            .iter()
            .find(|link| link.kind == PoolV1PairCopyRowLinkKindV1::InputSelectedSide)
            .unwrap();
        assert_eq!(
            usize::from(selected_side.producer_row),
            pool_v1_pair_path_base_row_v1(0).unwrap(),
        );
        assert_eq!(
            usize::from(selected_side.consumer_row),
            POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW,
        );
        let (producers, consumers) = endpoint_counts(&links).unwrap();
        assert!(producers.into_iter().all(|count| count <= 2));
        assert!(consumers.into_iter().all(|count| count <= 2));
        // The public-variant dual output routing consumes the final available
        // slots at precisely these two endpoints.
        assert_eq!(producers[32 * 16 + 11], 2);
        assert_eq!(consumers[33 * 16 + 12], 2);
        assert_eq!(
            pool_v1_pair_copy_row_schedule_fingerprint_v1().unwrap(),
            PINNED_POOL_V1_PAIR_COPY_ROW_SCHEDULE_FINGERPRINT_V1,
        );
    }

    #[test]
    fn relation_free_inventory_preserves_all_48_tail_rows() {
        let cells = pool_v1_pair_relation_free_mask_cells_v1().unwrap();
        assert!(cells
            .windows(2)
            .all(|pair| (pair[0].column, pair[0].row) < (pair[1].column, pair[1].row)));
        for column in 0..POOL_V1_PAIR_TRACE_COLUMNS {
            for row in 976..POOL_V1_PAIR_TRACE_ROWS {
                assert!(contains(&cells, row, column));
            }
            for block in 0..POOL_V1_PAIR_POSEIDON_BLOCKS {
                for local in 13..16 {
                    assert!(contains(
                        &cells,
                        block * POOL_V1_PAIR_TRACE_BLOCK_ROWS + local,
                        column,
                    ));
                }
            }
        }
        for row in [
            POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW,
            POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW,
        ] {
            for column in 0..POOL_V1_PAIR_OCCUPANCY_COMMITMENT_COLUMN_END {
                assert!(!contains(&cells, row, column));
            }
        }
        assert!(!contains(
            &cells,
            POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW,
            POOL_V1_PAIR_INPUT_SELECTED_SIDE_COLUMN,
        ));
        assert_eq!(cells.len(), POOL_V1_PAIR_RELATION_FREE_MASK_CELLS_V1);
        assert_eq!(
            pool_v1_pair_relation_free_mask_fingerprint_v1().unwrap(),
            PINNED_POOL_V1_PAIR_RELATION_FREE_MASK_FINGERPRINT_V1,
        );
    }

    #[test]
    fn active_and_inactive_masks_are_exact_complements() {
        let active = pool_v1_pair_copy_active_row_masks_v1().unwrap();
        let inactive = pool_v1_pair_copy_inactive_row_masks_v1().unwrap();
        assert_eq!(
            pool_v1_pair_copy_active_rows_v1().unwrap().len(),
            POOL_V1_PAIR_COPY_ACTIVE_ROWS_V1,
        );
        assert_eq!(
            pool_v1_pair_copy_active_rows_fingerprint_v1().unwrap(),
            PINNED_POOL_V1_PAIR_COPY_ACTIVE_ROWS_FINGERPRINT_V1,
        );
        for group in 0..64 {
            assert_eq!(active[group] ^ inactive[group], u16::MAX);
            assert_eq!(active[group] & inactive[group], 0);
        }
        assert_eq!(active[63], 0);
        assert_eq!(inactive[63], u16::MAX);
    }
}
