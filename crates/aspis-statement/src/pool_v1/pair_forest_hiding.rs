//! Production-inactive row/masking inventory for the eight-lane pair forest.
//!
//! The existing pair profile uses blocks `0..=53` for Poseidon, blocks
//! `54..=59` for 21 private path directions, and block `60` for value and
//! occupancy auxiliaries.  A literal use of blocks `61..=63` for the three
//! new parents is raw-opening-rank deficient.  The forest therefore permutes
//! the same ten-block tail: blocks `54..=56` are the three historical
//! lane-to-super-root parents, blocks `57..=62` carry all 24 private
//! directions, and block `63` carries value and occupancy auxiliaries.
//!
//! This is a layout gate only.  It does not activate a profile, change the
//! prover, or claim that the resulting mask map has full rank.  The prover
//! rank gate consumes this exact inventory separately.

use alloc::vec::Vec;

use crate::trace_v4::TraceCell;

use super::{
    pair_tree_hiding::{
        build_pool_v1_pair_copy_row_schedule_v1, pool_v1_pair_aux_cell_is_relation_used_v1,
        PoolV1PairCopyRowLinkKindV1, PoolV1PairCopyRowLinkV1, PoolV1PairHidingLayoutErrorV1,
        POOL_V1_PAIR_RELATION_FREE_PADDING_LOCAL_ROW_START_V1,
    },
    pair_tree_profile::{
        POOL_V1_PAIR_DIRECTIONS_PER_AUX_BLOCK, POOL_V1_PAIR_TRACE_BLOCK_ROWS,
        POOL_V1_PAIR_TRACE_COLUMNS, POOL_V1_PAIR_TRACE_ROWS,
    },
};

pub const POOL_V1_PAIR_FOREST_LANES_V1: usize = 8;
pub const POOL_V1_PAIR_FOREST_SUPER_ROOT_DEPTH_V1: usize = 3;
pub const POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1: usize = 24;
pub const POOL_V1_PAIR_FOREST_FIRST_SUPER_ROOT_BLOCK_V1: usize = 54;
pub const POOL_V1_PAIR_FOREST_POSEIDON_BLOCKS_V1: usize = 57;
pub const POOL_V1_PAIR_FOREST_PATH_AUX_ROW_START_V1: usize = 57 * 16;
pub const POOL_V1_PAIR_FOREST_PATH_AUX_ROW_END_V1: usize = 63 * 16;
pub const POOL_V1_PAIR_FOREST_VALUE_AUX_ROW_START_V1: usize = 63 * 16;
pub const POOL_V1_PAIR_FOREST_INPUT_OCCUPANCY_AUX_ROW_V1: usize = 63 * 16 + 9;
pub const POOL_V1_PAIR_FOREST_OUTPUT_OCCUPANCY_AUX_ROW_V1: usize = 63 * 16 + 10;
pub const POOL_V1_PAIR_FOREST_SEMANTIC_ROW_END_V1: usize = 64 * 16;
pub const POOL_V1_PAIR_FOREST_COPY_ROW_LINKS_V1: usize = 136;
pub const POOL_V1_PAIR_FOREST_COPY_ACTIVE_ROWS_V1: usize = 214;
pub const POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_CELLS_V1: usize = 3_611;
pub const PINNED_POOL_V1_PAIR_FOREST_COPY_ROW_SCHEDULE_FINGERPRINT_V1: u64 = 0x4808_09b8_3677_8dc6;
pub const PINNED_POOL_V1_PAIR_FOREST_COPY_ACTIVE_ROWS_FINGERPRINT_V1: u64 = 0xdf39_4a5a_8554_d09c;
pub const PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1: u64 = 0x1a13_c450_d356_0861;

#[inline]
pub const fn pool_v1_pair_forest_path_base_row_v1(level: usize) -> Option<usize> {
    if level >= POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1 {
        return None;
    }
    Some(
        POOL_V1_PAIR_FOREST_PATH_AUX_ROW_START_V1
            + (level / POOL_V1_PAIR_DIRECTIONS_PER_AUX_BLOCK) * POOL_V1_PAIR_TRACE_BLOCK_ROWS
            + 1
            + 4 * (level % POOL_V1_PAIR_DIRECTIONS_PER_AUX_BLOCK),
    )
}

#[inline]
pub const fn pool_v1_pair_forest_membership_hash_block_v1(level: usize) -> Option<usize> {
    if level >= POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1 {
        None
    } else if level <= 20 {
        Some(4 + level)
    } else {
        Some(33 + level)
    }
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

pub fn build_pool_v1_pair_forest_copy_row_schedule_v1(
) -> Result<Vec<PoolV1PairCopyRowLinkV1>, PoolV1PairHidingLayoutErrorV1> {
    let mut links = build_pool_v1_pair_copy_row_schedule_v1()?
        .into_iter()
        .filter(|scheduled| {
            !matches!(
                scheduled.kind,
                PoolV1PairCopyRowLinkKindV1::PrivatePathCurrent { .. }
                    | PoolV1PairCopyRowLinkKindV1::PrivatePathLeft { .. }
                    | PoolV1PairCopyRowLinkKindV1::PrivatePathRight { .. }
            )
        })
        .collect::<Vec<_>>();
    // The existing schedule's auxiliary endpoints live in rows 864..975.
    // Move that complete seven-block region forward by three blocks while
    // leaving every existing Poseidon endpoint unchanged.
    for scheduled in &mut links {
        if usize::from(scheduled.producer_row) >= 54 * POOL_V1_PAIR_TRACE_BLOCK_ROWS {
            scheduled.producer_row += 3 * POOL_V1_PAIR_TRACE_BLOCK_ROWS as u16;
        }
        if usize::from(scheduled.consumer_row) >= 54 * POOL_V1_PAIR_TRACE_BLOCK_ROWS {
            scheduled.consumer_row += 3 * POOL_V1_PAIR_TRACE_BLOCK_ROWS as u16;
        }
    }
    links.reserve(3 * POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1);
    for level in 0..POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1 {
        let auxiliary = pool_v1_pair_forest_path_base_row_v1(level)
            .ok_or(PoolV1PairHidingLayoutErrorV1::Shape)?;
        let target_block = pool_v1_pair_forest_membership_hash_block_v1(level)
            .ok_or(PoolV1PairHidingLayoutErrorV1::Shape)?;
        let previous_block = if level == 0 {
            3
        } else {
            pool_v1_pair_forest_membership_hash_block_v1(level - 1)
                .ok_or(PoolV1PairHidingLayoutErrorV1::Shape)?
        };
        links.push(link(
            PoolV1PairCopyRowLinkKindV1::PrivatePathCurrent { level: level as u8 },
            previous_block * POOL_V1_PAIR_TRACE_BLOCK_ROWS + 11,
            auxiliary,
        ));
        links.push(link(
            PoolV1PairCopyRowLinkKindV1::PrivatePathLeft { level: level as u8 },
            auxiliary + 1,
            target_block * POOL_V1_PAIR_TRACE_BLOCK_ROWS + 12,
        ));
        links.push(link(
            PoolV1PairCopyRowLinkKindV1::PrivatePathRight { level: level as u8 },
            auxiliary + 1,
            target_block * POOL_V1_PAIR_TRACE_BLOCK_ROWS,
        ));
    }
    if links.len() != POOL_V1_PAIR_FOREST_COPY_ROW_LINKS_V1 {
        return Err(PoolV1PairHidingLayoutErrorV1::Shape);
    }
    endpoint_counts(&links)?;
    Ok(links)
}

pub fn pool_v1_pair_forest_copy_active_rows_v1() -> Result<Vec<u16>, PoolV1PairHidingLayoutErrorV1>
{
    let mut rows = build_pool_v1_pair_forest_copy_row_schedule_v1()?
        .into_iter()
        .flat_map(|link| [link.producer_row, link.consumer_row])
        .collect::<Vec<_>>();
    rows.sort_unstable();
    rows.dedup();
    Ok(rows)
}

pub fn pool_v1_pair_forest_copy_active_row_masks_v1(
) -> Result<[u16; 64], PoolV1PairHidingLayoutErrorV1> {
    let mut masks = [0u16; 64];
    for row in pool_v1_pair_forest_copy_active_rows_v1()? {
        masks[usize::from(row) >> 4] |= 1 << (usize::from(row) & 15);
    }
    Ok(masks)
}

pub fn pool_v1_pair_forest_copy_inactive_row_masks_v1(
) -> Result<[u16; 64], PoolV1PairHidingLayoutErrorV1> {
    Ok(pool_v1_pair_forest_copy_active_row_masks_v1()?.map(|mask| !mask))
}

fn forest_path_aux_cell_is_used(row: usize, column: usize) -> bool {
    for level in 0..POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1 {
        let Some(base) = pool_v1_pair_forest_path_base_row_v1(level) else {
            return false;
        };
        if (row == base && column <= 8) || row == base + 1 || (row == base + 2 && column < 8) {
            return true;
        }
    }
    false
}

#[inline]
fn forest_poseidon_row(row: usize) -> bool {
    row < POOL_V1_PAIR_FOREST_POSEIDON_BLOCKS_V1 * POOL_V1_PAIR_TRACE_BLOCK_ROWS
}

fn forest_aux_cell_is_used(row: usize, column: usize) -> bool {
    if row < POOL_V1_PAIR_FOREST_PATH_AUX_ROW_START_V1 {
        return false;
    }
    if row < POOL_V1_PAIR_FOREST_VALUE_AUX_ROW_START_V1 {
        forest_path_aux_cell_is_used(row, column)
    } else {
        let translated = row - 3 * POOL_V1_PAIR_TRACE_BLOCK_ROWS;
        pool_v1_pair_aux_cell_is_relation_used_v1(translated, column)
    }
}

pub fn pool_v1_pair_forest_relation_free_mask_cells_v1(
) -> Result<Vec<TraceCell>, PoolV1PairHidingLayoutErrorV1> {
    let _ = build_pool_v1_pair_forest_copy_row_schedule_v1()?;
    let mut cells = Vec::new();
    for column in 0..POOL_V1_PAIR_TRACE_COLUMNS {
        for row in 0..POOL_V1_PAIR_TRACE_ROWS {
            let poseidon = forest_poseidon_row(row);
            let padding = poseidon
                && row % POOL_V1_PAIR_TRACE_BLOCK_ROWS
                    >= POOL_V1_PAIR_RELATION_FREE_PADDING_LOCAL_ROW_START_V1;
            let auxiliary = !poseidon && !forest_aux_cell_is_used(row, column);
            if padding || auxiliary {
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

fn copy_kind_code(kind: PoolV1PairCopyRowLinkKindV1) -> [u8; 3] {
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

pub fn pool_v1_pair_forest_copy_row_schedule_fingerprint_v1(
) -> Result<u64, PoolV1PairHidingLayoutErrorV1> {
    let bytes = build_pool_v1_pair_forest_copy_row_schedule_v1()?
        .into_iter()
        .flat_map(|link| {
            let kind = copy_kind_code(link.kind);
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

pub fn pool_v1_pair_forest_copy_active_rows_fingerprint_v1(
) -> Result<u64, PoolV1PairHidingLayoutErrorV1> {
    let bytes = pool_v1_pair_forest_copy_active_rows_v1()?
        .into_iter()
        .flat_map(u16::to_le_bytes)
        .collect::<Vec<_>>();
    Ok(fingerprint_bytes(bytes.iter()))
}

pub fn pool_v1_pair_forest_relation_free_mask_fingerprint_v1(
) -> Result<u64, PoolV1PairHidingLayoutErrorV1> {
    let bytes = pool_v1_pair_forest_relation_free_mask_cells_v1()?
        .into_iter()
        .flat_map(|cell| {
            let row = cell.row.to_le_bytes();
            [row[0], row[1], cell.column]
        })
        .collect::<Vec<_>>();
    Ok(fingerprint_bytes(bytes.iter()))
}

const _: () = assert!(POOL_V1_PAIR_FOREST_LANES_V1 == 1 << 3);
const _: () = assert!(POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1 == 6 * 4);
const _: () = assert!(POOL_V1_PAIR_FOREST_FIRST_SUPER_ROOT_BLOCK_V1 * 16 == 864);
const _: () = assert!(POOL_V1_PAIR_FOREST_POSEIDON_BLOCKS_V1 == 54 + 3);
const _: () = assert!(POOL_V1_PAIR_FOREST_SEMANTIC_ROW_END_V1 == POOL_V1_PAIR_TRACE_ROWS);

#[cfg(test)]
mod tests {
    use super::*;
    use std::println;

    fn contains(cells: &[TraceCell], row: usize, column: usize) -> bool {
        cells
            .binary_search_by_key(&(column as u8, row as u16), |cell| (cell.column, cell.row))
            .is_ok()
    }

    #[test]
    fn exact_forest_layout_inventory() {
        let schedule = build_pool_v1_pair_forest_copy_row_schedule_v1().unwrap();
        let active = pool_v1_pair_forest_copy_active_rows_v1().unwrap();
        let masks = pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
        assert_eq!(schedule.len(), 136);
        assert_eq!(active.len(), POOL_V1_PAIR_FOREST_COPY_ACTIVE_ROWS_V1);
        assert_eq!(masks.len(), POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_CELLS_V1);
        assert_eq!(pool_v1_pair_forest_path_base_row_v1(21), Some(997));
        assert_eq!(pool_v1_pair_forest_path_base_row_v1(22), Some(1001));
        assert_eq!(pool_v1_pair_forest_path_base_row_v1(23), Some(1005));
        assert_eq!(pool_v1_pair_forest_membership_hash_block_v1(21), Some(54));
        assert_eq!(pool_v1_pair_forest_membership_hash_block_v1(22), Some(55));
        assert_eq!(pool_v1_pair_forest_membership_hash_block_v1(23), Some(56));
        assert!(!contains(&masks, 864, 0));
        assert!(!contains(&masks, 876, 0));
        assert!(contains(&masks, 877, 0));
        assert!(!contains(&masks, 997, 0));
        assert_eq!(
            pool_v1_pair_forest_copy_row_schedule_fingerprint_v1().unwrap(),
            PINNED_POOL_V1_PAIR_FOREST_COPY_ROW_SCHEDULE_FINGERPRINT_V1
        );
        assert_eq!(
            pool_v1_pair_forest_copy_active_rows_fingerprint_v1().unwrap(),
            PINNED_POOL_V1_PAIR_FOREST_COPY_ACTIVE_ROWS_FINGERPRINT_V1
        );
        assert_eq!(
            pool_v1_pair_forest_relation_free_mask_fingerprint_v1().unwrap(),
            PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1
        );
        println!(
            "forest links={} active={} masks={} copy_fp={:#018x} active_fp={:#018x} mask_fp={:#018x}",
            schedule.len(),
            active.len(),
            masks.len(),
            pool_v1_pair_forest_copy_row_schedule_fingerprint_v1().unwrap(),
            pool_v1_pair_forest_copy_active_rows_fingerprint_v1().unwrap(),
            pool_v1_pair_forest_relation_free_mask_fingerprint_v1().unwrap(),
        );
    }
}
