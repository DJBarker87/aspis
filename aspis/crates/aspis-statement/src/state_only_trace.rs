//! Host-side foundation for the experimental 16-column state-only trace.
//!
//! This module deliberately does not alter the frozen v4 proof format.  It
//! projects an already-built [`SpendTraceV4`] into the physical layout being
//! investigated by `docs/stage2-state-only-two-round-candidate.md`, and gives
//! the host tests an independent replay surface before any auxiliary/copy or
//! direct-range cells are remapped.

use alloc::vec;
use alloc::vec::Vec;

use aspis_core::field::{M31, QM31};

use crate::poseidon2::{evaluate_trace_round_pair, DIGEST_ELEMS, POSEIDON2_WIDTH, RATE};
use crate::trace_v4::{
    copy_layout, merkle_boundary_layout, source_relation_layout, witness_aux_layout, CopyLink,
    CopyLinkKind, CopyTuple, SpendTraceV4, TraceCell, TupleLimb, WitnessAuxLayout,
    ABSORPTION_ROW_IN_BLOCK, ACTIVE_ROWS_PER_BLOCK, AUX_ABSORPTION_PRODUCER_ROW_START, BLOCK_ROWS,
    FIRST_ROUND_OUTPUT_COLUMN_START, INTERFACE_COLUMN_START, PERMUTATION_COUNT,
    SECOND_ROUND_OUTPUT_COLUMN_START, TRACE_ROWS,
};

pub const STATE_ONLY_C1_COLUMNS: usize = POSEIDON2_WIDTH;
pub const STATE_ONLY_FINAL_ROW_IN_BLOCK: usize = ACTIVE_ROWS_PER_BLOCK;
pub const STATE_ONLY_ABSORPTION_ROW_IN_BLOCK: usize = STATE_ONLY_FINAL_ROW_IN_BLOCK + 1;
pub const STATE_ONLY_PADDING_ROW_START_IN_BLOCK: usize = STATE_ONLY_ABSORPTION_ROW_IN_BLOCK + 1;
pub const STATE_ONLY_TRANSITIONS_PER_BLOCK: usize = ACTIVE_ROWS_PER_BLOCK;
pub const STATE_ONLY_TRANSITION_COUNT: usize = PERMUTATION_COUNT * STATE_ONLY_TRANSITIONS_PER_BLOCK;
pub const STATE_ONLY_AUX_ROW_START: usize = PERMUTATION_COUNT * BLOCK_ROWS;
pub const STATE_ONLY_AUX_ROW_END: usize = 864;
pub const STATE_ONLY_AUX_ROW_COUNT: usize = STATE_ONLY_AUX_ROW_END - STATE_ONLY_AUX_ROW_START;
pub const STATE_ONLY_DIRECT_RANGE_ROW_START: usize = STATE_ONLY_AUX_ROW_END;
pub const STATE_ONLY_DIRECT_RANGE_LIMB_COUNT: usize = 6;
pub const STATE_ONLY_DIRECT_RANGE_BITS: usize = 10;
pub const STATE_ONLY_DIRECT_RANGE_RECONSTRUCTION_COLUMN: usize = STATE_ONLY_DIRECT_RANGE_BITS;
pub const STATE_ONLY_DIRECT_RANGE_INPUT_TOTAL_COLUMN: usize = 11;
pub const STATE_ONLY_DIRECT_RANGE_BALANCE_OUTPUT_COLUMN: usize = 12;
/// Two `(z, succ(z), xor12(z))` triples: input limbs, then output limbs.
pub const STATE_ONLY_DIRECT_RANGE_ROWS: [usize; STATE_ONLY_DIRECT_RANGE_LIMB_COUNT] =
    [864, 865, 876, 866, 867, 878];
pub const STATE_ONLY_DIRECT_RANGE_ROW_END: usize = 879;
pub const STATE_ONLY_SURVIVING_COPY_LINK_COUNT: usize = 102;

/// This is pinned by the host test below.  It binds every logical old cell to
/// its physical state-only cell, as well as the dense surviving-copy order.
/// A layout change must deliberately update both this value and the tests.
pub const PINNED_STATE_ONLY_LAYOUT_FINGERPRINT: u64 = 0x121d_b4ec_14af_2130;
pub const PINNED_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT: u64 = 0x1420_cb92_10f5_2636;

/// Degree inventory for the eventual state-only zerocheck oracle.
///
/// `f(succ(z))` has individual degree at most ten: one input coordinate can
/// occur in at most all ten output coordinates of binary increment, while
/// `f` itself is multilinear.  The two-round Poseidon side dominates at
/// degree 25.  One active-row selector and the outer equality factor give the
/// conservative degree-27 sumcheck bound.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyDegreeBounds {
    pub successor_coordinate_total_degree: usize,
    pub successor_opening_individual_degree: usize,
    pub two_round_transition_individual_degree: usize,
    pub active_gated_individual_degree: usize,
    pub zerocheck_individual_degree: usize,
}

pub const STATE_ONLY_DEGREE_BOUNDS: StateOnlyDegreeBounds = StateOnlyDegreeBounds {
    successor_coordinate_total_degree: 10,
    successor_opening_individual_degree: 10,
    two_round_transition_individual_degree: 25,
    active_gated_individual_degree: 26,
    zerocheck_individual_degree: 27,
};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct StateOnlyTraceFoundation {
    /// Column-major, complete logical 16-column M31 table. Rows 0..783 are
    /// the state-only permutation blocks, rows 784..863 hold packed auxiliary
    /// cells, and two three-point triples in rows 864..878 hold the limbs.
    pub c1: [Vec<M31>; STATE_ONLY_C1_COLUMNS],
}

impl Drop for StateOnlyTraceFoundation {
    fn drop(&mut self) {
        // Host prover traces contain the unmasked witness before commitment.
        // Clear them on every return path instead of relying on allocator
        // reuse.  M31 is canonical, so zero is also a valid overwritten word.
        for column in &mut self.c1 {
            for value in column {
                // SAFETY: the vector is uniquely borrowed during drop.
                unsafe { core::ptr::write_volatile(value, M31::ZERO) };
            }
        }
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyLayoutError {
    MissingCell { row: u16, column: u8 },
    AuxComponentTooWide { cells: u16 },
    AuxCapacity { required_rows: u16 },
    EndpointNotRowLocal { link: u16 },
    Collision { row: u16, column: u8 },
}

/// The non-formula part of the old-to-new cell map. State cells and the six
/// range-limb cells have closed-form placements; everything else is listed
/// here in stable old-cell order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateOnlyCellMap {
    pub aux_entries: Vec<(TraceCell, TraceCell)>,
    pub aux_rows_used: u16,
}

impl StateOnlyCellMap {
    pub fn map(&self, old: TraceCell) -> Option<TraceCell> {
        let old = source_alias_target(old).unwrap_or(old);
        intrinsic_state_cell(old)
            .or_else(|| direct_range_reconstruction_cell(old))
            .or_else(|| direct_range_semantic_cell(old))
            .or_else(|| {
                self.aux_entries
                    .binary_search_by_key(&cell_key(old), |(source, _)| cell_key(*source))
                    .ok()
                    .map(|index| self.aux_entries[index].1)
            })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateOnlyCopyLayout {
    /// Dense links in the surviving canonical order. IDs and tags are
    /// deliberately reassigned to 0..101; `source_link_ids` records the old
    /// 490..591 provenance for independent parity tests.
    pub links: Vec<CopyLink>,
    pub source_link_ids: Vec<u16>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyTraceError {
    Shape,
    Layout(StateOnlyLayoutError),
    ProjectionMismatch { row: u16, column: u8 },
    FirstRoundMismatch { block: u8, local_row: u8, lane: u8 },
    SecondRoundMismatch { block: u8, local_row: u8, lane: u8 },
    SuccessorMismatch { block: u8, local_row: u8, lane: u8 },
    FinalStateMismatch { block: u8, lane: u8 },
    AbsorptionMismatch { block: u8, lane: u8 },
    AuxiliaryMismatch { row: u16, column: u8 },
    CopyMismatch { link: u16 },
    DirectRangeBitMismatch { limb: u8, bit: u8 },
    DirectRangeReconstructionMismatch { limb: u8 },
    NonZeroPadding { row: u16, lane: u8 },
}

/// Polynomial arithmetization of binary increment modulo `2^10` under the
/// trace's big-endian MLE coordinate convention.
///
/// On Boolean inputs this maps row `r` to `(r + 1) mod 1024`.  At an
/// off-domain point it is intentionally the polynomial representative of
/// increment, not the MLE of a pre-permuted table.
pub fn binary_successor_point(point: &[QM31; 10]) -> [QM31; 10] {
    let mut successor = [QM31::ZERO; 10];
    let mut carry = QM31::ONE;
    for coordinate in (0..point.len()).rev() {
        let value = point[coordinate];
        let value_times_carry = value.mul(carry);
        successor[coordinate] = value
            .add(carry)
            .sub(value_times_carry.add(value_times_carry));
        carry = carry.mul(value);
    }
    successor
}

/// Toggle row-index bits 2 and 3 (`12 = 0b1100`) under the big-endian MLE
/// coordinate convention.
pub fn xor12_point(point: &[QM31; 10]) -> [QM31; 10] {
    let mut shifted = *point;
    for bit in [2usize, 3] {
        let coordinate = point.len() - 1 - bit;
        shifted[coordinate] = QM31::ONE.sub(shifted[coordinate]);
    }
    shifted
}

const fn cell_key(cell: TraceCell) -> u32 {
    cell.row as u32 * 256 + cell.column as u32
}

fn push_cell(cells: &mut Vec<TraceCell>, cell: TraceCell) {
    cells.push(cell);
}

fn push_tuple_cells(cells: &mut Vec<TraceCell>, tuple: CopyTuple) {
    for limb in tuple.limbs {
        if let TupleLimb::Cell(cell) = limb {
            cells.push(cell);
        }
    }
}

fn push_witness_aux_cells(cells: &mut Vec<TraceCell>, aux: &WitnessAuxLayout) {
    for cell in aux
        .nullifier_key
        .into_iter()
        .chain(aux.input_salt)
        .chain(aux.output_salt)
        .chain(aux.output_owner_key)
    {
        push_cell(cells, cell);
    }
    for cell in [aux.input_asset_id, aux.value, aux.value_out] {
        push_cell(cells, cell);
    }
    for digest in aux.merkle_siblings {
        cells.extend(digest);
    }
    push_cell(cells, aux.merkle_path_index);
    cells.extend(aux.merkle_path_bits);
    cells.extend(aux.input_value_limbs);
    cells.extend(aux.output_value_limbs);
    for cell in [
        aux.input_value_reconstruction,
        aux.output_value_reconstruction,
        aux.output_value_for_balance,
    ] {
        push_cell(cells, cell);
    }
}

fn direct_range_source_cells() -> [TraceCell; STATE_ONLY_DIRECT_RANGE_LIMB_COUNT] {
    let aux = witness_aux_layout();
    [
        aux.input_value_limbs[0],
        aux.input_value_limbs[1],
        aux.input_value_limbs[2],
        aux.output_value_limbs[0],
        aux.output_value_limbs[1],
        aux.output_value_limbs[2],
    ]
}

/// The sixty frozen source equalities are represented structurally: both
/// logical names resolve to one committed cell. This saves sixty duplicate
/// auxiliaries and removes those identities from the runtime oracle without
/// weakening them.
fn source_alias_target(old: TraceCell) -> Option<TraceCell> {
    source_relation_layout().into_iter().find_map(|binding| {
        let row = (AUX_ABSORPTION_PRODUCER_ROW_START + usize::from(binding.block)) as u16;
        (old == TraceCell {
            row,
            column: binding.right_column,
        })
        .then_some(TraceCell {
            row,
            column: binding.left_column,
        })
    })
}

fn direct_range_reconstruction_cell(old: TraceCell) -> Option<TraceCell> {
    direct_range_source_cells()
        .iter()
        .position(|cell| *cell == old)
        .map(|limb| TraceCell {
            row: STATE_ONLY_DIRECT_RANGE_ROWS[limb] as u16,
            column: STATE_ONLY_DIRECT_RANGE_RECONSTRUCTION_COLUMN as u8,
        })
}

fn direct_range_semantic_cell(old: TraceCell) -> Option<TraceCell> {
    let aux = witness_aux_layout();
    if old == aux.input_value_reconstruction {
        Some(TraceCell {
            row: STATE_ONLY_DIRECT_RANGE_ROWS[0] as u16,
            column: STATE_ONLY_DIRECT_RANGE_INPUT_TOTAL_COLUMN as u8,
        })
    } else if old == aux.output_value_reconstruction {
        Some(TraceCell {
            row: STATE_ONLY_DIRECT_RANGE_ROWS[3] as u16,
            column: STATE_ONLY_DIRECT_RANGE_INPUT_TOTAL_COLUMN as u8,
        })
    } else if old == aux.output_value_for_balance {
        Some(TraceCell {
            row: STATE_ONLY_DIRECT_RANGE_ROWS[0] as u16,
            column: STATE_ONLY_DIRECT_RANGE_BALANCE_OUTPUT_COLUMN as u8,
        })
    } else {
        None
    }
}

/// Formula placements for the committed state. The old row-10 second-round
/// output is moved to row 11 and the old row-11 absorption payload is moved
/// to row 12. First-round columns and intermediate second-round columns have
/// no state-only cell because they are derived inside the transition oracle.
fn intrinsic_state_cell(old: TraceCell) -> Option<TraceCell> {
    let row = usize::from(old.row);
    let column = usize::from(old.column);
    if row >= STATE_ONLY_AUX_ROW_START {
        return None;
    }
    let local_row = row % BLOCK_ROWS;
    let base = row - local_row;
    if local_row < ACTIVE_ROWS_PER_BLOCK && column < POSEIDON2_WIDTH {
        return Some(old);
    }
    if local_row == ACTIVE_ROWS_PER_BLOCK - 1
        && (SECOND_ROUND_OUTPUT_COLUMN_START..SECOND_ROUND_OUTPUT_COLUMN_START + POSEIDON2_WIDTH)
            .contains(&column)
    {
        return Some(TraceCell {
            row: (base + STATE_ONLY_FINAL_ROW_IN_BLOCK) as u16,
            column: (column - SECOND_ROUND_OUTPUT_COLUMN_START) as u8,
        });
    }
    if local_row == ABSORPTION_ROW_IN_BLOCK && column < POSEIDON2_WIDTH {
        return Some(TraceCell {
            row: (base + STATE_ONLY_ABSORPTION_ROW_IN_BLOCK) as u16,
            column: column as u8,
        });
    }
    None
}

/// Stable inventory of every old cell retained by the state-only statement:
/// surviving copy endpoints, all private/public auxiliary dependencies,
/// source/selection relations, and the five public output digests.
pub fn state_only_required_old_cells_v4() -> Vec<TraceCell> {
    let mut cells = Vec::new();
    for link in copy_layout()
        .links
        .into_iter()
        .filter(|link| link.kind != CopyLinkKind::IntraPermutation)
    {
        push_tuple_cells(&mut cells, link.producer);
        push_tuple_cells(&mut cells, link.consumer);
    }

    let aux = witness_aux_layout();
    push_witness_aux_cells(&mut cells, &aux);
    for binding in source_relation_layout() {
        let row = (AUX_ABSORPTION_PRODUCER_ROW_START + usize::from(binding.block)) as u16;
        cells.push(TraceCell {
            row,
            column: binding.left_column,
        });
        cells.push(TraceCell {
            row,
            column: binding.right_column,
        });
    }
    for boundary in merkle_boundary_layout() {
        cells.push(boundary.path_bit);
        cells.extend(boundary.left);
        cells.extend(boundary.right);
        cells.extend(boundary.current);
        cells.extend(boundary.sibling);
    }

    // Five public digests are final outputs. The public asset mirror is a
    // separate source-slab cell, while input_asset_id is already in `aux`.
    for block in [0usize, 3, 43, 45, 48] {
        let row = block * BLOCK_ROWS + ACTIVE_ROWS_PER_BLOCK - 1;
        for limb in 0..DIGEST_ELEMS {
            cells.push(TraceCell {
                row: row as u16,
                column: (SECOND_ROUND_OUTPUT_COLUMN_START + limb) as u8,
            });
        }
    }
    cells.push(TraceCell {
        row: (AUX_ABSORPTION_PRODUCER_ROW_START + 47) as u16,
        column: 34,
    });

    cells.sort_unstable_by_key(|cell| cell_key(*cell));
    cells.dedup();
    cells
}

fn find_cell(cells: &[TraceCell], target: TraceCell) -> Option<usize> {
    cells
        .binary_search_by_key(&cell_key(target), |cell| cell_key(*cell))
        .ok()
}

fn find_root(parents: &mut [usize], mut index: usize) -> usize {
    let mut root = index;
    while parents[root] != root {
        root = parents[root];
    }
    while parents[index] != index {
        let next = parents[index];
        parents[index] = root;
        index = next;
    }
    root
}

fn union(parents: &mut [usize], left: usize, right: usize) {
    let left_root = find_root(parents, left);
    let right_root = find_root(parents, right);
    if left_root != right_root {
        if left_root < right_root {
            parents[right_root] = left_root;
        } else {
            parents[left_root] = right_root;
        }
    }
}

fn generic_aux_tuple_cells(tuple: CopyTuple, aux_cells: &[TraceCell]) -> Vec<usize> {
    tuple
        .limbs
        .into_iter()
        .filter_map(|limb| match limb {
            TupleLimb::Cell(cell) => {
                let cell = source_alias_target(cell).unwrap_or(cell);
                if intrinsic_state_cell(cell).is_some()
                    || direct_range_reconstruction_cell(cell).is_some()
                    || direct_range_semantic_cell(cell).is_some()
                {
                    return None;
                }
                find_cell(aux_cells, cell)
            }
            _ => None,
        })
        .collect()
}

fn place_aux_member(
    placements: &mut [Option<TraceCell>],
    row_masks: &mut [u16],
    member: usize,
    row: usize,
    column: usize,
) -> Result<(), StateOnlyLayoutError> {
    let row_index = row
        .checked_sub(STATE_ONLY_AUX_ROW_START)
        .filter(|index| *index < STATE_ONLY_AUX_ROW_COUNT)
        .ok_or(StateOnlyLayoutError::AuxCapacity {
            required_rows: (row + 1).saturating_sub(STATE_ONLY_AUX_ROW_START) as u16,
        })?;
    let bit = 1u16 << column;
    if row_masks[row_index] & bit != 0 {
        return Err(StateOnlyLayoutError::Collision {
            row: row as u16,
            column: column as u8,
        });
    }
    let cell = TraceCell {
        row: row as u16,
        column: column as u8,
    };
    if let Some(existing) = placements[member] {
        if existing != cell {
            return Err(StateOnlyLayoutError::Collision {
                row: existing.row,
                column: existing.column,
            });
        }
        return Ok(());
    }
    placements[member] = Some(cell);
    row_masks[row_index] |= bit;
    Ok(())
}

fn first_free_aux_columns(mask: u16, count: usize) -> Option<Vec<usize>> {
    let columns = (0..STATE_ONLY_C1_COLUMNS)
        .filter(|column| mask & (1u16 << column) == 0)
        .take(count)
        .collect::<Vec<_>>();
    (columns.len() == count).then_some(columns)
}

/// Build the deterministic old-to-new map.  The twenty Merkle selections are
/// placed first as `(z, succ(z), xor12(z))` triples: `bit || current`, then
/// `left || right`, then `sibling`. This makes the 33-value selection fit a
/// 16-column trace without adding a fourth PCS point. Remaining row-local
/// semantic and copy components are packed only after those triples.
pub fn build_state_only_cell_map_v4() -> Result<StateOnlyCellMap, StateOnlyLayoutError> {
    let required = state_only_required_old_cells_v4();
    let mut aux_cells = required
        .into_iter()
        .map(|cell| source_alias_target(cell).unwrap_or(cell))
        .filter(|cell| {
            intrinsic_state_cell(*cell).is_none()
                && direct_range_reconstruction_cell(*cell).is_none()
                && direct_range_semantic_cell(*cell).is_none()
        })
        .collect::<Vec<_>>();
    aux_cells.sort_unstable_by_key(|cell| cell_key(*cell));
    aux_cells.dedup();
    let mut parents = (0..aux_cells.len()).collect::<Vec<_>>();
    let mut endpoint_members = vec![false; aux_cells.len()];
    for link in copy_layout()
        .links
        .into_iter()
        .filter(|link| link.kind != CopyLinkKind::IntraPermutation)
    {
        for tuple in [link.producer, link.consumer] {
            let members = generic_aux_tuple_cells(tuple, &aux_cells);
            if let Some((&first, rest)) = members.split_first() {
                endpoint_members[first] = true;
                for &member in rest {
                    endpoint_members[member] = true;
                    union(&mut parents, first, member);
                }
            }
        }
    }

    let roots = (0..aux_cells.len())
        .map(|index| find_root(&mut parents, index))
        .collect::<Vec<_>>();
    let mut producer_occurrences = vec![0u8; aux_cells.len()];
    let mut consumer_occurrences = vec![0u8; aux_cells.len()];
    for link in copy_layout()
        .links
        .into_iter()
        .filter(|link| link.kind != CopyLinkKind::IntraPermutation)
    {
        for (tuple, occurrences) in [
            (link.producer, &mut producer_occurrences),
            (link.consumer, &mut consumer_occurrences),
        ] {
            if let Some(member) = generic_aux_tuple_cells(tuple, &aux_cells).first() {
                occurrences[roots[*member]] = occurrences[roots[*member]].saturating_add(1);
            }
        }
    }
    let mut components: Vec<(usize, Vec<usize>, bool)> = Vec::new();
    for (index, root) in roots.iter().copied().enumerate() {
        if let Some((_, members, endpoint)) =
            components.iter_mut().find(|(found, _, _)| *found == root)
        {
            members.push(index);
            *endpoint |= endpoint_members[index];
        } else {
            components.push((root, vec![index], endpoint_members[index]));
        }
    }
    components.sort_unstable_by_key(|(_, members, _)| cell_key(aux_cells[members[0]]));
    if let Some((_, members, _)) = components
        .iter()
        .find(|(_, members, _)| members.len() > STATE_ONLY_C1_COLUMNS)
    {
        return Err(StateOnlyLayoutError::AuxComponentTooWide {
            cells: members.len() as u16,
        });
    }

    let mut placements = vec![None; aux_cells.len()];
    let mut row_masks = vec![0u16; STATE_ONLY_AUX_ROW_COUNT];

    // Four levels per 16-row high block. For local bases 0,2,4,6 the three
    // rows `base`, `base+1`, `base xor 12` are pairwise disjoint.
    for boundary in merkle_boundary_layout() {
        let level = usize::from(boundary.level);
        let base = STATE_ONLY_AUX_ROW_START + 16 * (level / 4) + 2 * (level % 4);
        let successor = base + 1;
        let shifted = base ^ 12;
        let bit =
            find_cell(&aux_cells, boundary.path_bit).ok_or(StateOnlyLayoutError::MissingCell {
                row: boundary.path_bit.row,
                column: boundary.path_bit.column,
            })?;
        place_aux_member(&mut placements, &mut row_masks, bit, base, 0)?;
        for limb in 0..DIGEST_ELEMS {
            for (old, row, column) in [
                (boundary.current[limb], base, 1 + limb),
                (boundary.left[limb], successor, limb),
                (boundary.right[limb], successor, RATE + limb),
                (boundary.sibling[limb], shifted, limb),
            ] {
                let member =
                    find_cell(&aux_cells, old).ok_or(StateOnlyLayoutError::MissingCell {
                        row: old.row,
                        column: old.column,
                    })?;
                place_aux_member(&mut placements, &mut row_masks, member, row, column)?;
            }
        }
    }

    let mut row_producers = vec![0u8; STATE_ONLY_AUX_ROW_COUNT];
    let mut row_consumers = vec![0u8; STATE_ONLY_AUX_ROW_COUNT];

    // First complete components touched by the fixed triples and account for
    // their producer/consumer arity.
    for (root, members, endpoint) in &components {
        let pinned_rows = members
            .iter()
            .filter_map(|member| placements[*member].map(|cell| cell.row))
            .collect::<Vec<_>>();
        if pinned_rows.is_empty() {
            continue;
        }
        let row = pinned_rows[0];
        if pinned_rows.iter().any(|candidate| *candidate != row) {
            return Err(StateOnlyLayoutError::EndpointNotRowLocal { link: 0 });
        }
        let row_index = usize::from(row) - STATE_ONLY_AUX_ROW_START;
        let missing = members
            .iter()
            .filter(|member| placements[**member].is_none())
            .copied()
            .collect::<Vec<_>>();
        let columns = first_free_aux_columns(row_masks[row_index], missing.len()).ok_or(
            StateOnlyLayoutError::AuxComponentTooWide {
                cells: members.len() as u16,
            },
        )?;
        for (member, column) in missing.into_iter().zip(columns) {
            place_aux_member(
                &mut placements,
                &mut row_masks,
                member,
                usize::from(row),
                column,
            )?;
        }
        if *endpoint {
            row_producers[row_index] =
                row_producers[row_index].saturating_add(producer_occurrences[*root]);
            row_consumers[row_index] =
                row_consumers[row_index].saturating_add(consumer_occurrences[*root]);
            if row_producers[row_index] > 2 || row_consumers[row_index] > 2 {
                return Err(StateOnlyLayoutError::EndpointNotRowLocal { link: 0 });
            }
        }
    }

    // Then place untouched endpoint components, respecting the two-by-two
    // LogUp row shape, and finally pack relation-only cells into all spares.
    for endpoint_phase in [true, false] {
        for (root, members, endpoint) in &components {
            if *endpoint != endpoint_phase
                || members.iter().any(|member| placements[*member].is_some())
            {
                continue;
            }
            let producer_count = producer_occurrences[*root];
            let consumer_count = consumer_occurrences[*root];
            let Some(row_index) = (0..STATE_ONLY_AUX_ROW_COUNT).find(|row| {
                first_free_aux_columns(row_masks[*row], members.len()).is_some()
                    && (!endpoint_phase
                        || (row_producers[*row].saturating_add(producer_count) <= 2
                            && row_consumers[*row].saturating_add(consumer_count) <= 2))
            }) else {
                return Err(StateOnlyLayoutError::AuxCapacity {
                    required_rows: (STATE_ONLY_AUX_ROW_COUNT + 1) as u16,
                });
            };
            let columns = first_free_aux_columns(row_masks[row_index], members.len()).unwrap();
            for (&member, column) in members.iter().zip(columns) {
                place_aux_member(
                    &mut placements,
                    &mut row_masks,
                    member,
                    STATE_ONLY_AUX_ROW_START + row_index,
                    column,
                )?;
            }
            if endpoint_phase {
                row_producers[row_index] = row_producers[row_index].saturating_add(producer_count);
                row_consumers[row_index] = row_consumers[row_index].saturating_add(consumer_count);
            }
        }
    }

    let mut aux_entries = aux_cells
        .into_iter()
        .enumerate()
        .map(|(index, old)| (old, placements[index].expect("all aux cells placed")))
        .collect::<Vec<_>>();
    aux_entries.sort_unstable_by_key(|(old, _)| cell_key(*old));
    let aux_rows_used = row_masks
        .iter()
        .rposition(|mask| *mask != 0)
        .map_or(0, |last| last + 1) as u16;
    Ok(StateOnlyCellMap {
        aux_entries,
        aux_rows_used,
    })
}

fn remap_tuple(
    map: &StateOnlyCellMap,
    tuple: CopyTuple,
) -> Result<(CopyTuple, u16), StateOnlyLayoutError> {
    let mut row = None;
    let mut limbs = [TupleLimb::Zero; POSEIDON2_WIDTH];
    for (index, limb) in tuple.limbs.into_iter().enumerate() {
        if let TupleLimb::Cell(old) = limb {
            let new = map.map(old).ok_or(StateOnlyLayoutError::MissingCell {
                row: old.row,
                column: old.column,
            })?;
            if let Some(expected) = row {
                if expected != new.row {
                    return Err(StateOnlyLayoutError::EndpointNotRowLocal { link: 0 });
                }
            } else {
                row = Some(new.row);
            }
            limbs[index] = TupleLimb::Cell(new);
        }
    }
    Ok((CopyTuple { limbs }, row.unwrap_or(0)))
}

pub fn state_only_copy_layout_v4() -> Result<StateOnlyCopyLayout, StateOnlyLayoutError> {
    let map = build_state_only_cell_map_v4()?;
    let mut links = Vec::with_capacity(STATE_ONLY_SURVIVING_COPY_LINK_COUNT);
    let mut source_link_ids = Vec::with_capacity(STATE_ONLY_SURVIVING_COPY_LINK_COUNT);
    for old in copy_layout()
        .links
        .into_iter()
        .filter(|link| link.kind != CopyLinkKind::IntraPermutation)
    {
        let dense_id = links.len() as u16;
        let (producer, producer_row) =
            remap_tuple(&map, old.producer).map_err(|error| match error {
                StateOnlyLayoutError::EndpointNotRowLocal { .. } => {
                    StateOnlyLayoutError::EndpointNotRowLocal { link: old.id }
                }
                other => other,
            })?;
        let (consumer, consumer_row) =
            remap_tuple(&map, old.consumer).map_err(|error| match error {
                StateOnlyLayoutError::EndpointNotRowLocal { .. } => {
                    StateOnlyLayoutError::EndpointNotRowLocal { link: old.id }
                }
                other => other,
            })?;
        links.push(CopyLink {
            id: dense_id,
            tag: M31(u32::from(dense_id) + 1),
            kind: old.kind,
            producer_row,
            consumer_row,
            producer,
            consumer,
        });
        source_link_ids.push(old.id);
    }
    debug_assert_eq!(links.len(), STATE_ONLY_SURVIVING_COPY_LINK_COUNT);
    Ok(StateOnlyCopyLayout {
        links,
        source_link_ids,
    })
}

fn required_mapped_cell(
    map: &StateOnlyCellMap,
    old: TraceCell,
) -> Result<TraceCell, StateOnlyLayoutError> {
    map.map(old).ok_or(StateOnlyLayoutError::MissingCell {
        row: old.row,
        column: old.column,
    })
}

fn required_mapped_cells<const N: usize>(
    map: &StateOnlyCellMap,
    old: [TraceCell; N],
) -> Result<[TraceCell; N], StateOnlyLayoutError> {
    let mut mapped = old;
    for cell in &mut mapped {
        *cell = required_mapped_cell(map, *cell)?;
    }
    Ok(mapped)
}

/// Remapped public description of every private witness dependency. The six
/// 10-bit limbs point at column 10 of the two three-point range triples; their
/// bits occupy columns 0..9 of those same rows.
pub fn state_only_witness_aux_layout_v4() -> Result<WitnessAuxLayout, StateOnlyLayoutError> {
    let old = witness_aux_layout();
    let map = build_state_only_cell_map_v4()?;
    let mut merkle_siblings = old.merkle_siblings;
    for digest in &mut merkle_siblings {
        *digest = required_mapped_cells(&map, *digest)?;
    }
    Ok(WitnessAuxLayout {
        nullifier_key: required_mapped_cells(&map, old.nullifier_key)?,
        input_salt: required_mapped_cells(&map, old.input_salt)?,
        output_salt: required_mapped_cells(&map, old.output_salt)?,
        output_owner_key: required_mapped_cells(&map, old.output_owner_key)?,
        input_asset_id: required_mapped_cell(&map, old.input_asset_id)?,
        value: required_mapped_cell(&map, old.value)?,
        value_out: required_mapped_cell(&map, old.value_out)?,
        merkle_siblings,
        merkle_path_index: required_mapped_cell(&map, old.merkle_path_index)?,
        merkle_path_bits: required_mapped_cells(&map, old.merkle_path_bits)?,
        input_value_limbs: required_mapped_cells(&map, old.input_value_limbs)?,
        output_value_limbs: required_mapped_cells(&map, old.output_value_limbs)?,
        input_value_reconstruction: required_mapped_cell(&map, old.input_value_reconstruction)?,
        output_value_reconstruction: required_mapped_cell(&map, old.output_value_reconstruction)?,
        output_value_for_balance: required_mapped_cell(&map, old.output_value_for_balance)?,
    })
}

pub fn state_only_layout_fingerprint_v4() -> Result<u64, StateOnlyLayoutError> {
    let map = build_state_only_cell_map_v4()?;
    let copy = state_only_copy_layout_v4()?;
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    let mut absorb = |byte: u8| {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    };
    for old in state_only_required_old_cells_v4() {
        let new = map.map(old).ok_or(StateOnlyLayoutError::MissingCell {
            row: old.row,
            column: old.column,
        })?;
        for byte in old
            .row
            .to_le_bytes()
            .into_iter()
            .chain([old.column])
            .chain(new.row.to_le_bytes())
            .chain([new.column])
        {
            absorb(byte);
        }
    }
    for limb in 0..STATE_ONLY_DIRECT_RANGE_LIMB_COUNT {
        for bit in 0..STATE_ONLY_DIRECT_RANGE_BITS {
            absorb(0xff);
            absorb(limb as u8);
            absorb(bit as u8);
            for byte in (STATE_ONLY_DIRECT_RANGE_ROWS[limb] as u16)
                .to_le_bytes()
                .into_iter()
                .chain([bit as u8])
            {
                absorb(byte);
            }
        }
    }
    for (link, source_id) in copy.links.iter().zip(copy.source_link_ids) {
        for byte in source_id
            .to_le_bytes()
            .into_iter()
            .chain(link.id.to_le_bytes())
        {
            absorb(byte);
        }
    }
    Ok(hash)
}

/// Every C1 cell that is relation-free on the Boolean trace domain, in
/// column-major order. This is the sole layout API the hiding rank analysis
/// may consume: rows 0..=12 of permutation blocks, every mapped semantic/copy
/// endpoint, and all six direct-range rows are excluded mechanically.
pub fn state_only_relation_free_mask_cells_v4() -> Result<Vec<TraceCell>, StateOnlyLayoutError> {
    let map = build_state_only_cell_map_v4()?;
    let mut occupied = vec![false; STATE_ONLY_C1_COLUMNS * TRACE_ROWS];
    for old in state_only_required_old_cells_v4() {
        let cell = map.map(old).ok_or(StateOnlyLayoutError::MissingCell {
            row: old.row,
            column: old.column,
        })?;
        occupied[usize::from(cell.column) * TRACE_ROWS + usize::from(cell.row)] = true;
    }
    for row in STATE_ONLY_DIRECT_RANGE_ROWS {
        for column in 0..STATE_ONLY_DIRECT_RANGE_BITS {
            occupied[column * TRACE_ROWS + row] = true;
        }
    }

    let mut cells = Vec::new();
    for column in 0..STATE_ONLY_C1_COLUMNS {
        for row in 0..TRACE_ROWS {
            let in_relation_block = row < STATE_ONLY_AUX_ROW_START
                && row % BLOCK_ROWS < STATE_ONLY_PADDING_ROW_START_IN_BLOCK;
            if !in_relation_block && !occupied[column * TRACE_ROWS + row] {
                cells.push(TraceCell {
                    row: row as u16,
                    column: column as u8,
                });
            }
        }
    }
    Ok(cells)
}

pub fn state_only_relation_free_mask_fingerprint_v4() -> Result<u64, StateOnlyLayoutError> {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    for cell in state_only_relation_free_mask_cells_v4()? {
        for byte in cell.row.to_le_bytes().into_iter().chain([cell.column]) {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    Ok(hash)
}

/// Project the old 49-column honest trace into the state-only research
/// layout.  Production v4 messages and constraints are untouched.
pub fn project_state_only_trace_v4(
    trace: &SpendTraceV4,
) -> Result<StateOnlyTraceFoundation, StateOnlyTraceError> {
    if trace.c1.iter().any(|column| column.len() != TRACE_ROWS) {
        return Err(StateOnlyTraceError::Shape);
    }

    let mut c1: [Vec<M31>; STATE_ONLY_C1_COLUMNS] =
        core::array::from_fn(|_| vec![M31::ZERO; TRACE_ROWS]);
    for block in 0..PERMUTATION_COUNT {
        let base = block * BLOCK_ROWS;
        for local_row in 0..ACTIVE_ROWS_PER_BLOCK {
            let row = base + local_row;
            for lane in 0..POSEIDON2_WIDTH {
                c1[lane][row] = trace.c1[INTERFACE_COLUMN_START + lane][row];
            }
        }
        let old_final_row = base + ACTIVE_ROWS_PER_BLOCK - 1;
        let final_row = base + STATE_ONLY_FINAL_ROW_IN_BLOCK;
        let old_absorption_row = base + ABSORPTION_ROW_IN_BLOCK;
        let absorption_row = base + STATE_ONLY_ABSORPTION_ROW_IN_BLOCK;
        for lane in 0..POSEIDON2_WIDTH {
            c1[lane][final_row] = trace.c1[SECOND_ROUND_OUTPUT_COLUMN_START + lane][old_final_row];
            c1[lane][absorption_row] = trace.c1[lane][old_absorption_row];
        }
    }

    let map = build_state_only_cell_map_v4().map_err(StateOnlyTraceError::Layout)?;
    for &(old, new) in &map.aux_entries {
        c1[usize::from(new.column)][usize::from(new.row)] =
            trace.c1[usize::from(old.column)][usize::from(old.row)];
    }
    let aux = witness_aux_layout();
    for old in [
        aux.input_value_reconstruction,
        aux.output_value_reconstruction,
        aux.output_value_for_balance,
    ] {
        let new = direct_range_semantic_cell(old).expect("pinned range semantic cell");
        c1[usize::from(new.column)][usize::from(new.row)] =
            trace.c1[usize::from(old.column)][usize::from(old.row)];
    }
    for (limb, old) in direct_range_source_cells().into_iter().enumerate() {
        let value = trace.c1[usize::from(old.column)][usize::from(old.row)];
        let row = STATE_ONLY_DIRECT_RANGE_ROWS[limb];
        for bit in 0..STATE_ONLY_DIRECT_RANGE_BITS {
            c1[bit][row] = M31((value.0 >> bit) & 1);
        }
        c1[STATE_ONLY_DIRECT_RANGE_RECONSTRUCTION_COLUMN][row] = value;
    }

    let projected = StateOnlyTraceFoundation { c1 };
    validate_state_only_projection(trace, &projected)?;
    Ok(projected)
}

/// Replay every one of the 49 * 11 two-round transitions and compare the
/// state-only projection with both old round-output interfaces.  This is an
/// exact host guard, not a replacement for the future polynomial constraints.
pub fn validate_state_only_projection(
    source: &SpendTraceV4,
    projected: &StateOnlyTraceFoundation,
) -> Result<(), StateOnlyTraceError> {
    if source.c1.iter().any(|column| column.len() != TRACE_ROWS)
        || projected.c1.iter().any(|column| column.len() != TRACE_ROWS)
    {
        return Err(StateOnlyTraceError::Shape);
    }

    for block in 0..PERMUTATION_COUNT {
        let base = block * BLOCK_ROWS;
        let absorption_row = base + STATE_ONLY_ABSORPTION_ROW_IN_BLOCK;
        for local_row in 0..ACTIVE_ROWS_PER_BLOCK {
            let row = base + local_row;
            let mut input = core::array::from_fn(|lane| projected.c1[lane][row]);
            for lane in 0..POSEIDON2_WIDTH {
                if projected.c1[lane][row] != source.c1[INTERFACE_COLUMN_START + lane][row] {
                    return Err(StateOnlyTraceError::ProjectionMismatch {
                        row: row as u16,
                        column: lane as u8,
                    });
                }
            }
            if local_row == 0 {
                for lane in 0..RATE {
                    input[lane] = input[lane].add(projected.c1[lane][absorption_row]);
                }
            }
            let (first, second) =
                evaluate_trace_round_pair(input, local_row).ok_or(StateOnlyTraceError::Shape)?;
            for lane in 0..POSEIDON2_WIDTH {
                if first[lane] != source.c1[FIRST_ROUND_OUTPUT_COLUMN_START + lane][row] {
                    return Err(StateOnlyTraceError::FirstRoundMismatch {
                        block: block as u8,
                        local_row: local_row as u8,
                        lane: lane as u8,
                    });
                }
                if second[lane] != source.c1[SECOND_ROUND_OUTPUT_COLUMN_START + lane][row] {
                    return Err(StateOnlyTraceError::SecondRoundMismatch {
                        block: block as u8,
                        local_row: local_row as u8,
                        lane: lane as u8,
                    });
                }
                if projected.c1[lane][row + 1] != second[lane] {
                    return Err(StateOnlyTraceError::SuccessorMismatch {
                        block: block as u8,
                        local_row: local_row as u8,
                        lane: lane as u8,
                    });
                }
            }
        }

        let old_final_row = base + ACTIVE_ROWS_PER_BLOCK - 1;
        let final_row = base + STATE_ONLY_FINAL_ROW_IN_BLOCK;
        let old_absorption_row = base + ABSORPTION_ROW_IN_BLOCK;
        for lane in 0..POSEIDON2_WIDTH {
            if projected.c1[lane][final_row]
                != source.c1[SECOND_ROUND_OUTPUT_COLUMN_START + lane][old_final_row]
            {
                return Err(StateOnlyTraceError::FinalStateMismatch {
                    block: block as u8,
                    lane: lane as u8,
                });
            }
            if projected.c1[lane][absorption_row] != source.c1[lane][old_absorption_row] {
                return Err(StateOnlyTraceError::AbsorptionMismatch {
                    block: block as u8,
                    lane: lane as u8,
                });
            }
        }
        for local_row in STATE_ONLY_PADDING_ROW_START_IN_BLOCK..BLOCK_ROWS {
            let row = base + local_row;
            for lane in 0..POSEIDON2_WIDTH {
                if projected.c1[lane][row] != M31::ZERO {
                    return Err(StateOnlyTraceError::NonZeroPadding {
                        row: row as u16,
                        lane: lane as u8,
                    });
                }
            }
        }
    }

    let map = build_state_only_cell_map_v4().map_err(StateOnlyTraceError::Layout)?;
    for old in state_only_required_old_cells_v4() {
        let new = map.map(old).ok_or(StateOnlyTraceError::Layout(
            StateOnlyLayoutError::MissingCell {
                row: old.row,
                column: old.column,
            },
        ))?;
        if projected.c1[usize::from(new.column)][usize::from(new.row)]
            != source.c1[usize::from(old.column)][usize::from(old.row)]
        {
            return Err(StateOnlyTraceError::AuxiliaryMismatch {
                row: new.row,
                column: new.column,
            });
        }
    }

    for (limb, old) in direct_range_source_cells().into_iter().enumerate() {
        let value = source.c1[usize::from(old.column)][usize::from(old.row)];
        let row = STATE_ONLY_DIRECT_RANGE_ROWS[limb];
        let mut reconstruction = 0u32;
        for bit in 0..STATE_ONLY_DIRECT_RANGE_BITS {
            let found = projected.c1[bit][row];
            if found != M31::ZERO && found != M31::ONE {
                return Err(StateOnlyTraceError::DirectRangeBitMismatch {
                    limb: limb as u8,
                    bit: bit as u8,
                });
            }
            reconstruction |= found.0 << bit;
        }
        if projected.c1[STATE_ONLY_DIRECT_RANGE_RECONSTRUCTION_COLUMN][row] != value
            || M31(reconstruction) != value
        {
            return Err(StateOnlyTraceError::DirectRangeReconstructionMismatch {
                limb: limb as u8,
            });
        }
    }

    let copy = state_only_copy_layout_v4().map_err(StateOnlyTraceError::Layout)?;
    for link in copy.links {
        if tuple_value_state_only(projected, link.producer)
            != tuple_value_state_only(projected, link.consumer)
        {
            return Err(StateOnlyTraceError::CopyMismatch { link: link.id });
        }
    }

    let mut occupied = vec![false; STATE_ONLY_C1_COLUMNS * TRACE_ROWS];
    for &(_, cell) in &map.aux_entries {
        occupied[usize::from(cell.row) * STATE_ONLY_C1_COLUMNS + usize::from(cell.column)] = true;
    }
    for row in STATE_ONLY_AUX_ROW_START..STATE_ONLY_AUX_ROW_END {
        for column in 0..STATE_ONLY_C1_COLUMNS {
            if !occupied[row * STATE_ONLY_C1_COLUMNS + column]
                && projected.c1[column][row] != M31::ZERO
            {
                return Err(StateOnlyTraceError::NonZeroPadding {
                    row: row as u16,
                    lane: column as u8,
                });
            }
        }
    }
    Ok(())
}

fn tuple_value_state_only(
    trace: &StateOnlyTraceFoundation,
    tuple: CopyTuple,
) -> [M31; POSEIDON2_WIDTH] {
    tuple.limbs.map(|limb| match limb {
        TupleLimb::Cell(cell) => trace.c1[usize::from(cell.column)][usize::from(cell.row)],
        TupleLimb::Zero => M31::ZERO,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::CM31;

    use crate::constraints_v4::multilinear_evaluate;
    use crate::poseidon2::Digest;
    use crate::spend::{
        derive_nullifier, derive_owner_key, merkle_root, note_commitment, output_commitment,
        MerklePath, SpendPublic, SpendWitness,
    };
    use crate::trace_v4::{build_spend_trace_v4, validate_spend_trace_v4};

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32 * 17))
    }

    fn fixture() -> (SpendPublic, SpendWitness) {
        let nullifier_key = digest(101);
        let input_salt = digest(301);
        let output_salt = digest(501);
        let output_owner_key = digest(701);
        let asset_id = M31(17);
        let value = 1_000_000;
        let value_out = 999_999;
        let fee = 1;
        let owner_key = derive_owner_key(&nullifier_key);
        let note = note_commitment(&owner_key, value, asset_id, &input_salt);
        let path = MerklePath {
            siblings: (0..20)
                .map(|level| digest(1_000 + level as u32 * 31))
                .collect(),
            index: 0x5a5a5,
        };
        let public = SpendPublic {
            anchor: merkle_root(note, &path).unwrap(),
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output_commitment(
                &output_owner_key,
                value_out,
                asset_id,
                &output_salt,
            ),
            asset_id,
            fee,
        };
        let witness = SpendWitness {
            nullifier_key,
            input_salt,
            output_salt,
            output_owner_key,
            input_asset_id: asset_id,
            value,
            value_out,
            merkle_path: path,
        };
        (public, witness)
    }

    fn boolean_point(row: usize) -> [QM31; 10] {
        core::array::from_fn(|coordinate| {
            let bit = (row >> (9 - coordinate)) & 1;
            if bit == 0 {
                QM31::ZERO
            } else {
                QM31::ONE
            }
        })
    }

    fn boolean_row(point: &[QM31; 10]) -> usize {
        point.iter().fold(0usize, |row, coordinate| {
            (row << 1) | usize::from(*coordinate == QM31::ONE)
        })
    }

    fn next_u32(state: &mut u64) -> u32 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        ((*state >> 32) as u32) % aspis_core::field::P
    }

    fn random_qm31(state: &mut u64) -> QM31 {
        QM31 {
            c0: CM31::new(M31(next_u32(state)), M31(next_u32(state))),
            c1: CM31::new(M31(next_u32(state)), M31(next_u32(state))),
        }
    }

    fn dense_mle(column: &[M31], point: &[QM31; 10]) -> QM31 {
        (0..TRACE_ROWS).fold(QM31::ZERO, |sum, row| {
            let weight = point
                .iter()
                .enumerate()
                .fold(QM31::ONE, |weight, (coordinate, value)| {
                    let bit = (row >> (9 - coordinate)) & 1;
                    weight.mul(if bit == 0 {
                        QM31::ONE.sub(*value)
                    } else {
                        *value
                    })
                });
            sum.add(weight.mul_m31(column[row]))
        })
    }

    fn source_tuple_value(source: &SpendTraceV4, tuple: CopyTuple) -> [M31; POSEIDON2_WIDTH] {
        tuple.limbs.map(|limb| match limb {
            TupleLimb::Cell(cell) => source.c1[usize::from(cell.column)][usize::from(cell.row)],
            TupleLimb::Zero => M31::ZERO,
        })
    }

    #[test]
    fn successor_and_xor12_map_every_boolean_row_exactly() {
        for row in 0..TRACE_ROWS {
            assert_eq!(
                boolean_row(&binary_successor_point(&boolean_point(row))),
                (row + 1) % TRACE_ROWS
            );
            assert_eq!(boolean_row(&xor12_point(&boolean_point(row))), row ^ 12);
        }
    }

    #[test]
    fn projected_honest_trace_replays_all_539_two_round_edges() {
        let (public, witness) = fixture();
        let source = build_spend_trace_v4(&public, &witness).unwrap();
        assert_eq!(validate_spend_trace_v4(&public, &source), Ok(()));
        let projected = project_state_only_trace_v4(&source).unwrap();
        assert_eq!(STATE_ONLY_TRANSITION_COUNT, 49 * 11);
        assert_eq!(validate_state_only_projection(&source, &projected), Ok(()));

        for block in 0..PERMUTATION_COUNT {
            let base = block * BLOCK_ROWS;
            for lane in 0..POSEIDON2_WIDTH {
                assert_eq!(
                    projected.c1[lane][base + STATE_ONLY_FINAL_ROW_IN_BLOCK],
                    source.c1[SECOND_ROUND_OUTPUT_COLUMN_START + lane]
                        [base + ACTIVE_ROWS_PER_BLOCK - 1]
                );
                assert_eq!(
                    projected.c1[lane][base + STATE_ONLY_ABSORPTION_ROW_IN_BLOCK],
                    source.c1[lane][base + ABSORPTION_ROW_IN_BLOCK]
                );
                assert!((STATE_ONLY_PADDING_ROW_START_IN_BLOCK..BLOCK_ROWS)
                    .all(|local_row| projected.c1[lane][base + local_row] == M31::ZERO));
            }
        }
    }

    #[test]
    fn complete_layout_has_capacity_no_overlap_and_a_pinned_fingerprint() {
        let map = build_state_only_cell_map_v4().unwrap();
        let required = state_only_required_old_cells_v4();
        let mut occupied = vec![None; STATE_ONLY_C1_COLUMNS * TRACE_ROWS];
        for old in &required {
            let new = map.map(*old).unwrap();
            assert!(usize::from(new.row) < TRACE_ROWS);
            assert!(usize::from(new.column) < STATE_ONLY_C1_COLUMNS);
            let index = usize::from(new.row) * STATE_ONLY_C1_COLUMNS + usize::from(new.column);
            if let Some(previous) = occupied[index].replace(*old) {
                assert_eq!(
                    source_alias_target(previous).unwrap_or(previous),
                    source_alias_target(*old).unwrap_or(*old),
                    "non-alias collision at {new:?}"
                );
            }
            let local = usize::from(new.row) % BLOCK_ROWS;
            if usize::from(new.row) < STATE_ONLY_AUX_ROW_START {
                assert!(local <= STATE_ONLY_ABSORPTION_ROW_IN_BLOCK);
            }
        }
        assert!(map.aux_rows_used as usize <= STATE_ONLY_AUX_ROW_COUNT);
        assert!(map.aux_entries.iter().all(|(_, new)| {
            (STATE_ONLY_AUX_ROW_START..STATE_ONLY_AUX_ROW_END).contains(&usize::from(new.row))
        }));
        assert_eq!(STATE_ONLY_AUX_ROW_START, 784);
        assert_eq!(STATE_ONLY_AUX_ROW_END, 864);
        assert_eq!(STATE_ONLY_DIRECT_RANGE_ROW_START, 864);
        assert_eq!(STATE_ONLY_DIRECT_RANGE_ROW_END, 879);
        assert_eq!(
            (required.len(), map.aux_entries.len(), map.aux_rows_used),
            (2_434, 749, 79)
        );

        let fingerprint = state_only_layout_fingerprint_v4().unwrap();
        assert_eq!(fingerprint, PINNED_STATE_ONLY_LAYOUT_FINGERPRINT);
    }

    #[test]
    fn surviving_copy_layout_removes_exactly_490_links_and_preserves_every_endpoint_value() {
        let (public, witness) = fixture();
        let source = build_spend_trace_v4(&public, &witness).unwrap();
        let projected = project_state_only_trace_v4(&source).unwrap();
        let cell_map = build_state_only_cell_map_v4().unwrap();
        let old = copy_layout()
            .links
            .into_iter()
            .filter(|link| link.kind != CopyLinkKind::IntraPermutation)
            .collect::<Vec<_>>();
        let new = state_only_copy_layout_v4().unwrap();
        assert_eq!(592 - old.len(), 490);
        assert_eq!(old.len(), STATE_ONLY_SURVIVING_COPY_LINK_COUNT);
        assert_eq!(new.links.len(), STATE_ONLY_SURVIVING_COPY_LINK_COUNT);
        assert_eq!(new.source_link_ids, (490u16..592).collect::<Vec<_>>());

        let mut producer_arity = [0u8; TRACE_ROWS];
        let mut consumer_arity = [0u8; TRACE_ROWS];
        for (dense_id, (old, new)) in old.iter().zip(&new.links).enumerate() {
            assert_eq!(new.id, dense_id as u16);
            assert_eq!(new.tag, M31(dense_id as u32 + 1));
            assert_eq!(new.kind, old.kind);
            for (old_limb, new_limb) in old
                .producer
                .limbs
                .into_iter()
                .zip(new.producer.limbs)
                .chain(old.consumer.limbs.into_iter().zip(new.consumer.limbs))
            {
                match (old_limb, new_limb) {
                    (TupleLimb::Cell(old_cell), TupleLimb::Cell(new_cell)) => {
                        assert_eq!(cell_map.map(old_cell), Some(new_cell));
                    }
                    (TupleLimb::Zero, TupleLimb::Zero) => {}
                    pair => panic!("copy limb-shape mismatch: {pair:?}"),
                }
            }
            assert_eq!(
                source_tuple_value(&source, old.producer),
                tuple_value_state_only(&projected, new.producer)
            );
            assert_eq!(
                source_tuple_value(&source, old.consumer),
                tuple_value_state_only(&projected, new.consumer)
            );
            assert_eq!(
                tuple_value_state_only(&projected, new.producer),
                tuple_value_state_only(&projected, new.consumer)
            );
            for limb in new.producer.limbs {
                if let TupleLimb::Cell(cell) = limb {
                    assert_eq!(cell.row, new.producer_row);
                }
            }
            for limb in new.consumer.limbs {
                if let TupleLimb::Cell(cell) = limb {
                    assert_eq!(cell.row, new.consumer_row);
                }
            }
            producer_arity[usize::from(new.producer_row)] += 1;
            consumer_arity[usize::from(new.consumer_row)] += 1;
        }
        assert!(producer_arity.into_iter().all(|count| count <= 2));
        assert!(consumer_arity.into_iter().all(|count| count <= 2));
        assert_eq!(
            new.links
                .iter()
                .filter(|link| link.kind == CopyLinkKind::SpongeContinuation)
                .count(),
            25
        );
        assert_eq!(
            new.links
                .iter()
                .filter(|link| link.kind == CopyLinkKind::MerkleLevel)
                .count(),
            19
        );
        assert_eq!(
            new.links
                .iter()
                .filter(|link| link.kind == CopyLinkKind::SemanticIngress)
                .count(),
            6
        );
        assert_eq!(
            new.links
                .iter()
                .filter(|link| link.kind == CopyLinkKind::Absorption)
                .count(),
            49
        );
        assert_eq!(
            new.links
                .iter()
                .filter(|link| link.kind == CopyLinkKind::ValueReconstruction)
                .count(),
            3
        );
    }

    #[test]
    fn every_aux_dependency_and_direct_range_limb_has_independent_value_parity() {
        let (public, witness) = fixture();
        let source = build_spend_trace_v4(&public, &witness).unwrap();
        let projected = project_state_only_trace_v4(&source).unwrap();
        let map = build_state_only_cell_map_v4().unwrap();
        for old in state_only_required_old_cells_v4() {
            let new = map.map(old).unwrap();
            assert_eq!(
                source.c1[usize::from(old.column)][usize::from(old.row)],
                projected.c1[usize::from(new.column)][usize::from(new.row)]
            );
        }

        let new_aux = state_only_witness_aux_layout_v4().unwrap();
        for (limb, cell) in new_aux
            .input_value_limbs
            .into_iter()
            .chain(new_aux.output_value_limbs)
            .enumerate()
        {
            assert_eq!(usize::from(cell.row), STATE_ONLY_DIRECT_RANGE_ROWS[limb]);
            assert_eq!(
                usize::from(cell.column),
                STATE_ONLY_DIRECT_RANGE_RECONSTRUCTION_COLUMN
            );
            let value = projected.c1[usize::from(cell.column)][usize::from(cell.row)];
            let reconstructed = (0..STATE_ONLY_DIRECT_RANGE_BITS).fold(0u32, |sum, bit| {
                sum | (projected.c1[bit][usize::from(cell.row)].0 << bit)
            });
            assert_eq!(M31(reconstructed), value);
        }
        assert!(projected
            .c1
            .iter()
            .all(|column| column[STATE_ONLY_DIRECT_RANGE_ROW_END] == M31::ZERO));
    }

    #[test]
    fn projection_guard_has_transition_absorption_and_padding_teeth() {
        let (public, witness) = fixture();
        let source = build_spend_trace_v4(&public, &witness).unwrap();
        let projected = project_state_only_trace_v4(&source).unwrap();

        let mut transition = projected.clone();
        transition.c1[7][5] = transition.c1[7][5].add(M31::ONE);
        assert!(matches!(
            validate_state_only_projection(&source, &transition),
            Err(StateOnlyTraceError::ProjectionMismatch { .. })
                | Err(StateOnlyTraceError::SuccessorMismatch { .. })
        ));

        let mut absorption = projected.clone();
        absorption.c1[3][STATE_ONLY_ABSORPTION_ROW_IN_BLOCK] =
            absorption.c1[3][STATE_ONLY_ABSORPTION_ROW_IN_BLOCK].add(M31::ONE);
        assert!(matches!(
            validate_state_only_projection(&source, &absorption),
            Err(StateOnlyTraceError::FirstRoundMismatch { .. })
                | Err(StateOnlyTraceError::AbsorptionMismatch { .. })
        ));

        let mut padding = projected;
        padding.c1[9][STATE_ONLY_PADDING_ROW_START_IN_BLOCK] = M31::ONE;
        assert!(matches!(
            validate_state_only_projection(&source, &padding),
            Err(StateOnlyTraceError::NonZeroPadding { .. })
        ));
    }

    #[test]
    fn projection_guard_has_aux_direct_range_and_suffix_padding_teeth() {
        let (public, witness) = fixture();
        let source = build_spend_trace_v4(&public, &witness).unwrap();
        let projected = project_state_only_trace_v4(&source).unwrap();

        let map = build_state_only_cell_map_v4().unwrap();
        let mut aux = projected.clone();
        let (_, cell) = map.aux_entries[0];
        aux.c1[usize::from(cell.column)][usize::from(cell.row)] =
            aux.c1[usize::from(cell.column)][usize::from(cell.row)].add(M31::ONE);
        assert!(matches!(
            validate_state_only_projection(&source, &aux),
            Err(StateOnlyTraceError::AuxiliaryMismatch { .. })
        ));

        let mut direct_bit = projected.clone();
        direct_bit.c1[0][STATE_ONLY_DIRECT_RANGE_ROW_START] = M31(2);
        assert!(matches!(
            validate_state_only_projection(&source, &direct_bit),
            Err(StateOnlyTraceError::DirectRangeBitMismatch { .. })
        ));

        let mut suffix = projected;
        suffix.c1[15][STATE_ONLY_DIRECT_RANGE_ROW_END] = M31::ONE;
        assert_eq!(validate_state_only_projection(&source, &suffix), Ok(()));
    }

    #[test]
    fn randomized_mle_successor_evaluation_matches_the_composed_representative() {
        let mut random = 0x6a09_e667_f3bc_c909u64;
        let column = (0..TRACE_ROWS)
            .map(|_| M31(next_u32(&mut random)))
            .collect::<Vec<_>>();

        // On the cube, composition with the successor point is exactly the
        // successor row lookup for arbitrary table values.
        for _ in 0..128 {
            let row = next_u32(&mut random) as usize % TRACE_ROWS;
            let successor = binary_successor_point(&boolean_point(row));
            assert_eq!(
                multilinear_evaluate(&column, &successor).unwrap(),
                QM31::ONE.mul_m31(column[(row + 1) % TRACE_ROWS])
            );
        }

        // Off-domain, validate f(succ(z)) against a dense independent MLE
        // walk.  It is intentionally not equated with MLE(f°succ)(z).
        for _ in 0..8 {
            let point = core::array::from_fn(|_| random_qm31(&mut random));
            let successor = binary_successor_point(&point);
            assert_eq!(
                multilinear_evaluate(&column, &successor).unwrap(),
                dense_mle(&column, &successor)
            );
        }
    }

    #[test]
    fn degree_inventory_covers_successor_and_two_round_branches() {
        // Big-endian coordinate i influences successor coordinates 0..=i,
        // so its multiplicity in a composed multilinear opening is i+1.
        let dependency_counts = core::array::from_fn::<_, 10, _>(|coordinate| coordinate + 1);
        assert_eq!(dependency_counts.into_iter().max(), Some(10));
        assert_eq!(
            STATE_ONLY_DEGREE_BOUNDS.successor_opening_individual_degree,
            10
        );
        assert!(
            STATE_ONLY_DEGREE_BOUNDS.successor_opening_individual_degree
                <= STATE_ONLY_DEGREE_BOUNDS.two_round_transition_individual_degree
        );
        assert_eq!(
            STATE_ONLY_DEGREE_BOUNDS.active_gated_individual_degree,
            STATE_ONLY_DEGREE_BOUNDS.two_round_transition_individual_degree + 1
        );
        assert_eq!(
            STATE_ONLY_DEGREE_BOUNDS.zerocheck_individual_degree,
            STATE_ONLY_DEGREE_BOUNDS.active_gated_individual_degree + 1
        );
    }

    #[test]
    fn relation_free_mask_registry_is_column_major_complete_and_pinned() {
        let cells = state_only_relation_free_mask_cells_v4().unwrap();
        assert_eq!(cells.len(), 5_374);
        assert!(cells
            .windows(2)
            .all(|pair| (pair[0].column, pair[0].row) < (pair[1].column, pair[1].row)));
        let counts: [usize; STATE_ONLY_C1_COLUMNS] = core::array::from_fn(|column| {
            cells
                .iter()
                .filter(|cell| usize::from(cell.column) == column)
                .count()
        });
        assert_eq!(
            counts,
            [316, 316, 316, 316, 316, 316, 316, 316, 333, 352, 355, 359, 360, 361, 363, 363,]
        );
        assert_eq!(
            state_only_relation_free_mask_fingerprint_v4().unwrap(),
            PINNED_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT
        );

        let map = build_state_only_cell_map_v4().unwrap();
        for old in state_only_required_old_cells_v4() {
            assert!(!cells.contains(&map.map(old).unwrap()));
        }
        for block in 0..PERMUTATION_COUNT {
            for local in 0..STATE_ONLY_PADDING_ROW_START_IN_BLOCK {
                assert!(
                    (0..STATE_ONLY_C1_COLUMNS).all(|column| !cells.contains(&TraceCell {
                        row: (block * BLOCK_ROWS + local) as u16,
                        column: column as u8,
                    }))
                );
            }
            assert!(
                (0..STATE_ONLY_C1_COLUMNS).all(|column| cells.contains(&TraceCell {
                    row: (block * BLOCK_ROWS + STATE_ONLY_PADDING_ROW_START_IN_BLOCK) as u16,
                    column: column as u8,
                }))
            );
        }
    }
}
