//! Atomic-v3 copy and semantic registry generator.
//!
//! This is a production-neutral replacement surface for the frozen v4
//! routing constants. It does not modify or repin those constants.

use alloc::vec;
use alloc::vec::Vec;

use aspis_core::field::{M31, QM31};
use aspis_core::state_only_hiding::STATE_ONLY_HIDING_SELECTED_TOTAL_GENERATOR_WIDTH;

use crate::atomic_state_only_trace::{
    AtomicStateOnlyTraceV3, ATOMIC_STATE_ONLY_INPUT_PATH_BLOCK_START,
    ATOMIC_STATE_ONLY_INPUT_ROOT_BLOCK, ATOMIC_STATE_ONLY_OUTPUT_PATH_BLOCK_START,
    ATOMIC_STATE_ONLY_OUTPUT_ROOT_BLOCK,
};
use crate::atomic_statement::{AtomicPaymentStatementV4, ATOMIC_PAYMENT_TREE_DEPTH};
use crate::logup::{
    build_copy_logup_helper, compress_tagged_tuple, verify_copy_logup_constraints, CopyLogUpRow,
};
use crate::poseidon2::{DIGEST_ELEMS, MERKLE_NODE_COMPRESSION_V3_TWEAK, POSEIDON2_WIDTH};
use crate::state_only_trace::{
    build_state_only_cell_map_v4, state_only_copy_layout_v4,
    state_only_relation_free_mask_cells_v4, state_only_required_old_cells_v4, StateOnlyLayoutError,
    StateOnlyTraceFoundation, STATE_ONLY_AUX_ROW_COUNT, STATE_ONLY_AUX_ROW_START,
    STATE_ONLY_C1_COLUMNS,
};
use crate::trace_v4::{
    copy_layout, merkle_boundary_layout, CopyLinkKind, CopyTuple, TraceCell, TupleLimb, BLOCK_ROWS,
};

pub const ATOMIC_STATE_ONLY_BASE_SEMANTIC_LANES: usize = 77;
pub const ATOMIC_STATE_ONLY_COPY_LANES: usize = 1;
pub const ATOMIC_STATE_ONLY_PACKED_BASE_LANES: usize =
    ATOMIC_STATE_ONLY_BASE_SEMANTIC_LANES.div_ceil(4);
pub const ATOMIC_STATE_ONLY_RANDOMIZED_SEMANTIC_LANES: usize =
    ATOMIC_STATE_ONLY_PACKED_BASE_LANES + ATOMIC_STATE_ONLY_COPY_LANES;
pub const ATOMIC_STATE_ONLY_POSEIDON_LANES: usize = 4;
pub const ATOMIC_STATE_ONLY_THETA_LANES: usize =
    ATOMIC_STATE_ONLY_POSEIDON_LANES + ATOMIC_STATE_ONLY_RANDOMIZED_SEMANTIC_LANES;
pub const ATOMIC_STATE_ONLY_THETA_COLLISION_DEGREE: usize = ATOMIC_STATE_ONLY_THETA_LANES - 1;
pub const ATOMIC_STATE_ONLY_ZEROCHECK_DEGREE: usize = 27;
pub const ATOMIC_STATE_ONLY_TERMINAL_POINTS: usize = 3;
pub const ATOMIC_STATE_ONLY_SELECTED_PCS_WIDTH: usize =
    STATE_ONLY_HIDING_SELECTED_TOTAL_GENERATOR_WIDTH;

const _: () = assert!(ATOMIC_STATE_ONLY_PACKED_BASE_LANES == 20);
const _: () = assert!(ATOMIC_STATE_ONLY_RANDOMIZED_SEMANTIC_LANES == 21);
const _: () = assert!(ATOMIC_STATE_ONLY_THETA_LANES == 25);
const _: () = assert!(ATOMIC_STATE_ONLY_SELECTED_PCS_WIDTH == 28);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AtomicPointTransformV3 {
    Z,
    Succ,
    Xor12,
}

pub const fn atomic_state_only_required_point_transforms_v3() -> [AtomicPointTransformV3; 3] {
    [
        AtomicPointTransformV3::Z,
        AtomicPointTransformV3::Succ,
        AtomicPointTransformV3::Xor12,
    ]
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AtomicTupleLimbV3 {
    Zero,
    Constant(M31),
    AffineCell {
        cell: TraceCell,
        scale: M31,
        offset: M31,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AtomicCopyTupleV3 {
    pub row: u16,
    pub limbs: [AtomicTupleLimbV3; POSEIDON2_WIDTH],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AtomicCopyLinkKindV3 {
    Retained(CopyLinkKind),
    PathCurrent { output: bool, level: u8 },
    PathSelect { output: bool, level: u8, item: u8 },
    PathBitAlias { level: u8, hop: u8 },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AtomicCopyLinkV3 {
    pub id: u16,
    /// Selection links for the same path/level intentionally share a tag;
    /// their two-item multiset implements the private left/right swap.
    pub tag: M31,
    pub kind: AtomicCopyLinkKindV3,
    pub producer: AtomicCopyTupleV3,
    pub consumer: AtomicCopyTupleV3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AtomicPathAuxLevelV3 {
    pub level: u8,
    pub input_bit: TraceCell,
    pub input_current: [TraceCell; DIGEST_ELEMS],
    pub output_bit: TraceCell,
    pub output_current: [TraceCell; DIGEST_ELEMS],
    pub sibling_bit: TraceCell,
    pub sibling: [TraceCell; DIGEST_ELEMS],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicStateOnlyRegistryV3 {
    pub links: Vec<AtomicCopyLinkV3>,
    pub path_aux: [AtomicPathAuxLevelV3; ATOMIC_PAYMENT_TREE_DEPTH],
    pub retained_links: usize,
    pub path_current_links: usize,
    pub path_selection_links: usize,
    pub path_bit_alias_links: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AtomicStateOnlyRegistryStatsV3 {
    /// Number of producer/consumer terms in the copy multiset.
    pub copy_terms_m: usize,
    pub unique_tag_groups: usize,
    pub endpoint_active_rows: usize,
    pub maximum_producers_per_row: usize,
    pub maximum_consumers_per_row: usize,
    pub tuple_patterns: usize,
    /// Sum of the M31 ranks of every high-by-low selector-routing matrix.
    pub tensor_routing_rank: usize,
    pub auxiliary_cells_used: usize,
    pub auxiliary_cells_capacity: usize,
    pub auxiliary_rows_high_water: usize,
    pub base_semantic_lanes: usize,
    pub randomized_semantic_lanes: usize,
    pub theta_lanes: usize,
    pub theta_collision_degree: usize,
    pub zerocheck_degree: usize,
    pub terminal_points: usize,
    pub selected_pcs_width: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AtomicStateOnlyRegistryErrorV3 {
    Layout,
    AuxRowMismatch { level: u8 },
    NonRowLocalTuple { link: u16 },
    EndpointCapacity { row: u16 },
    CopyImbalance,
    PublicRootMismatch,
}

fn cell(cell: TraceCell) -> AtomicTupleLimbV3 {
    AtomicTupleLimbV3::AffineCell {
        cell,
        scale: M31::ONE,
        offset: M31::ZERO,
    }
}

fn affine_cell(cell: TraceCell, scale: M31, offset: M31) -> AtomicTupleLimbV3 {
    AtomicTupleLimbV3::AffineCell {
        cell,
        scale,
        offset,
    }
}

fn digest_tuple(cells: [TraceCell; DIGEST_ELEMS]) -> AtomicCopyTupleV3 {
    let mut limbs = [AtomicTupleLimbV3::Zero; POSEIDON2_WIDTH];
    for (limb, source) in limbs.iter_mut().zip(cells) {
        *limb = cell(source);
    }
    AtomicCopyTupleV3 {
        row: cells[0].row,
        limbs,
    }
}

fn scalar_tuple(limb: AtomicTupleLimbV3, row: u16) -> AtomicCopyTupleV3 {
    let mut limbs = [AtomicTupleLimbV3::Zero; POSEIDON2_WIDTH];
    limbs[0] = limb;
    AtomicCopyTupleV3 { row, limbs }
}

fn selected_digest_tuple(
    selector: AtomicTupleLimbV3,
    cells: [TraceCell; DIGEST_ELEMS],
    last_offset: M31,
) -> AtomicCopyTupleV3 {
    let mut limbs = [AtomicTupleLimbV3::Zero; POSEIDON2_WIDTH];
    limbs[0] = selector;
    for limb in 0..DIGEST_ELEMS {
        limbs[1 + limb] = affine_cell(
            cells[limb],
            M31::ONE,
            if limb + 1 == DIGEST_ELEMS {
                last_offset
            } else {
                M31::ZERO
            },
        );
    }
    AtomicCopyTupleV3 {
        row: cells[0].row,
        limbs,
    }
}

fn tuple_from_generic(tuple: CopyTuple) -> AtomicCopyTupleV3 {
    let row = tuple
        .limbs
        .iter()
        .find_map(|limb| match limb {
            TupleLimb::Cell(cell) => Some(cell.row),
            TupleLimb::Zero => None,
        })
        .unwrap_or(0);
    AtomicCopyTupleV3 {
        row,
        limbs: tuple.limbs.map(|limb| match limb {
            TupleLimb::Cell(source) => cell(source),
            TupleLimb::Zero => AtomicTupleLimbV3::Zero,
        }),
    }
}

fn tuple_row(tuple: AtomicCopyTupleV3, link: u16) -> Result<u16, AtomicStateOnlyRegistryErrorV3> {
    for limb in tuple.limbs {
        if let AtomicTupleLimbV3::AffineCell { cell, .. } = limb {
            if tuple.row != cell.row {
                return Err(AtomicStateOnlyRegistryErrorV3::NonRowLocalTuple { link });
            }
        }
    }
    Ok(tuple.row)
}

fn old_boundary_cells() -> Result<Vec<TraceCell>, AtomicStateOnlyRegistryErrorV3> {
    let map = build_state_only_cell_map_v4().map_err(|_| AtomicStateOnlyRegistryErrorV3::Layout)?;
    let mut cells = Vec::new();
    for boundary in merkle_boundary_layout() {
        cells.push(
            map.map(boundary.path_bit)
                .ok_or(AtomicStateOnlyRegistryErrorV3::Layout)?,
        );
        for source in boundary
            .current
            .into_iter()
            .chain(boundary.left)
            .chain(boundary.right)
            .chain(boundary.sibling)
        {
            cells.push(
                map.map(source)
                    .ok_or(AtomicStateOnlyRegistryErrorV3::Layout)?,
            );
        }
    }
    cells.sort_unstable_by_key(|cell| (cell.row, cell.column));
    cells.dedup();
    Ok(cells)
}

fn allocate_atomic_path_component(
    occupied: &mut Vec<TraceCell>,
    producer_arity: &mut [u8; 1024],
    consumer_arity: &mut [u8; 1024],
    consumer_endpoints: u8,
) -> Result<(TraceCell, [TraceCell; DIGEST_ELEMS]), AtomicStateOnlyRegistryErrorV3> {
    let (row, cells) = (STATE_ONLY_AUX_ROW_START
        ..STATE_ONLY_AUX_ROW_START + STATE_ONLY_AUX_ROW_COUNT)
        .find_map(|row| {
            if producer_arity[row] != 0
                || consumer_arity[row].saturating_add(consumer_endpoints) > 2
            {
                return None;
            }
            let free = (0..STATE_ONLY_C1_COLUMNS)
                .map(|column| TraceCell {
                    row: row as u16,
                    column: column as u8,
                })
                .filter(|cell| !occupied.contains(cell))
                .take(1 + DIGEST_ELEMS)
                .collect::<Vec<_>>();
            (free.len() == 1 + DIGEST_ELEMS).then_some((row, free))
        })
        .ok_or(AtomicStateOnlyRegistryErrorV3::Layout)?;
    let bit = cells[0];
    let digest = core::array::from_fn(|limb| cells[1 + limb]);
    occupied.extend(cells);
    producer_arity[row] += 2;
    consumer_arity[row] += consumer_endpoints;
    Ok((bit, digest))
}

pub fn atomic_state_only_path_aux_layout_v3(
) -> Result<[AtomicPathAuxLevelV3; ATOMIC_PAYMENT_TREE_DEPTH], AtomicStateOnlyRegistryErrorV3> {
    let map = build_state_only_cell_map_v4().map_err(|_| AtomicStateOnlyRegistryErrorV3::Layout)?;
    let removed = old_boundary_cells()?;
    let mut occupied = state_only_required_old_cells_v4()
        .into_iter()
        .filter_map(|old| map.map(old))
        .filter(|cell| {
            usize::from(cell.row) >= STATE_ONLY_AUX_ROW_START
                && usize::from(cell.row) < STATE_ONLY_AUX_ROW_START + STATE_ONLY_AUX_ROW_COUNT
                && !removed.contains(cell)
        })
        .collect::<Vec<_>>();
    occupied.sort_unstable_by_key(|cell| (cell.row, cell.column));
    occupied.dedup();

    // Reserve endpoint capacity already consumed by retained non-path links.
    let source = copy_layout();
    let old_by_id = source.links;
    let state_only =
        state_only_copy_layout_v4().map_err(|_| AtomicStateOnlyRegistryErrorV3::Layout)?;
    let mut producer_arity = [0u8; 1024];
    let mut consumer_arity = [0u8; 1024];
    for (link, source_id) in state_only.links.into_iter().zip(state_only.source_link_ids) {
        let old = old_by_id
            .iter()
            .find(|candidate| candidate.id == source_id)
            .ok_or(AtomicStateOnlyRegistryErrorV3::Layout)?;
        if old.kind == CopyLinkKind::MerkleLevel
            || tuple_touches_replaced_path(old.producer)
            || tuple_touches_replaced_path(old.consumer)
        {
            continue;
        }
        producer_arity[usize::from(link.producer_row)] += 1;
        consumer_arity[usize::from(link.consumer_row)] += 1;
    }

    let mut layouts = Vec::with_capacity(ATOMIC_PAYMENT_TREE_DEPTH);
    for level in 0..ATOMIC_PAYMENT_TREE_DEPTH {
        let (input_bit, input_current) = allocate_atomic_path_component(
            &mut occupied,
            &mut producer_arity,
            &mut consumer_arity,
            1,
        )?;
        let (output_bit, output_current) = allocate_atomic_path_component(
            &mut occupied,
            &mut producer_arity,
            &mut consumer_arity,
            2,
        )?;
        let (sibling_bit, sibling) = allocate_atomic_path_component(
            &mut occupied,
            &mut producer_arity,
            &mut consumer_arity,
            1,
        )?;
        layouts.push(AtomicPathAuxLevelV3 {
            level: level as u8,
            input_bit,
            input_current,
            output_bit,
            output_current,
            sibling_bit,
            sibling,
        });
    }
    layouts
        .try_into()
        .map_err(|_| AtomicStateOnlyRegistryErrorV3::Layout)
}

fn tuple_touches_replaced_path(tuple: CopyTuple) -> bool {
    tuple.limbs.into_iter().any(|limb| {
        let TupleLimb::Cell(cell) = limb else {
            return false;
        };
        let row = usize::from(cell.row);
        row < 49 * BLOCK_ROWS && (4..=43).contains(&(row / BLOCK_ROWS))
    })
}

fn trace_digest_cells(block: usize, local_row: usize) -> [TraceCell; DIGEST_ELEMS] {
    core::array::from_fn(|limb| TraceCell {
        row: (block * BLOCK_ROWS + local_row) as u16,
        column: limb as u8,
    })
}

fn path_left_cells(block: usize) -> [TraceCell; DIGEST_ELEMS] {
    trace_digest_cells(
        block,
        crate::state_only_trace::STATE_ONLY_ABSORPTION_ROW_IN_BLOCK,
    )
}

fn path_right_cells(block: usize) -> [TraceCell; DIGEST_ELEMS] {
    core::array::from_fn(|limb| TraceCell {
        row: (block * BLOCK_ROWS) as u16,
        column: (DIGEST_ELEMS + limb) as u8,
    })
}

pub fn build_atomic_state_only_registry_v3(
) -> Result<AtomicStateOnlyRegistryV3, AtomicStateOnlyRegistryErrorV3> {
    let path_aux = atomic_state_only_path_aux_layout_v3()?;
    let source = copy_layout();
    let old_by_id = source.links;
    let state_only =
        state_only_copy_layout_v4().map_err(|_| AtomicStateOnlyRegistryErrorV3::Layout)?;
    let mut links = Vec::new();
    let mut next_tag = 1u32;

    for (link, source_id) in state_only.links.into_iter().zip(state_only.source_link_ids) {
        let old = old_by_id
            .iter()
            .find(|candidate| candidate.id == source_id)
            .ok_or(AtomicStateOnlyRegistryErrorV3::Layout)?;
        if old.kind == CopyLinkKind::MerkleLevel
            || tuple_touches_replaced_path(old.producer)
            || tuple_touches_replaced_path(old.consumer)
        {
            continue;
        }
        let id = links.len() as u16;
        links.push(AtomicCopyLinkV3 {
            id,
            tag: M31(next_tag),
            kind: AtomicCopyLinkKindV3::Retained(link.kind),
            producer: tuple_from_generic(link.producer),
            consumer: tuple_from_generic(link.consumer),
        });
        next_tag += 1;
    }
    let retained_links = links.len();

    let mut path_current_links = 0usize;
    let mut path_selection_links = 0usize;
    let mut path_bit_alias_links = 0usize;
    for level in 0..ATOMIC_PAYMENT_TREE_DEPTH {
        let aux = path_aux[level];
        for output in [false, true] {
            let block = if output {
                ATOMIC_STATE_ONLY_OUTPUT_PATH_BLOCK_START + level
            } else {
                ATOMIC_STATE_ONLY_INPUT_PATH_BLOCK_START + level
            };
            let previous_block = if level == 0 {
                if output {
                    48
                } else {
                    3
                }
            } else {
                block - 1
            };
            let current_cells = if output {
                aux.output_current
            } else {
                aux.input_current
            };
            let bit_cell = if output {
                aux.output_bit
            } else {
                aux.input_bit
            };

            links.push(AtomicCopyLinkV3 {
                id: links.len() as u16,
                tag: M31(next_tag),
                kind: AtomicCopyLinkKindV3::PathCurrent {
                    output,
                    level: level as u8,
                },
                producer: digest_tuple(trace_digest_cells(
                    previous_block,
                    crate::state_only_trace::STATE_ONLY_FINAL_ROW_IN_BLOCK,
                )),
                consumer: digest_tuple(current_cells),
            });
            next_tag += 1;
            path_current_links += 1;

            // Both links intentionally share one tag. At bit zero the
            // nominal pairs match; at bit one the two consumer matches swap.
            let selection_tag = M31(next_tag);
            next_tag += 1;
            links.push(AtomicCopyLinkV3 {
                id: links.len() as u16,
                tag: selection_tag,
                kind: AtomicCopyLinkKindV3::PathSelect {
                    output,
                    level: level as u8,
                    item: 0,
                },
                producer: selected_digest_tuple(cell(bit_cell), current_cells, M31::ZERO),
                consumer: selected_digest_tuple(
                    AtomicTupleLimbV3::Constant(M31::ZERO),
                    path_left_cells(block),
                    M31::ZERO,
                ),
            });
            links.push(AtomicCopyLinkV3 {
                id: links.len() as u16,
                tag: selection_tag,
                kind: AtomicCopyLinkKindV3::PathSelect {
                    output,
                    level: level as u8,
                    item: 1,
                },
                producer: selected_digest_tuple(
                    affine_cell(aux.sibling_bit, M31::ZERO.sub(M31::ONE), M31::ONE),
                    aux.sibling,
                    M31::ZERO,
                ),
                consumer: selected_digest_tuple(
                    AtomicTupleLimbV3::Constant(M31::ONE),
                    path_right_cells(block),
                    M31::ZERO.sub(MERKLE_NODE_COMPRESSION_V3_TWEAK),
                ),
            });
            path_selection_links += 2;
        }

        for (hop, producer, consumer) in [
            (0u8, aux.input_bit, aux.output_bit),
            (1u8, aux.output_bit, aux.sibling_bit),
        ] {
            links.push(AtomicCopyLinkV3 {
                id: links.len() as u16,
                tag: M31(next_tag),
                kind: AtomicCopyLinkKindV3::PathBitAlias {
                    level: level as u8,
                    hop,
                },
                producer: scalar_tuple(cell(producer), producer.row),
                consumer: scalar_tuple(cell(consumer), consumer.row),
            });
            next_tag += 1;
            path_bit_alias_links += 1;
        }
    }

    let registry = AtomicStateOnlyRegistryV3 {
        links,
        path_aux,
        retained_links,
        path_current_links,
        path_selection_links,
        path_bit_alias_links,
    };
    endpoint_slots(&registry)?;
    Ok(registry)
}

#[derive(Clone, Copy)]
struct EndpointSlots {
    producer: [u8; 1024],
    consumer: [u8; 1024],
}

fn endpoint_slots(
    registry: &AtomicStateOnlyRegistryV3,
) -> Result<EndpointSlots, AtomicStateOnlyRegistryErrorV3> {
    let mut slots = EndpointSlots {
        producer: [0; 1024],
        consumer: [0; 1024],
    };
    for link in &registry.links {
        for (tuple, counts) in [
            (link.producer, &mut slots.producer),
            (link.consumer, &mut slots.consumer),
        ] {
            let row = usize::from(tuple_row(tuple, link.id)?);
            if counts[row] >= 2 {
                return Err(AtomicStateOnlyRegistryErrorV3::EndpointCapacity { row: row as u16 });
            }
            counts[row] += 1;
        }
    }
    Ok(slots)
}

fn tuple_value(
    trace: &StateOnlyTraceFoundation,
    tuple: AtomicCopyTupleV3,
) -> [M31; POSEIDON2_WIDTH] {
    tuple.limbs.map(|limb| match limb {
        AtomicTupleLimbV3::Zero => M31::ZERO,
        AtomicTupleLimbV3::Constant(value) => value,
        AtomicTupleLimbV3::AffineCell {
            cell,
            scale,
            offset,
        } => trace.c1[usize::from(cell.column)][usize::from(cell.row)]
            .mul(scale)
            .add(offset),
    })
}

pub fn atomic_state_only_copy_rows_v3(
    registry: &AtomicStateOnlyRegistryV3,
    trace: &AtomicStateOnlyTraceV3,
    lambda: QM31,
) -> Result<Vec<CopyLogUpRow>, AtomicStateOnlyRegistryErrorV3> {
    atomic_state_only_copy_rows_from_foundation_v3(registry, &trace.trace, lambda)
}

/// Build the atomic copy rows from the committed foundation alone.  The
/// metadata-rich `AtomicStateOnlyTraceV3` wrapper is intentionally not needed
/// after relation-free masks have been applied to the committed columns.
pub fn atomic_state_only_copy_rows_from_foundation_v3(
    registry: &AtomicStateOnlyRegistryV3,
    trace: &StateOnlyTraceFoundation,
    lambda: QM31,
) -> Result<Vec<CopyLogUpRow>, AtomicStateOnlyRegistryErrorV3> {
    endpoint_slots(registry)?;
    let empty = CopyLogUpRow {
        producer_values: [QM31::ZERO; 2],
        producer_weights: [M31::ZERO; 2],
        consumer_values: [QM31::ZERO; 2],
        consumer_weights: [M31::ZERO; 2],
    };
    let mut rows = vec![empty; 1024];
    for link in &registry.links {
        for (tuple, producer) in [(link.producer, true), (link.consumer, false)] {
            let row_index = usize::from(tuple_row(tuple, link.id)?);
            let row = &mut rows[row_index];
            let (values, weights) = if producer {
                (&mut row.producer_values, &mut row.producer_weights)
            } else {
                (&mut row.consumer_values, &mut row.consumer_weights)
            };
            let slot = weights
                .iter()
                .position(|weight| *weight == M31::ZERO)
                .ok_or(AtomicStateOnlyRegistryErrorV3::EndpointCapacity {
                    row: tuple_row(tuple, link.id)?,
                })?;
            values[slot] = compress_tagged_tuple(link.tag, &tuple_value(trace, tuple), lambda);
            weights[slot] = M31::ONE;
        }
    }
    Ok(rows)
}

/// Build the unique atomic-v3 LogUp helper bound by `lambda,chi`.
pub fn build_atomic_state_only_copy_helper_v3(
    trace: &StateOnlyTraceFoundation,
    lambda: QM31,
    chi: QM31,
) -> Result<Vec<QM31>, AtomicStateOnlyRegistryErrorV3> {
    let registry = build_atomic_state_only_registry_v3()?;
    let rows = atomic_state_only_copy_rows_from_foundation_v3(&registry, trace, lambda)?;
    build_copy_logup_helper(&rows, chi).map_err(|_| AtomicStateOnlyRegistryErrorV3::CopyImbalance)
}

/// Conservative exact mask inventory for atomic-v3.  Start from the already
/// audited state-only relation-free cells, then remove every newly introduced
/// atomic copy endpoint.  Retaining now-unused legacy exclusions costs mask
/// entropy but cannot make a constrained cell maskable.
pub fn atomic_state_only_relation_free_mask_cells_v3(
) -> Result<Vec<TraceCell>, AtomicStateOnlyRegistryErrorV3> {
    let registry = build_atomic_state_only_registry_v3()?;
    let mut occupied = Vec::new();
    for link in registry.links {
        for tuple in [link.producer, link.consumer] {
            for limb in tuple.limbs {
                if let AtomicTupleLimbV3::AffineCell { cell, .. } = limb {
                    occupied.push(cell);
                }
            }
        }
    }
    occupied.sort_unstable_by_key(|cell| (cell.row, cell.column));
    occupied.dedup();
    let mut cells = state_only_relation_free_mask_cells_v4()
        .map_err(|_| AtomicStateOnlyRegistryErrorV3::Layout)?;
    cells.retain(|cell| {
        !occupied
            .binary_search_by_key(&(cell.row, cell.column), |candidate| {
                (candidate.row, candidate.column)
            })
            .is_ok()
    });
    Ok(cells)
}

pub fn atomic_state_only_relation_free_mask_fingerprint_v3(
) -> Result<u64, AtomicStateOnlyRegistryErrorV3> {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    for cell in atomic_state_only_relation_free_mask_cells_v3()? {
        for byte in cell.row.to_le_bytes().into_iter().chain([cell.column]) {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    Ok(hash)
}

pub fn verify_atomic_state_only_copy_registry_v3(
    registry: &AtomicStateOnlyRegistryV3,
    trace: &AtomicStateOnlyTraceV3,
    lambda: QM31,
    chi: QM31,
) -> Result<(), AtomicStateOnlyRegistryErrorV3> {
    let rows = atomic_state_only_copy_rows_v3(registry, trace, lambda)?;
    let helper = build_copy_logup_helper(&rows, chi)
        .map_err(|_| AtomicStateOnlyRegistryErrorV3::CopyImbalance)?;
    verify_copy_logup_constraints(&rows, &helper, chi)
        .map_err(|_| AtomicStateOnlyRegistryErrorV3::CopyImbalance)
}

pub fn verify_atomic_state_only_public_roots_v3(
    statement: &AtomicPaymentStatementV4,
    trace: &AtomicStateOnlyTraceV3,
) -> Result<(), AtomicStateOnlyRegistryErrorV3> {
    let digest = |block: usize| {
        let row = block * BLOCK_ROWS + crate::state_only_trace::STATE_ONLY_FINAL_ROW_IN_BLOCK;
        core::array::from_fn(|limb| trace.trace.c1[limb][row])
    };
    if digest(ATOMIC_STATE_ONLY_INPUT_ROOT_BLOCK) != statement.spend.anchor
        || digest(ATOMIC_STATE_ONLY_OUTPUT_ROOT_BLOCK) != statement.output_anchor
    {
        return Err(AtomicStateOnlyRegistryErrorV3::PublicRootMismatch);
    }
    Ok(())
}

fn pattern_signature(tuple: AtomicCopyTupleV3) -> [u32; 4 * POSEIDON2_WIDTH] {
    let mut signature = [0u32; 4 * POSEIDON2_WIDTH];
    for (index, limb) in tuple.limbs.into_iter().enumerate() {
        let base = 4 * index;
        match limb {
            AtomicTupleLimbV3::Zero => {}
            AtomicTupleLimbV3::Constant(value) => {
                signature[base] = 1;
                signature[base + 3] = value.0;
            }
            AtomicTupleLimbV3::AffineCell {
                cell,
                scale,
                offset,
            } => {
                signature[base] = 2;
                signature[base + 1] = u32::from(cell.column);
                signature[base + 2] = scale.0;
                signature[base + 3] = offset.0;
            }
        }
    }
    signature
}

fn rank_m31(mut matrix: Vec<Vec<M31>>) -> usize {
    let rows = matrix.len();
    let columns = matrix.first().map_or(0, Vec::len);
    let mut rank = 0usize;
    for column in 0..columns {
        let Some(pivot) = (rank..rows).find(|&row| matrix[row][column] != M31::ZERO) else {
            continue;
        };
        matrix.swap(rank, pivot);
        let inverse = matrix[rank][column].inv();
        for value in &mut matrix[rank][column..] {
            *value = value.mul(inverse);
        }
        let tail = matrix[rank][column..].to_vec();
        for row in rank + 1..rows {
            let scale = matrix[row][column];
            if scale == M31::ZERO {
                continue;
            }
            for (value, pivot_value) in matrix[row][column..].iter_mut().zip(&tail) {
                *value = value.sub(scale.mul(*pivot_value));
            }
        }
        rank += 1;
        if rank == rows {
            break;
        }
    }
    rank
}

fn atomic_routing_projected_index(row: usize, bit_mask: u16) -> usize {
    let mut output = 0usize;
    for bit in (0..10).rev() {
        if bit_mask & (1 << bit) != 0 {
            output = (output << 1) | ((row >> bit) & 1);
        }
    }
    output
}

pub fn atomic_state_only_registry_stats_v3(
    registry: &AtomicStateOnlyRegistryV3,
) -> Result<AtomicStateOnlyRegistryStatsV3, AtomicStateOnlyRegistryErrorV3> {
    let slots = endpoint_slots(registry)?;
    let endpoint_active_rows = (0..1024)
        .filter(|row| slots.producer[*row] != 0 || slots.consumer[*row] != 0)
        .count();
    let maximum_producers_per_row = slots.producer.into_iter().max().unwrap_or(0) as usize;
    let maximum_consumers_per_row = slots.consumer.into_iter().max().unwrap_or(0) as usize;

    let mut patterns = Vec::new();
    for link in &registry.links {
        for tuple in [link.producer, link.consumer] {
            let signature = pattern_signature(tuple);
            if !patterns.contains(&signature) {
                patterns.push(signature);
            }
        }
    }
    // Exhaustive partition search pins top row bits 9..6 as the 16-entry
    // factor and bottom bits 5..0 as the 64-entry factor.
    const LOW_ROW_BITS: u16 = 0x03c0;
    const HIGH_ROW_BITS: u16 = (!LOW_ROW_BITS) & 0x03ff;
    let matrix_count = 4 * (2 + patterns.len());
    let mut matrices = vec![vec![vec![M31::ZERO; 16]; 64]; matrix_count];
    let mut producer_slots = [0u8; 1024];
    let mut consumer_slots = [0u8; 1024];
    for link in &registry.links {
        for (tuple, side, counts) in [
            (link.producer, 0usize, &mut producer_slots),
            (link.consumer, 2usize, &mut consumer_slots),
        ] {
            let row = usize::from(tuple_row(tuple, link.id)?);
            let slot = side + usize::from(counts[row]);
            counts[row] += 1;
            let high = atomic_routing_projected_index(row, HIGH_ROW_BITS);
            let low = atomic_routing_projected_index(row, LOW_ROW_BITS);
            let base = slot * (2 + patterns.len());
            matrices[base][high][low] = matrices[base][high][low].add(M31::ONE);
            matrices[base + 1][high][low] = matrices[base + 1][high][low].add(link.tag);
            let pattern = patterns
                .iter()
                .position(|candidate| *candidate == pattern_signature(tuple))
                .unwrap();
            matrices[base + 2 + pattern][high][low] =
                matrices[base + 2 + pattern][high][low].add(M31::ONE);
        }
    }
    let tensor_routing_rank = matrices.into_iter().map(rank_m31).sum();

    let map = build_state_only_cell_map_v4().map_err(|_| AtomicStateOnlyRegistryErrorV3::Layout)?;
    let removed = old_boundary_cells()?;
    let mut aux_cells = state_only_required_old_cells_v4()
        .into_iter()
        .filter_map(|old| map.map(old))
        .filter(|cell| {
            usize::from(cell.row) >= STATE_ONLY_AUX_ROW_START
                && usize::from(cell.row) < STATE_ONLY_AUX_ROW_START + STATE_ONLY_AUX_ROW_COUNT
                && !removed.contains(cell)
        })
        .collect::<Vec<_>>();
    for level in registry.path_aux {
        aux_cells.extend([level.input_bit, level.output_bit, level.sibling_bit]);
        aux_cells.extend(level.input_current);
        aux_cells.extend(level.output_current);
        aux_cells.extend(level.sibling);
    }
    aux_cells.sort_unstable_by_key(|cell| (cell.row, cell.column));
    aux_cells.dedup();
    let auxiliary_rows_high_water = aux_cells
        .iter()
        .map(|cell| usize::from(cell.row) - STATE_ONLY_AUX_ROW_START + 1)
        .max()
        .unwrap_or(0);

    let mut tags = registry
        .links
        .iter()
        .map(|link| link.tag)
        .collect::<Vec<_>>();
    tags.sort_unstable_by_key(|tag| tag.0);
    tags.dedup();
    Ok(AtomicStateOnlyRegistryStatsV3 {
        copy_terms_m: registry.links.len(),
        unique_tag_groups: tags.len(),
        endpoint_active_rows,
        maximum_producers_per_row,
        maximum_consumers_per_row,
        tuple_patterns: patterns.len(),
        tensor_routing_rank,
        auxiliary_cells_used: aux_cells.len(),
        auxiliary_cells_capacity: STATE_ONLY_AUX_ROW_COUNT * STATE_ONLY_C1_COLUMNS,
        auxiliary_rows_high_water,
        base_semantic_lanes: ATOMIC_STATE_ONLY_BASE_SEMANTIC_LANES,
        randomized_semantic_lanes: ATOMIC_STATE_ONLY_RANDOMIZED_SEMANTIC_LANES,
        theta_lanes: ATOMIC_STATE_ONLY_THETA_LANES,
        theta_collision_degree: ATOMIC_STATE_ONLY_THETA_COLLISION_DEGREE,
        zerocheck_degree: ATOMIC_STATE_ONLY_ZEROCHECK_DEGREE,
        terminal_points: ATOMIC_STATE_ONLY_TERMINAL_POINTS,
        selected_pcs_width: ATOMIC_STATE_ONLY_SELECTED_PCS_WIDTH,
    })
}

pub fn atomic_state_only_registry_fingerprint_v3(
    registry: &AtomicStateOnlyRegistryV3,
) -> Result<u64, AtomicStateOnlyRegistryErrorV3> {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    let mut absorb = |byte: u8| {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    };
    for byte in b"aspis-atomic-state-only-registry-v3" {
        absorb(*byte);
    }
    for value in [
        ATOMIC_STATE_ONLY_BASE_SEMANTIC_LANES,
        ATOMIC_STATE_ONLY_RANDOMIZED_SEMANTIC_LANES,
        ATOMIC_STATE_ONLY_THETA_LANES,
        ATOMIC_STATE_ONLY_THETA_COLLISION_DEGREE,
        ATOMIC_STATE_ONLY_ZEROCHECK_DEGREE,
        ATOMIC_STATE_ONLY_TERMINAL_POINTS,
        ATOMIC_STATE_ONLY_SELECTED_PCS_WIDTH,
    ] {
        for byte in (value as u64).to_le_bytes() {
            absorb(byte);
        }
    }
    for level in registry.path_aux {
        absorb(level.level);
        for cell in [level.input_bit, level.output_bit, level.sibling_bit]
            .into_iter()
            .chain(level.input_current)
            .chain(level.output_current)
            .chain(level.sibling)
        {
            for byte in cell.row.to_le_bytes().into_iter().chain([cell.column]) {
                absorb(byte);
            }
        }
    }
    for link in &registry.links {
        for byte in link
            .id
            .to_le_bytes()
            .into_iter()
            .chain(link.tag.0.to_le_bytes())
        {
            absorb(byte);
        }
        for tuple in [link.producer, link.consumer] {
            for value in pattern_signature(tuple) {
                for byte in value.to_le_bytes() {
                    absorb(byte);
                }
            }
            for byte in tuple_row(tuple, link.id)?.to_le_bytes() {
                absorb(byte);
            }
        }
    }
    Ok(hash)
}

/// Pinned by the local three-point registry parity/rank artifact.
pub const PINNED_ATOMIC_STATE_ONLY_REGISTRY_FINGERPRINT_V3: u64 = 0xa524_9dda_67f7_5888;

impl From<StateOnlyLayoutError> for AtomicStateOnlyRegistryErrorV3 {
    fn from(_: StateOnlyLayoutError) -> Self {
        Self::Layout
    }
}
