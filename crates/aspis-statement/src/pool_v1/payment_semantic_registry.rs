//! Exact row-local routing registry for the Pool V1 Tag-73 payment trace.
//!
//! The payment trace uses the frozen 1,024-row, 16-C1 geometry.  Cross-row
//! equalities are represented by one bounded two-producer/two-consumer LogUp
//! helper, while path selection and 30-bit value checks are placed in the
//! existing `(z, successor(z), xor12(z))` three-point geometry.  This module
//! is still a host/compiler foundation: it does not alter the production
//! verifier or claim that the Pool relation is accepted on chain.

use alloc::{vec, vec::Vec};

use aspis_core::field::{M31, QM31};

use crate::{
    logup::{
        build_copy_logup_helper, compress_tagged_tuple, verify_copy_logup_constraints, CopyLogUpRow,
    },
    poseidon2::{DIGEST_ELEMS, MERKLE_NODE_COMPRESSION_V3_TWEAK, POSEIDON2_WIDTH},
    state_only_trace::StateOnlyTraceFoundation,
    trace_v4::TraceCell,
};

use super::payment_trace::{
    PoolV1PaymentTraceVariantV1, POOL_V1_PAYMENT_TRACE_BLOCK_ROWS, POOL_V1_PAYMENT_TRACE_ROWS,
};

pub const POOL_V1_PAYMENT_PATH_AUX_BLOCK_START: usize = 49;
pub const POOL_V1_PAYMENT_PATH_LEVELS_PER_AUX_BLOCK: usize = 4;
pub const POOL_V1_PAYMENT_PATH_AUX_BLOCKS: usize = 5;
pub const POOL_V1_PAYMENT_VALUE_AUX_BLOCK: usize = 54;
pub const POOL_V1_PAYMENT_VALUE_AUX_ROW_START: usize =
    POOL_V1_PAYMENT_VALUE_AUX_BLOCK * POOL_V1_PAYMENT_TRACE_BLOCK_ROWS;
pub const POOL_V1_PAYMENT_AUX_ROW_END: usize = 879;

pub const POOL_V1_PAYMENT_BASE_SEMANTIC_LANES: usize = 94;
pub const POOL_V1_PAYMENT_PACKED_BASE_LANES: usize =
    POOL_V1_PAYMENT_BASE_SEMANTIC_LANES.div_ceil(4);
pub const POOL_V1_PAYMENT_COPY_LANES: usize = 1;
pub const POOL_V1_PAYMENT_RANDOMIZED_SEMANTIC_LANES: usize =
    POOL_V1_PAYMENT_PACKED_BASE_LANES + POOL_V1_PAYMENT_COPY_LANES;
pub const POOL_V1_PAYMENT_POSEIDON_LANES: usize = 4;
pub const POOL_V1_PAYMENT_THETA_LANES: usize =
    POOL_V1_PAYMENT_POSEIDON_LANES + POOL_V1_PAYMENT_RANDOMIZED_SEMANTIC_LANES;
pub const POOL_V1_PAYMENT_THETA_COLLISION_DEGREE: usize = POOL_V1_PAYMENT_THETA_LANES - 1;
pub const POOL_V1_PAYMENT_ZEROCHECK_DEGREE: usize = 27;

const PATH_BASE_LOCAL_ROWS: [usize; POOL_V1_PAYMENT_PATH_LEVELS_PER_AUX_BLOCK] = [0, 2, 4, 6];
const VALUE_BASE_LOCAL_ROWS: [usize; 3] = [0, 2, 4];
const CONSERVATION_BASE_LOCAL_ROW: usize = 6;
const COPY_TAG_BASE: u32 = 0x4100_0000;

const _: () = assert!(DIGEST_ELEMS == 8);
const _: () = assert!(POSEIDON2_WIDTH == 16);
const _: () = assert!(POOL_V1_PAYMENT_PATH_AUX_BLOCKS * 4 == 20);
const _: () = assert!(POOL_V1_PAYMENT_PACKED_BASE_LANES == 24);
const _: () = assert!(POOL_V1_PAYMENT_RANDOMIZED_SEMANTIC_LANES == 25);
const _: () = assert!(POOL_V1_PAYMENT_THETA_LANES == 29);
const _: () = assert!(POOL_V1_PAYMENT_THETA_COLLISION_DEGREE == 28);
const _: () = assert!(POOL_V1_PAYMENT_AUX_ROW_END <= POOL_V1_PAYMENT_TRACE_ROWS);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PaymentPathAuxV1 {
    pub bit: TraceCell,
    pub current: [TraceCell; DIGEST_ELEMS],
    pub left: [TraceCell; DIGEST_ELEMS],
    pub right: [TraceCell; DIGEST_ELEMS],
    pub sibling: [TraceCell; DIGEST_ELEMS],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PaymentValueAuxV1 {
    pub bits: [TraceCell; 30],
    pub source: TraceCell,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PaymentConservationAuxV1 {
    pub input: TraceCell,
    pub recipient_or_amount: TraceCell,
    pub partial: TraceCell,
    pub carried_partial: TraceCell,
    pub change: TraceCell,
}

#[inline(always)]
const fn cell(row: usize, column: usize) -> TraceCell {
    TraceCell {
        row: row as u16,
        column: column as u8,
    }
}

#[inline(always)]
const fn xor12_row(row: usize) -> usize {
    row ^ 12
}

pub fn pool_v1_payment_path_aux_v1(level: usize) -> Option<PoolV1PaymentPathAuxV1> {
    if level >= 20 {
        return None;
    }
    let block =
        POOL_V1_PAYMENT_PATH_AUX_BLOCK_START + level / POOL_V1_PAYMENT_PATH_LEVELS_PER_AUX_BLOCK;
    let local = PATH_BASE_LOCAL_ROWS[level % POOL_V1_PAYMENT_PATH_LEVELS_PER_AUX_BLOCK];
    let base = block * POOL_V1_PAYMENT_TRACE_BLOCK_ROWS + local;
    let successor = base + 1;
    let sibling = xor12_row(base);
    Some(PoolV1PaymentPathAuxV1 {
        bit: cell(base, 0),
        current: core::array::from_fn(|lane| cell(base, 1 + lane)),
        left: core::array::from_fn(|lane| cell(successor, lane)),
        right: core::array::from_fn(|lane| cell(successor, 8 + lane)),
        sibling: core::array::from_fn(|lane| cell(sibling, lane)),
    })
}

pub fn pool_v1_payment_value_aux_v1(value: usize) -> Option<PoolV1PaymentValueAuxV1> {
    if value >= 3 {
        return None;
    }
    let base = POOL_V1_PAYMENT_VALUE_AUX_ROW_START + VALUE_BASE_LOCAL_ROWS[value];
    Some(PoolV1PaymentValueAuxV1 {
        bits: core::array::from_fn(|bit| {
            let view = bit / 10;
            let row = match view {
                0 => base,
                1 => base + 1,
                _ => xor12_row(base),
            };
            cell(row, bit % 10)
        }),
        source: cell(base, 10),
    })
}

pub const fn pool_v1_payment_conservation_aux_v1() -> PoolV1PaymentConservationAuxV1 {
    let base = POOL_V1_PAYMENT_VALUE_AUX_ROW_START + CONSERVATION_BASE_LOCAL_ROW;
    PoolV1PaymentConservationAuxV1 {
        input: cell(base, 0),
        recipient_or_amount: cell(base, 1),
        partial: cell(base, 2),
        carried_partial: cell(base + 1, 0),
        change: cell(base + 1, 1),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PaymentTupleLimbV1 {
    Zero,
    Constant(M31),
    AffineCell {
        cell: TraceCell,
        scale: M31,
        offset: M31,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PaymentCopyTupleV1 {
    pub row: u16,
    pub limbs: [PoolV1PaymentTupleLimbV1; POSEIDON2_WIDTH],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PaymentCopyLinkKindV1 {
    SpongeCarry { from: u8, to: u8 },
    OwnerOutput,
    NullifierKey,
    InputSaltHead,
    InputSaltTail,
    PathCurrent { level: u8 },
    PathLeft { level: u8 },
    PathRight { level: u8 },
    ValueSource { value: u8 },
    ConservationInput,
    ConservationRecipientOrAmount,
    ConservationChange,
    ConservationPartial,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PaymentCopyLinkV1 {
    pub id: u16,
    pub tag: M31,
    pub kind: PoolV1PaymentCopyLinkKindV1,
    pub producer: PoolV1PaymentCopyTupleV1,
    pub consumer: PoolV1PaymentCopyTupleV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoolV1PaymentSemanticRegistryV1 {
    pub variant: PoolV1PaymentTraceVariantV1,
    pub links: Vec<PoolV1PaymentCopyLinkV1>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PaymentSemanticRegistryErrorV1 {
    Layout,
    NonRowLocalTuple { link: u16 },
    EndpointCapacity { row: u16 },
    CopyImbalance,
}

fn affine(source: TraceCell) -> PoolV1PaymentTupleLimbV1 {
    PoolV1PaymentTupleLimbV1::AffineCell {
        cell: source,
        scale: M31::ONE,
        offset: M31::ZERO,
    }
}

fn affine_offset(source: TraceCell, offset: M31) -> PoolV1PaymentTupleLimbV1 {
    PoolV1PaymentTupleLimbV1::AffineCell {
        cell: source,
        scale: M31::ONE,
        offset,
    }
}

fn tuple(row: usize, limbs: &[PoolV1PaymentTupleLimbV1]) -> PoolV1PaymentCopyTupleV1 {
    let mut output = [PoolV1PaymentTupleLimbV1::Zero; POSEIDON2_WIDTH];
    output[..limbs.len()].copy_from_slice(limbs);
    PoolV1PaymentCopyTupleV1 {
        row: row as u16,
        limbs: output,
    }
}

fn cells_tuple(row: usize, cells: &[TraceCell]) -> PoolV1PaymentCopyTupleV1 {
    tuple(row, &cells.iter().copied().map(affine).collect::<Vec<_>>())
}

fn block_cells(block: usize, local_row: usize, start: usize, count: usize) -> Vec<TraceCell> {
    let row = block * POOL_V1_PAYMENT_TRACE_BLOCK_ROWS + local_row;
    (start..start + count)
        .map(|column| cell(row, column))
        .collect()
}

fn push_link(
    links: &mut Vec<PoolV1PaymentCopyLinkV1>,
    kind: PoolV1PaymentCopyLinkKindV1,
    producer: PoolV1PaymentCopyTupleV1,
    consumer: PoolV1PaymentCopyTupleV1,
) {
    let id = links.len() as u16;
    links.push(PoolV1PaymentCopyLinkV1 {
        id,
        tag: M31(COPY_TAG_BASE + u32::from(id)),
        kind,
        producer,
        consumer,
    });
}

pub fn build_pool_v1_payment_semantic_registry_v1(
    variant: PoolV1PaymentTraceVariantV1,
) -> Result<PoolV1PaymentSemanticRegistryV1, PoolV1PaymentSemanticRegistryErrorV1> {
    let mut links = Vec::new();

    let mut carries = vec![(1usize, 2usize), (2, 3), (24, 25), (29, 30), (30, 31)];
    if variant == PoolV1PaymentTraceVariantV1::PrivateTransfer {
        carries.extend([(26, 27), (27, 28)]);
    }
    for (from, to) in carries {
        push_link(
            &mut links,
            PoolV1PaymentCopyLinkKindV1::SpongeCarry {
                from: from as u8,
                to: to as u8,
            },
            cells_tuple(from * 16 + 11, &block_cells(from, 11, 0, POSEIDON2_WIDTH)),
            cells_tuple(to * 16, &block_cells(to, 0, 0, POSEIDON2_WIDTH)),
        );
    }

    push_link(
        &mut links,
        PoolV1PaymentCopyLinkKindV1::OwnerOutput,
        cells_tuple(11, &block_cells(0, 11, 0, DIGEST_ELEMS)),
        cells_tuple(1 * 16 + 12, &block_cells(1, 12, 0, DIGEST_ELEMS)),
    );
    push_link(
        &mut links,
        PoolV1PaymentCopyLinkKindV1::NullifierKey,
        cells_tuple(12, &block_cells(0, 12, 0, DIGEST_ELEMS)),
        cells_tuple(24 * 16 + 12, &block_cells(24, 12, 0, DIGEST_ELEMS)),
    );
    push_link(
        &mut links,
        PoolV1PaymentCopyLinkKindV1::InputSaltHead,
        cells_tuple(2 * 16 + 12, &block_cells(2, 12, 2, 6)),
        cells_tuple(25 * 16 + 12, &block_cells(25, 12, 0, 6)),
    );
    push_link(
        &mut links,
        PoolV1PaymentCopyLinkKindV1::InputSaltTail,
        cells_tuple(3 * 16 + 12, &block_cells(3, 12, 0, 2)),
        cells_tuple(25 * 16 + 12, &block_cells(25, 12, 6, 2)),
    );

    for level in 0..20 {
        let aux = pool_v1_payment_path_aux_v1(level)
            .ok_or(PoolV1PaymentSemanticRegistryErrorV1::Layout)?;
        let previous_block = 3 + level;
        push_link(
            &mut links,
            PoolV1PaymentCopyLinkKindV1::PathCurrent { level: level as u8 },
            cells_tuple(
                previous_block * 16 + 11,
                &block_cells(previous_block, 11, 0, DIGEST_ELEMS),
            ),
            cells_tuple(usize::from(aux.current[0].row), &aux.current),
        );
        push_link(
            &mut links,
            PoolV1PaymentCopyLinkKindV1::PathLeft { level: level as u8 },
            cells_tuple(usize::from(aux.left[0].row), &aux.left),
            cells_tuple(
                (4 + level) * 16 + 12,
                &block_cells(4 + level, 12, 0, DIGEST_ELEMS),
            ),
        );
        let actual_right = block_cells(4 + level, 0, 8, DIGEST_ELEMS);
        let mut adjusted = actual_right.iter().copied().map(affine).collect::<Vec<_>>();
        adjusted[DIGEST_ELEMS - 1] = affine_offset(
            actual_right[DIGEST_ELEMS - 1],
            M31::ZERO.sub(MERKLE_NODE_COMPRESSION_V3_TWEAK),
        );
        push_link(
            &mut links,
            PoolV1PaymentCopyLinkKindV1::PathRight { level: level as u8 },
            cells_tuple(usize::from(aux.right[0].row), &aux.right),
            tuple((4 + level) * 16, &adjusted),
        );
    }

    let source_cells = [
        cell(2 * 16 + 12, 0),
        cell(27 * 16 + 12, 0),
        cell(30 * 16 + 12, 0),
    ];
    for value in 0..3 {
        if value == 1 && variant == PoolV1PaymentTraceVariantV1::Withdrawal {
            continue;
        }
        let aux = pool_v1_payment_value_aux_v1(value)
            .ok_or(PoolV1PaymentSemanticRegistryErrorV1::Layout)?;
        push_link(
            &mut links,
            PoolV1PaymentCopyLinkKindV1::ValueSource { value: value as u8 },
            cells_tuple(usize::from(source_cells[value].row), &[source_cells[value]]),
            cells_tuple(usize::from(aux.source.row), &[aux.source]),
        );
    }

    let conservation = pool_v1_payment_conservation_aux_v1();
    for (kind, value, destination) in [
        (
            PoolV1PaymentCopyLinkKindV1::ConservationInput,
            0usize,
            conservation.input,
        ),
        (
            PoolV1PaymentCopyLinkKindV1::ConservationRecipientOrAmount,
            1usize,
            conservation.recipient_or_amount,
        ),
        (
            PoolV1PaymentCopyLinkKindV1::ConservationChange,
            2usize,
            conservation.change,
        ),
    ] {
        let source = pool_v1_payment_value_aux_v1(value)
            .ok_or(PoolV1PaymentSemanticRegistryErrorV1::Layout)?
            .source;
        push_link(
            &mut links,
            kind,
            cells_tuple(usize::from(source.row), &[source]),
            cells_tuple(usize::from(destination.row), &[destination]),
        );
    }
    push_link(
        &mut links,
        PoolV1PaymentCopyLinkKindV1::ConservationPartial,
        cells_tuple(
            usize::from(conservation.partial.row),
            &[conservation.partial],
        ),
        cells_tuple(
            usize::from(conservation.carried_partial.row),
            &[conservation.carried_partial],
        ),
    );

    let registry = PoolV1PaymentSemanticRegistryV1 { variant, links };
    endpoint_slots(&registry)?;
    Ok(registry)
}

fn tuple_row(
    tuple: PoolV1PaymentCopyTupleV1,
    link: u16,
) -> Result<u16, PoolV1PaymentSemanticRegistryErrorV1> {
    for limb in tuple.limbs {
        if let PoolV1PaymentTupleLimbV1::AffineCell { cell, .. } = limb {
            if cell.row != tuple.row {
                return Err(PoolV1PaymentSemanticRegistryErrorV1::NonRowLocalTuple { link });
            }
        }
    }
    Ok(tuple.row)
}

fn endpoint_slots(
    registry: &PoolV1PaymentSemanticRegistryV1,
) -> Result<([u8; 1024], [u8; 1024]), PoolV1PaymentSemanticRegistryErrorV1> {
    let mut producer = [0u8; 1024];
    let mut consumer = [0u8; 1024];
    for link in &registry.links {
        for (tuple, counts) in [
            (link.producer, &mut producer),
            (link.consumer, &mut consumer),
        ] {
            let row = usize::from(tuple_row(tuple, link.id)?);
            if counts[row] >= 2 {
                return Err(PoolV1PaymentSemanticRegistryErrorV1::EndpointCapacity {
                    row: row as u16,
                });
            }
            counts[row] += 1;
        }
    }
    Ok((producer, consumer))
}

fn tuple_value(
    trace: &StateOnlyTraceFoundation,
    tuple: PoolV1PaymentCopyTupleV1,
) -> [M31; POSEIDON2_WIDTH] {
    tuple.limbs.map(|limb| match limb {
        PoolV1PaymentTupleLimbV1::Zero => M31::ZERO,
        PoolV1PaymentTupleLimbV1::Constant(value) => value,
        PoolV1PaymentTupleLimbV1::AffineCell {
            cell,
            scale,
            offset,
        } => trace.c1[usize::from(cell.column)][usize::from(cell.row)]
            .mul(scale)
            .add(offset),
    })
}

pub fn pool_v1_payment_copy_rows_v1(
    registry: &PoolV1PaymentSemanticRegistryV1,
    trace: &StateOnlyTraceFoundation,
    lambda: QM31,
) -> Result<Vec<CopyLogUpRow>, PoolV1PaymentSemanticRegistryErrorV1> {
    let (mut producer_slots, mut consumer_slots) = endpoint_slots(registry)?;
    producer_slots.fill(0);
    consumer_slots.fill(0);
    let empty = CopyLogUpRow {
        producer_values: [QM31::ZERO; 2],
        producer_weights: [M31::ZERO; 2],
        consumer_values: [QM31::ZERO; 2],
        consumer_weights: [M31::ZERO; 2],
    };
    let mut rows = vec![empty; POOL_V1_PAYMENT_TRACE_ROWS];
    for link in &registry.links {
        for (tuple, is_producer) in [(link.producer, true), (link.consumer, false)] {
            let row_index = usize::from(tuple_row(tuple, link.id)?);
            let row = &mut rows[row_index];
            let (values, weights) = if is_producer {
                (&mut row.producer_values, &mut row.producer_weights)
            } else {
                (&mut row.consumer_values, &mut row.consumer_weights)
            };
            let slot = weights
                .iter()
                .position(|weight| *weight == M31::ZERO)
                .ok_or(PoolV1PaymentSemanticRegistryErrorV1::EndpointCapacity {
                    row: row_index as u16,
                })?;
            values[slot] = compress_tagged_tuple(link.tag, &tuple_value(trace, tuple), lambda);
            weights[slot] = M31::ONE;
        }
    }
    Ok(rows)
}

pub fn verify_pool_v1_payment_copy_registry_v1(
    variant: PoolV1PaymentTraceVariantV1,
    trace: &StateOnlyTraceFoundation,
    lambda: QM31,
    chi: QM31,
) -> Result<(), PoolV1PaymentSemanticRegistryErrorV1> {
    let registry = build_pool_v1_payment_semantic_registry_v1(variant)?;
    let rows = pool_v1_payment_copy_rows_v1(&registry, trace, lambda)?;
    let helper = build_copy_logup_helper(&rows, chi)
        .map_err(|_| PoolV1PaymentSemanticRegistryErrorV1::CopyImbalance)?;
    verify_copy_logup_constraints(&rows, &helper, chi)
        .map_err(|_| PoolV1PaymentSemanticRegistryErrorV1::CopyImbalance)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_geometry_and_endpoint_capacity_are_frozen() {
        for variant in [
            PoolV1PaymentTraceVariantV1::PrivateTransfer,
            PoolV1PaymentTraceVariantV1::Withdrawal,
        ] {
            let registry = build_pool_v1_payment_semantic_registry_v1(variant).unwrap();
            assert_eq!(
                registry.links.len(),
                if variant == PoolV1PaymentTraceVariantV1::PrivateTransfer {
                    78
                } else {
                    75
                }
            );
            let (producer, consumer) = endpoint_slots(&registry).unwrap();
            assert!(producer.into_iter().all(|count| count <= 2));
            assert!(consumer.into_iter().all(|count| count <= 2));
        }
        assert_eq!(pool_v1_payment_path_aux_v1(0).unwrap().bit, cell(784, 0));
        assert_eq!(pool_v1_payment_path_aux_v1(19).unwrap().sibling[0].row, 858);
        assert_eq!(pool_v1_payment_value_aux_v1(0).unwrap().bits[20].row, 876);
        assert_eq!(pool_v1_payment_value_aux_v1(2).unwrap().bits[20].row, 872);
    }
}
