//! Frozen payment constraint registry for the lr10/rate-1/16 SpendV0 trace.
//!
//! The registry contains 252 source constraints. The first 250 are
//! base-field-valued and are injectively packed four-at-a-time into 63 QM31
//! polynomials; the two LogUp constraints remain separate. Together with the
//! two independent helper-sum claims, the generic randomized ledger contains
//! 67 claims. The selected direct-range profile replaces the range LogUp with
//! nine packed lanes and has 73 constraint lanes plus one helper claim.

use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;

use aspis_core::field::{
    qm31_dot, qm31_evaluate_degree72_radix8, qm31_m31_dot, qm31_pack_base4, qm31_sum_products2,
    qm31_sum_products3, qm31_sum_products4, PreparedQm31Multiplier, CM31, M31, P, QM31,
};
use aspis_core::statement_sumcheck::PaymentConstraintChallenges;

use crate::logup::{
    build_copy_logup_helper, build_range_logup_helper, copy_logup_residual, range_logup_residual,
    verify_copy_logup_constraints, verify_range_logup_constraints, CopyLogUpRow, LogUpError,
    RangeLogUpRow,
};
use crate::poseidon2::{
    evaluate_trace_round, trace_round_constant, DIGEST_ELEMS, POSEIDON2_WIDTH, RATE,
};
use crate::spend::{SpendPublic, VALUE_LIMIT};
use crate::trace_v4::{
    copy_terminal_pattern, has_carry_payload, is_poseidon_active_row, is_poseidon_padding_row,
    merkle_boundary_layout, permutation_block_schedule, source_relation_layout,
    visit_copy_exceptional_terminal_links, visit_copy_links, visit_copy_terminal_links,
    witness_aux_layout, CopyTuple, SpendTraceV4, TraceCell, TupleLimb, ABSORPTION_ROW_IN_BLOCK,
    ACTIVE_ROWS_PER_BLOCK, AUX_ABSORPTION_PRODUCER_ROW_START, BLOCK_ROWS, COPY_LINK_COUNT,
    COPY_TERMINAL_PATTERN_COUNT, EXCEPTIONAL_COPY_TERMINAL_LINKS, FIRST_ROUND_OUTPUT_COLUMN_START,
    INPUT_VALUE_RANGE_ROW, INTERFACE_COLUMN_START, MULTIPLICITY_COLUMN, OUTPUT_VALUE_RANGE_ROW,
    PERMUTATION_COUNT, SECOND_ROUND_OUTPUT_COLUMN_START, STATE_AND_INTERFACE_COLUMNS, TRACE_ROWS,
    VALUE_RECONSTRUCTION_COLUMN,
};

pub const POSEIDON_FIRST_START: usize = 0;
pub const POSEIDON_SECOND_START: usize = POSEIDON_FIRST_START + POSEIDON2_WIDTH;
pub const INITIAL_STATE_START: usize = POSEIDON_SECOND_START + POSEIDON2_WIDTH;
pub const PADDING_ZERO_START: usize = INITIAL_STATE_START + POSEIDON2_WIDTH;
pub const ABSORPTION_TAIL_START: usize = PADDING_ZERO_START + STATE_AND_INTERFACE_COLUMNS;
pub const SOURCE_EQUALITY_START: usize = ABSORPTION_TAIL_START + STATE_AND_INTERFACE_COLUMNS;
pub const SOURCE_EQUALITY_COUNT: usize = 60;
pub const MERKLE_BIT_BOOLEAN_ID: usize = SOURCE_EQUALITY_START + SOURCE_EQUALITY_COUNT;
pub const MERKLE_LEFT_START: usize = MERKLE_BIT_BOOLEAN_ID + 1;
pub const MERKLE_RIGHT_START: usize = MERKLE_LEFT_START + DIGEST_ELEMS;
pub const INPUT_VALUE_RECONSTRUCTION_ID: usize = MERKLE_RIGHT_START + DIGEST_ELEMS;
pub const OUTPUT_VALUE_RECONSTRUCTION_ID: usize = INPUT_VALUE_RECONSTRUCTION_ID + 1;
pub const BALANCE_ID: usize = OUTPUT_VALUE_RECONSTRUCTION_ID + 1;
pub const PUBLIC_ANCHOR_START: usize = BALANCE_ID + 1;
pub const PUBLIC_NULLIFIER_START: usize = PUBLIC_ANCHOR_START + DIGEST_ELEMS;
pub const PUBLIC_OUTPUT_START: usize = PUBLIC_NULLIFIER_START + DIGEST_ELEMS;
pub const PUBLIC_INPUT_ASSET_ID: usize = PUBLIC_OUTPUT_START + DIGEST_ELEMS;
pub const PUBLIC_OUTPUT_ASSET_ID: usize = PUBLIC_INPUT_ASSET_ID + 1;
pub const COPY_LOGUP_ID: usize = PUBLIC_OUTPUT_ASSET_ID + 1;
pub const RANGE_LOGUP_ID: usize = COPY_LOGUP_ID + 1;
pub const CONSTRAINT_COUNT: usize = RANGE_LOGUP_ID + 1;
pub const GLOBAL_HELPER_SUM_CLAIMS: usize = 2;
pub const BASE_FIELD_CONSTRAINT_COUNT: usize = COPY_LOGUP_ID;
pub const PACKED_BASE_CONSTRAINT_COUNT: usize = (BASE_FIELD_CONSTRAINT_COUNT + 3) / 4;
pub const RANDOMIZED_CONSTRAINT_COUNT: usize = PACKED_BASE_CONSTRAINT_COUNT + 2;
pub const RANDOMIZED_CLAIM_COUNT: usize = RANDOMIZED_CONSTRAINT_COUNT + GLOBAL_HELPER_SUM_CLAIMS;
pub const DIRECT_RANGE_SOURCE_RESIDUAL_COUNT: usize =
    crate::direct_range_hiding_v4::DIRECT_RANGE_BITS_PER_ROW
        + crate::direct_range_hiding_v4::DIRECT_RANGE_LIMBS_PER_ROW;
pub const DIRECT_RANGE_CONSTRAINT_SOURCE_COUNT: usize =
    BASE_FIELD_CONSTRAINT_COUNT + 1 + DIRECT_RANGE_SOURCE_RESIDUAL_COUNT;
pub const DIRECT_RANGE_PACKED_LANE_COUNT: usize = (DIRECT_RANGE_SOURCE_RESIDUAL_COUNT + 3) / 4;
pub const DIRECT_RANGE_RANDOMIZED_CONSTRAINT_COUNT: usize =
    PACKED_BASE_CONSTRAINT_COUNT + 1 + DIRECT_RANGE_PACKED_LANE_COUNT;
pub const DIRECT_RANGE_GLOBAL_HELPER_SUM_CLAIMS: usize = 1;
pub const DIRECT_RANGE_RANDOMIZED_CLAIM_COUNT: usize =
    DIRECT_RANGE_RANDOMIZED_CONSTRAINT_COUNT + DIRECT_RANGE_GLOBAL_HELPER_SUM_CLAIMS;
pub const DIRECT_RANGE_THETA_COLLISION_DEGREE: usize = DIRECT_RANGE_RANDOMIZED_CONSTRAINT_COUNT - 1;

const _: () = assert!(CONSTRAINT_COUNT == 252);
const _: () = assert!(BASE_FIELD_CONSTRAINT_COUNT == 250);
const _: () = assert!(PACKED_BASE_CONSTRAINT_COUNT == 63);
const _: () = assert!(RANDOMIZED_CONSTRAINT_COUNT == 65);
const _: () = assert!(RANDOMIZED_CLAIM_COUNT == 67);
const _: () = assert!(DIRECT_RANGE_SOURCE_RESIDUAL_COUNT == 33);
const _: () = assert!(DIRECT_RANGE_CONSTRAINT_SOURCE_COUNT == 284);
const _: () = assert!(DIRECT_RANGE_PACKED_LANE_COUNT == 9);
const _: () = assert!(DIRECT_RANGE_GLOBAL_HELPER_SUM_CLAIMS == 1);
const _: () = assert!(DIRECT_RANGE_RANDOMIZED_CONSTRAINT_COUNT == 73);
const _: () = assert!(DIRECT_RANGE_RANDOMIZED_CLAIM_COUNT == 74);
const _: () = assert!(DIRECT_RANGE_THETA_COLLISION_DEGREE == 72);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ConstraintId(u16);

impl ConstraintId {
    pub const fn new(index: usize) -> Option<Self> {
        if index < CONSTRAINT_COUNT {
            Some(Self(index as u16))
        } else {
            None
        }
    }

    pub const fn index(self) -> usize {
        self.0 as usize
    }

    pub const fn wire_value(self) -> u16 {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstraintKind {
    PoseidonFirst { lane: u8 },
    PoseidonSecond { lane: u8 },
    InitialSpongeState { lane: u8 },
    PaddingZero { column: u8 },
    AbsorptionTailZero { column: u8 },
    SourceEquality { binding: u8 },
    MerklePathBitBoolean,
    MerkleLeftSelection { limb: u8 },
    MerkleRightSelection { limb: u8 },
    InputValueReconstruction,
    OutputValueReconstruction,
    Balance,
    PublicAnchor { limb: u8 },
    PublicNullifier { limb: u8 },
    PublicOutputCommitment { limb: u8 },
    PublicInputAsset,
    PublicOutputAsset,
    CopyLogUp,
    RangeLogUp,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ConstraintDescriptor {
    pub id: ConstraintId,
    pub kind: ConstraintKind,
}

pub fn constraint_registry() -> Vec<ConstraintDescriptor> {
    (0..CONSTRAINT_COUNT)
        .map(|index| {
            let id = ConstraintId::new(index).expect("registry index is in range");
            let kind = if index < POSEIDON_SECOND_START {
                ConstraintKind::PoseidonFirst {
                    lane: (index - POSEIDON_FIRST_START) as u8,
                }
            } else if index < INITIAL_STATE_START {
                ConstraintKind::PoseidonSecond {
                    lane: (index - POSEIDON_SECOND_START) as u8,
                }
            } else if index < PADDING_ZERO_START {
                ConstraintKind::InitialSpongeState {
                    lane: (index - INITIAL_STATE_START) as u8,
                }
            } else if index < ABSORPTION_TAIL_START {
                ConstraintKind::PaddingZero {
                    column: (index - PADDING_ZERO_START) as u8,
                }
            } else if index < SOURCE_EQUALITY_START {
                ConstraintKind::AbsorptionTailZero {
                    column: (index - ABSORPTION_TAIL_START) as u8,
                }
            } else if index < MERKLE_BIT_BOOLEAN_ID {
                ConstraintKind::SourceEquality {
                    binding: (index - SOURCE_EQUALITY_START) as u8,
                }
            } else if index == MERKLE_BIT_BOOLEAN_ID {
                ConstraintKind::MerklePathBitBoolean
            } else if index < MERKLE_RIGHT_START {
                ConstraintKind::MerkleLeftSelection {
                    limb: (index - MERKLE_LEFT_START) as u8,
                }
            } else if index < INPUT_VALUE_RECONSTRUCTION_ID {
                ConstraintKind::MerkleRightSelection {
                    limb: (index - MERKLE_RIGHT_START) as u8,
                }
            } else if index == INPUT_VALUE_RECONSTRUCTION_ID {
                ConstraintKind::InputValueReconstruction
            } else if index == OUTPUT_VALUE_RECONSTRUCTION_ID {
                ConstraintKind::OutputValueReconstruction
            } else if index == BALANCE_ID {
                ConstraintKind::Balance
            } else if index < PUBLIC_NULLIFIER_START {
                ConstraintKind::PublicAnchor {
                    limb: (index - PUBLIC_ANCHOR_START) as u8,
                }
            } else if index < PUBLIC_OUTPUT_START {
                ConstraintKind::PublicNullifier {
                    limb: (index - PUBLIC_NULLIFIER_START) as u8,
                }
            } else if index < PUBLIC_INPUT_ASSET_ID {
                ConstraintKind::PublicOutputCommitment {
                    limb: (index - PUBLIC_OUTPUT_START) as u8,
                }
            } else if index == PUBLIC_INPUT_ASSET_ID {
                ConstraintKind::PublicInputAsset
            } else if index == PUBLIC_OUTPUT_ASSET_ID {
                ConstraintKind::PublicOutputAsset
            } else if index == COPY_LOGUP_ID {
                ConstraintKind::CopyLogUp
            } else {
                ConstraintKind::RangeLogUp
            };
            ConstraintDescriptor { id, kind }
        })
        .collect()
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PaymentHelpersV4 {
    pub copy_rows: Vec<CopyLogUpRow>,
    pub range_rows: Vec<RangeLogUpRow>,
    pub h1: Vec<QM31>,
    pub h2: Vec<QM31>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstraintBuildError {
    Shape,
    PublicFeeOutOfRange,
    CopyEndpointOverflow { row: u16 },
    LogUp(LogUpError),
}

impl From<LogUpError> for ConstraintBuildError {
    fn from(error: LogUpError) -> Self {
        Self::LogUp(error)
    }
}

#[inline(always)]
fn lift(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}

#[inline(always)]
fn mul_cm31_by_tower_non_residue(value: CM31) -> CM31 {
    // (2+i)(a+bi) = (2a-b) + (a+2b)i.
    CM31::new(value.a.double().sub(value.b), value.a.add(value.b.double()))
}

/// Multiply by one of the M31 basis elements (1, i, u, iu) without a
/// generic extension multiplication. For M31-valued Boolean-row residuals,
/// summing four such coordinates is an injective packing into QM31.
#[inline(always)]
fn mul_tower_basis(value: QM31, coordinate: usize) -> QM31 {
    match coordinate {
        0 => value,
        1 => QM31 {
            c0: value.c0.mul_i(),
            c1: value.c1.mul_i(),
        },
        2 => QM31 {
            c0: mul_cm31_by_tower_non_residue(value.c1),
            c1: value.c0,
        },
        3 => QM31 {
            c0: mul_cm31_by_tower_non_residue(value.c1).mul_i(),
            c1: value.c0.mul_i(),
        },
        _ => unreachable!("QM31 has four M31 basis coordinates"),
    }
}

#[inline(always)]
fn pack_base_values(values: &[QM31]) -> QM31 {
    qm31_pack_base4(values)
}

#[inline(never)]
fn compose_randomized_residuals(
    residuals: &[QM31],
    direct_packed: Option<&[QM31]>,
    theta: QM31,
) -> QM31 {
    debug_assert_eq!(residuals.len(), CONSTRAINT_COUNT);
    let mut randomized = Vec::with_capacity(RANDOMIZED_CONSTRAINT_COUNT);
    for (group, chunk) in residuals[..BASE_FIELD_CONSTRAINT_COUNT]
        .chunks(4)
        .enumerate()
    {
        let packed = chunk
            .iter()
            .copied()
            .enumerate()
            .fold(QM31::ZERO, |packed, (coordinate, residual)| {
                packed.add(mul_tower_basis(residual, coordinate))
            });
        randomized.push(if let Some(direct) = direct_packed {
            packed.add(direct[group])
        } else {
            packed
        });
    }
    randomized.push(residuals[COPY_LOGUP_ID]);
    randomized.push(residuals[RANGE_LOGUP_ID]);
    debug_assert_eq!(randomized.len(), RANDOMIZED_CONSTRAINT_COUNT);

    let prepared_theta = PreparedQm31Multiplier::new(theta);
    randomized
        .into_iter()
        .rev()
        .fold(QM31::ZERO, |accumulator, residual| {
            prepared_theta.mul(accumulator).add(residual)
        })
}

/// Direct-range profile batching. The 63 packed base lanes are followed by the
/// extension-valued copy LogUp and nine injectively packed range lanes. There
/// is one outer theta polynomial of degree 72; no nested theta polynomial is
/// hidden inside the final lane.
#[inline(never)]
fn compose_direct_range_randomized_residuals(
    residuals: &[QM31],
    direct_packed: &[QM31],
    direct_range_packed: &[QM31; DIRECT_RANGE_PACKED_LANE_COUNT],
    theta: QM31,
) -> QM31 {
    debug_assert_eq!(residuals.len(), CONSTRAINT_COUNT);
    debug_assert_eq!(direct_packed.len(), PACKED_BASE_CONSTRAINT_COUNT);
    let mut randomized = Vec::with_capacity(DIRECT_RANGE_RANDOMIZED_CONSTRAINT_COUNT);
    for (group, chunk) in residuals[..BASE_FIELD_CONSTRAINT_COUNT]
        .chunks(4)
        .enumerate()
    {
        randomized.push(pack_base_values(chunk).add(direct_packed[group]));
    }
    randomized.push(residuals[COPY_LOGUP_ID]);
    randomized.extend_from_slice(direct_range_packed);
    debug_assert_eq!(randomized.len(), DIRECT_RANGE_RANDOMIZED_CONSTRAINT_COUNT);

    let prepared_theta = PreparedQm31Multiplier::new(theta);
    randomized
        .into_iter()
        .rev()
        .fold(QM31::ZERO, |accumulator, residual| {
            prepared_theta.mul(accumulator).add(residual)
        })
}

/// Terminal-only form of the ordinary composition.  The extension-point
/// evaluator already constructs all 63 packed base lanes directly, so
/// allocating and zeroing 252 scalar residuals merely to pack those zeros
/// again is dead work.  Starting Horner at the highest coefficient also
/// avoids multiplying an initial zero accumulator.
#[inline(never)]
fn compose_terminal_packed_residuals(
    direct_packed: &[QM31],
    copy_residual: QM31,
    range_residual: QM31,
    theta: QM31,
) -> QM31 {
    debug_assert_eq!(direct_packed.len(), PACKED_BASE_CONSTRAINT_COUNT);
    let prepared_theta = PreparedQm31Multiplier::new(theta);
    let mut accumulator = range_residual;
    accumulator = prepared_theta.mul(accumulator).add(copy_residual);
    for residual in direct_packed.iter().rev() {
        accumulator = prepared_theta.mul(accumulator).add(*residual);
    }
    accumulator
}

/// Terminal-only degree-72 direct-range composition over the already packed
/// lanes.  Coefficient order is the same as the generic/table path:
/// 63 base lanes, copy LogUp, then nine packed range lanes.
#[inline(never)]
fn compose_direct_range_terminal_packed_residuals(
    direct_packed: &[QM31],
    copy_residual: QM31,
    direct_range_packed: &[QM31; DIRECT_RANGE_PACKED_LANE_COUNT],
    theta: QM31,
) -> QM31 {
    debug_assert_eq!(direct_packed.len(), PACKED_BASE_CONSTRAINT_COUNT);
    let prepared_theta = PreparedQm31Multiplier::new(theta);
    let mut accumulator = direct_range_packed[DIRECT_RANGE_PACKED_LANE_COUNT - 1];
    for residual in direct_range_packed[..DIRECT_RANGE_PACKED_LANE_COUNT - 1]
        .iter()
        .rev()
    {
        accumulator = prepared_theta.mul(accumulator).add(*residual);
    }
    accumulator = prepared_theta.mul(accumulator).add(copy_residual);
    for residual in direct_packed.iter().rev() {
        accumulator = prepared_theta.mul(accumulator).add(*residual);
    }
    accumulator
}

/// Radix-eight A/B candidate for the production degree-72 terminal.
///
/// The terminal evaluator has already materialized the 63 base lanes in a
/// vector and does not use them after composition.  Appending the copy lane
/// and nine direct-range lanes in place therefore gives the fixed evaluator a
/// contiguous 73-coefficient view without another allocation or a 1,168-byte
/// stack copy.  The caller reserves the final capacity before constructing
/// the base lanes.
#[inline(never)]
fn compose_direct_range_terminal_packed_residuals_radix8(
    direct_packed: &mut Vec<QM31>,
    copy_residual: QM31,
    direct_range_packed: &[QM31; DIRECT_RANGE_PACKED_LANE_COUNT],
    theta: QM31,
) -> QM31 {
    debug_assert_eq!(direct_packed.len(), PACKED_BASE_CONSTRAINT_COUNT);
    direct_packed.push(copy_residual);
    direct_packed.extend_from_slice(direct_range_packed);
    let coefficients: &[QM31; DIRECT_RANGE_RANDOMIZED_CONSTRAINT_COUNT] = direct_packed
        .as_slice()
        .try_into()
        .expect("fixed degree-72 terminal coefficient count");
    qm31_evaluate_degree72_radix8(coefficients, theta)
}

fn read_cell(trace: &SpendTraceV4, cell: TraceCell) -> M31 {
    trace.c1[cell.column as usize][cell.row as usize]
}

fn tuple_value(trace: &SpendTraceV4, tuple: CopyTuple) -> [M31; POSEIDON2_WIDTH] {
    tuple.limbs.map(|limb| match limb {
        TupleLimb::Cell(cell) => read_cell(trace, cell),
        TupleLimb::Zero => M31::ZERO,
    })
}

fn insert_copy_endpoint(
    values: &mut [QM31; 2],
    weights: &mut [M31; 2],
    value: QM31,
    row: usize,
) -> Result<(), ConstraintBuildError> {
    let slot = weights
        .iter()
        .position(|weight| *weight == M31::ZERO)
        .ok_or(ConstraintBuildError::CopyEndpointOverflow { row: row as u16 })?;
    values[slot] = value;
    weights[slot] = M31::ONE;
    Ok(())
}

pub fn build_payment_helpers_v4(
    trace: &SpendTraceV4,
    lambda: QM31,
    chi: QM31,
) -> Result<PaymentHelpersV4, ConstraintBuildError> {
    if trace.c1.iter().any(|column| column.len() != TRACE_ROWS) {
        return Err(ConstraintBuildError::Shape);
    }
    let mut copy_rows = vec![
        CopyLogUpRow {
            producer_values: [QM31::ZERO; 2],
            producer_weights: [M31::ZERO; 2],
            consumer_values: [QM31::ZERO; 2],
            consumer_weights: [M31::ZERO; 2],
        };
        TRACE_ROWS
    ];
    let mut endpoint_error = None;
    visit_copy_links(|link| {
        if endpoint_error.is_some() {
            return;
        }
        let producer_row = usize::from(link.producer_row);
        let consumer_row = usize::from(link.consumer_row);
        let producer = crate::logup::compress_tagged_tuple(
            link.tag,
            &tuple_value(trace, link.producer),
            lambda,
        );
        let consumer = crate::logup::compress_tagged_tuple(
            link.tag,
            &tuple_value(trace, link.consumer),
            lambda,
        );
        {
            let row = &mut copy_rows[producer_row];
            if let Err(error) = insert_copy_endpoint(
                &mut row.producer_values,
                &mut row.producer_weights,
                producer,
                producer_row,
            ) {
                endpoint_error = Some(error);
                return;
            }
        }
        {
            let row = &mut copy_rows[consumer_row];
            if let Err(error) = insert_copy_endpoint(
                &mut row.consumer_values,
                &mut row.consumer_weights,
                consumer,
                consumer_row,
            ) {
                endpoint_error = Some(error);
            }
        }
    });
    if let Some(error) = endpoint_error {
        return Err(error);
    }

    let aux = witness_aux_layout();
    let range_rows = (0..TRACE_ROWS)
        .map(|row| {
            let producer_weights = if row == INPUT_VALUE_RANGE_ROW || row == OUTPUT_VALUE_RANGE_ROW
            {
                [M31::ONE; 3]
            } else {
                [M31::ZERO; 3]
            };
            RangeLogUpRow {
                producer_values: core::array::from_fn(|index| lift(trace.c1[index][row])),
                producer_weights,
                consumer_value: lift(M31(row as u32)),
                consumer_weight: trace.c1[MULTIPLICITY_COLUMN][row],
            }
        })
        .collect::<Vec<_>>();
    debug_assert_eq!(
        read_cell(trace, aux.input_value_limbs[0]),
        trace.c1[0][INPUT_VALUE_RANGE_ROW]
    );
    debug_assert_eq!(
        read_cell(trace, aux.output_value_limbs[0]),
        trace.c1[0][OUTPUT_VALUE_RANGE_ROW]
    );

    let h1 = build_copy_logup_helper(&copy_rows, chi)?;
    let h2 = build_range_logup_helper(&range_rows, chi)?;
    Ok(PaymentHelpersV4 {
        copy_rows,
        range_rows,
        h1,
        h2,
    })
}

pub fn verify_payment_helpers_v4(
    helpers: &PaymentHelpersV4,
    chi: QM31,
) -> Result<(), ConstraintBuildError> {
    verify_copy_logup_constraints(&helpers.copy_rows, &helpers.h1, chi)?;
    verify_range_logup_constraints(&helpers.range_rows, &helpers.h2, chi)?;
    Ok(())
}

pub struct ConstraintContextV4<'a> {
    pub public: &'a SpendPublic,
    pub trace: &'a SpendTraceV4,
    pub helpers: &'a PaymentHelpersV4,
    pub chi: QM31,
}

/// The 51 committed MLE values needed by the statement terminal, plus the
/// C1 values at the low-bit-XOR-11 point used to read block absorptions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PointOpeningsV4 {
    pub c1: [QM31; STATE_AND_INTERFACE_COLUMNS + 1],
    pub c1_xor11: [QM31; STATE_AND_INTERFACE_COLUMNS + 1],
    pub c2: [QM31; 2],
}

/// One-mask+C1-padding statement openings. Every value is opened and bound by
/// the ordinary 51-column gamma combination.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DirectRangeHidingPointOpeningsV4 {
    pub c1: [QM31; STATE_AND_INTERFACE_COLUMNS + 1],
    pub c1_xor11: [QM31; STATE_AND_INTERFACE_COLUMNS + 1],
    pub h1: QM31,
    pub payment_mask: QM31,
}

impl DirectRangeHidingPointOpeningsV4 {
    pub fn constraint_openings(self) -> PointOpeningsV4 {
        PointOpeningsV4 {
            c1: self.c1,
            c1_xor11: self.c1_xor11,
            c2: [self.h1, QM31::ZERO],
        }
    }
}

#[inline(always)]
fn eq_row(point: &[QM31; 10], row: usize) -> QM31 {
    let mut weight = QM31::ONE;
    for (coordinate, value) in point.iter().enumerate() {
        let bit = (row >> (point.len() - 1 - coordinate)) & 1;
        weight = weight.mul(if bit == 0 {
            QM31::ONE.sub(*value)
        } else {
            *value
        });
    }
    weight
}

fn sparse_eq_weights(point: &[QM31; 10]) -> Vec<(usize, QM31)> {
    let trailing_boolean = point
        .iter()
        .rev()
        .take_while(|value| **value == QM31::ZERO || **value == QM31::ONE)
        .count();
    let prefix_len = point.len() - trailing_boolean;
    let mut suffix = 0usize;
    for coordinate in &point[prefix_len..] {
        suffix = (suffix << 1) | usize::from(*coordinate == QM31::ONE);
    }
    let mut weights = Vec::with_capacity(1usize << prefix_len);
    for prefix in 0..(1usize << prefix_len) {
        let row = (prefix << trailing_boolean) | suffix;
        let mut weight = QM31::ONE;
        for (coordinate, value) in point[..prefix_len].iter().enumerate() {
            let bit = (prefix >> (prefix_len - 1 - coordinate)) & 1;
            weight = weight.mul(if bit == 0 {
                QM31::ONE.sub(*value)
            } else {
                *value
            });
        }
        weights.push((row, weight));
    }
    weights
}

#[derive(Clone, Copy)]
struct TensorSelectors {
    high: [QM31; 64],
    low: [QM31; 16],
}

impl TensorSelectors {
    fn expand<const N: usize>(coordinates: &[QM31]) -> [QM31; N] {
        debug_assert_eq!(N, 1usize << coordinates.len());
        let mut weights = [QM31::ZERO; N];
        weights[0] = QM31::ONE;
        let mut len = 1usize;
        for coordinate in coordinates {
            let prepared = PreparedQm31Multiplier::new(*coordinate);
            for index in (0..len).rev() {
                let parent = weights[index];
                let right = prepared.mul(parent);
                weights[2 * index] = parent.sub(right);
                weights[2 * index + 1] = right;
            }
            len *= 2;
        }
        weights
    }

    fn new(point: &[QM31; 10]) -> Self {
        Self {
            high: Self::expand(&point[..6]),
            low: Self::expand(&point[6..]),
        }
    }

    #[inline(always)]
    fn row(&self, row: usize) -> QM31 {
        self.high[row >> 4].mul(self.low[row & 15])
    }

    fn high_sum<I>(&self, indices: I) -> QM31
    where
        I: IntoIterator<Item = usize>,
    {
        indices
            .into_iter()
            .fold(QM31::ZERO, |sum, index| sum.add(self.high[index]))
    }

    /// Exact MLEs of the two adjacent direct-range row intervals. Rows
    /// 864..866 share high tensor coordinate 54 and low coordinates 0/1;
    /// rows 866..1024 are the remainder of high coordinates 54..64. Reusing
    /// the first selector in the second identity avoids walking the generic
    /// dyadic decomposition twice.
    #[inline(always)]
    fn direct_range_and_copy_padding(&self) -> (QM31, QM31) {
        const DIRECT_RANGE_HIGH: usize =
            crate::direct_range_hiding_v4::DIRECT_RANGE_BIT_ROW_START / 16;
        const _: () = assert!(
            crate::direct_range_hiding_v4::DIRECT_RANGE_BIT_ROW_START == DIRECT_RANGE_HIGH * 16
        );
        const _: () = assert!(
            crate::direct_range_hiding_v4::COPY_HELPER_PADDING_ROW_START
                == crate::direct_range_hiding_v4::DIRECT_RANGE_BIT_ROW_START + 2
        );

        let direct_range = self.high[DIRECT_RANGE_HIGH].mul(self.low[0].add(self.low[1]));
        let direct_range_and_padding = self.high_sum(DIRECT_RANGE_HIGH..64);
        (direct_range, direct_range_and_padding.sub(direct_range))
    }
}

/// Toggle the low row-index bits `0, 1, 3`. For multilinear tables this is
/// exactly the extension-field point whose evaluation equals the XOR-11
/// permuted table at the original point.
pub fn xor11_point(point: &[QM31; 10]) -> [QM31; 10] {
    let mut shifted = *point;
    for bit in [0usize, 1, 3] {
        let coordinate = point.len() - 1 - bit;
        shifted[coordinate] = QM31::ONE.sub(shifted[coordinate]);
    }
    shifted
}

pub fn multilinear_evaluate(column: &[M31], point: &[QM31; 10]) -> Option<QM31> {
    if column.len() != TRACE_ROWS {
        return None;
    }
    Some(
        sparse_eq_weights(point)
            .into_iter()
            .fold(QM31::ZERO, |sum, (row, weight)| {
                sum.add(weight.mul_m31(column[row]))
            }),
    )
}

#[cfg(not(target_os = "solana"))]
pub fn trace_openings_at_point(
    trace: &SpendTraceV4,
    helpers: &PaymentHelpersV4,
    point: &[QM31; 10],
) -> Option<PointOpeningsV4> {
    trace_openings_from_columns(trace, &helpers.h1, &helpers.h2, point)
}

/// One-mask+C1-padding openings. The removed range helper's C2 slot is
/// occupied by the single full-domain payment mask oracle.
#[cfg(not(target_os = "solana"))]
pub fn direct_range_hiding_trace_openings_at_point(
    trace: &SpendTraceV4,
    helpers: &crate::direct_range_hiding_v4::DirectRangeHidingHelpersV4,
    point: &[QM31; 10],
) -> Option<DirectRangeHidingPointOpeningsV4> {
    let first = trace_openings_from_columns(trace, &helpers.h1, &helpers.payment_mask, point)?;
    Some(DirectRangeHidingPointOpeningsV4 {
        c1: first.c1,
        c1_xor11: first.c1_xor11,
        h1: first.c2[0],
        payment_mask: first.c2[1],
    })
}

#[cfg(not(target_os = "solana"))]
fn trace_openings_from_columns(
    trace: &SpendTraceV4,
    h1: &[QM31],
    h2: &[QM31],
    point: &[QM31; 10],
) -> Option<PointOpeningsV4> {
    if trace.c1.iter().any(|column| column.len() != TRACE_ROWS)
        || h1.len() != TRACE_ROWS
        || h2.len() != TRACE_ROWS
    {
        return None;
    }
    let shifted = xor11_point(point);
    let weights = sparse_eq_weights(point);
    let shifted_weights = sparse_eq_weights(&shifted);
    let evaluate_m31 = |column: &[M31], weights: &[(usize, QM31)]| {
        weights.iter().fold(QM31::ZERO, |sum, &(row, weight)| {
            sum.add(weight.mul_m31(column[row]))
        })
    };
    let evaluate_qm31 = |column: &[QM31], weights: &[(usize, QM31)]| {
        weights.iter().fold(QM31::ZERO, |sum, &(row, weight)| {
            sum.add(weight.mul(column[row]))
        })
    };
    Some(PointOpeningsV4 {
        c1: core::array::from_fn(|column| evaluate_m31(&trace.c1[column], &weights)),
        c1_xor11: core::array::from_fn(|column| evaluate_m31(&trace.c1[column], &shifted_weights)),
        c2: [evaluate_qm31(h1, &weights), evaluate_qm31(h2, &weights)],
    })
}

pub fn multilinear_evaluate_qm31(column: &[QM31], point: &[QM31; 10]) -> Option<QM31> {
    if column.len() != TRACE_ROWS {
        return None;
    }
    Some(
        sparse_eq_weights(point)
            .into_iter()
            .fold(QM31::ZERO, |sum, (row, weight)| {
                sum.add(weight.mul(column[row]))
            }),
    )
}

#[inline(always)]
fn pow5_extension(value: QM31) -> QM31 {
    let square = value.square();
    square.square().mul(value)
}

#[inline(always)]
fn extension_limbs(value: QM31) -> [u32; 4] {
    [value.c0.a.0, value.c0.b.0, value.c1.a.0, value.c1.b.0]
}

#[inline(always)]
fn extension_from_raw_limbs(limbs: [u64; 4]) -> QM31 {
    QM31 {
        c0: CM31::new(M31::reduce_u62(limbs[0]), M31::reduce_u62(limbs[1])),
        c1: CM31::new(M31::reduce_u62(limbs[2]), M31::reduce_u62(limbs[3])),
    }
}

#[inline(never)]
fn external_linear_extension(state: &mut [QM31; POSEIDON2_WIDTH]) {
    for values in state.chunks_exact_mut(4) {
        let input: [QM31; 4] = values.try_into().expect("four-lane chunk");
        let input = input.map(extension_limbs);
        for output in 0..4 {
            let raw = core::array::from_fn(|limb| {
                let a = u64::from(input[0][limb]);
                let b = u64::from(input[1][limb]);
                let c = u64::from(input[2][limb]);
                let d = u64::from(input[3][limb]);
                match output {
                    0 => 2 * a + 3 * b + c + d,
                    1 => a + 2 * b + 3 * c + d,
                    2 => a + b + 2 * c + 3 * d,
                    3 => 3 * a + b + c + 2 * d,
                    _ => unreachable!(),
                }
            });
            values[output] = extension_from_raw_limbs(raw);
        }
    }
    let sums: [[u64; 4]; 4] = core::array::from_fn(|column| {
        core::array::from_fn(|limb| {
            (0..4)
                .map(|row| u64::from(extension_limbs(state[row * 4 + column])[limb]))
                .sum()
        })
    });
    for (index, value) in state.iter_mut().enumerate() {
        let limbs = extension_limbs(*value);
        *value = extension_from_raw_limbs(core::array::from_fn(|limb| {
            u64::from(limbs[limb]) + sums[index & 3][limb]
        }));
    }
}

#[inline(never)]
fn internal_linear_extension(state: &mut [QM31; POSEIDON2_WIDTH]) {
    const SHIFTS: [u8; 15] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16];
    let old_zero = extension_limbs(state[0]);
    let part_sum: [u64; 4] = core::array::from_fn(|limb| {
        state[1..]
            .iter()
            .map(|value| u64::from(extension_limbs(*value)[limb]))
            .sum()
    });
    let full_sum: [u64; 4] =
        core::array::from_fn(|limb| part_sum[limb] + u64::from(old_zero[limb]));
    state[0] = extension_from_raw_limbs(core::array::from_fn(|limb| {
        part_sum[limb] + u64::from(P) - u64::from(old_zero[limb])
    }));
    for lane in 1..POSEIDON2_WIDTH {
        let limbs = extension_limbs(state[lane]);
        state[lane] = extension_from_raw_limbs(core::array::from_fn(|limb| {
            full_sum[limb] + (u64::from(limbs[limb]) << SHIFTS[lane - 1])
        }));
    }
}

#[inline(never)]
fn apply_extension_round(state: &mut [QM31; POSEIDON2_WIDTH], round: usize) {
    let (constants, full) = crate::poseidon2::trace_round_descriptor(round)
        .expect("trace round index is fixed and valid");
    if full {
        for lane in 0..POSEIDON2_WIDTH {
            state[lane] = pow5_extension(state[lane].add(lift(constants[lane])));
        }
        external_linear_extension(state);
    } else {
        state[0] = pow5_extension(state[0].add(lift(constants[0])));
        internal_linear_extension(state);
    }
}

#[cfg(test)]
#[inline(never)]
fn extension_round_pair(
    mut first_input: [QM31; POSEIDON2_WIDTH],
    mut second_input: [QM31; POSEIDON2_WIDTH],
    local_row: usize,
) -> ([QM31; POSEIDON2_WIDTH], [QM31; POSEIDON2_WIDTH]) {
    if local_row == 0 {
        external_linear_extension(&mut first_input);
    }
    apply_extension_round(&mut first_input, 2 * local_row);
    apply_extension_round(&mut second_input, 2 * local_row + 1);
    (first_input, second_input)
}

#[inline(never)]
fn apply_extension_full_round(
    mut state: [QM31; POSEIDON2_WIDTH],
    constants: [QM31; POSEIDON2_WIDTH],
) -> [QM31; POSEIDON2_WIDTH] {
    for lane in 0..POSEIDON2_WIDTH {
        state[lane] = pow5_extension(state[lane].add(constants[lane]));
    }
    external_linear_extension(&mut state);
    state
}

#[inline(never)]
fn apply_extension_internal_round(
    mut state: [QM31; POSEIDON2_WIDTH],
    constant: QM31,
) -> [QM31; POSEIDON2_WIDTH] {
    state[0] = pow5_extension(state[0].add(constant));
    internal_linear_extension(&mut state);
    state
}

#[inline(always)]
fn accumulate_poseidon_first_category(
    selector: QM31,
    openings: &PointOpeningsV4,
    first: [QM31; POSEIDON2_WIDTH],
    packed: &mut [QM31],
) {
    for lane_group in 0..POSEIDON2_WIDTH / 4 {
        let lane_start = 4 * lane_group;
        let first_values: [QM31; 4] = core::array::from_fn(|offset| {
            let lane = lane_start + offset;
            openings.c1[FIRST_ROUND_OUTPUT_COLUMN_START + lane].sub(first[lane])
        });
        let first_group = POSEIDON_FIRST_START / 4 + lane_group;
        packed[first_group] =
            packed[first_group].add(selector.mul(pack_base_values(&first_values)));
    }
}

#[inline(always)]
fn accumulate_poseidon_second_category(
    selector: QM31,
    openings: &PointOpeningsV4,
    second: [QM31; POSEIDON2_WIDTH],
    packed: &mut [QM31],
) {
    for lane_group in 0..POSEIDON2_WIDTH / 4 {
        let lane_start = 4 * lane_group;
        let second_values: [QM31; 4] = core::array::from_fn(|offset| {
            let lane = lane_start + offset;
            openings.c1[SECOND_ROUND_OUTPUT_COLUMN_START + lane].sub(second[lane])
        });
        let second_group = POSEIDON_SECOND_START / 4 + lane_group;
        packed[second_group] =
            packed[second_group].add(selector.mul(pack_base_values(&second_values)));
    }
}

#[cfg(test)]
#[inline(always)]
fn accumulate_poseidon_category(
    selector: QM31,
    openings: &PointOpeningsV4,
    first: [QM31; POSEIDON2_WIDTH],
    second: [QM31; POSEIDON2_WIDTH],
    packed: &mut [QM31],
) {
    accumulate_poseidon_first_category(selector, openings, first, packed);
    accumulate_poseidon_second_category(selector, openings, second, packed);
}

/// The selector and the interpolated full-round constants are individually
/// multilinear. A fifth-power S-box followed by one category selector therefore
/// has individual degree at most six, below the degree-ten sumcheck wire bound.
const POSEIDON_PREPROCESSED_INDIVIDUAL_DEGREE: usize = 6;
const _: () = assert!(
    POSEIDON_PREPROCESSED_INDIVIDUAL_DEGREE
        < aspis_core::statement_sumcheck::PAYMENT_SUMCHECK_FULL_COEFFICIENTS
);

/// Evaluate the two-round Poseidon transition with preprocessed row classes.
/// Row zero and local rows 1/9/10 retain distinct even-round computations.
/// Their odd rounds are all full, consume the same first-round opening vector,
/// and are combined into one selector-interpolated full-round computation.
/// This changes the off-domain representative but agrees with the frozen AIR
/// on every Boolean row and remains inside the degree-ten sumcheck wire bound.
#[inline(never)]
fn evaluate_poseidon_constraints(
    openings: &PointOpeningsV4,
    selectors: &TensorSelectors,
    block_selector: QM31,
    packed: &mut [QM31],
) {
    // Row zero includes absorption from the XOR-11 row and the permutation's
    // leading external linear layer.
    let mut first_input = core::array::from_fn(|lane| openings.c1[INTERFACE_COLUMN_START + lane]);
    for lane in 0..RATE {
        first_input[lane] = first_input[lane].add(openings.c1_xor11[lane]);
    }
    external_linear_extension(&mut first_input);
    apply_extension_round(&mut first_input, 0);
    let leading_low = selectors.low[0];
    accumulate_poseidon_first_category(
        block_selector.mul(leading_low),
        openings,
        first_input,
        packed,
    );

    // Local rows 1, 9, and 10 contain the remaining six full rounds. A
    // preprocessed constant column is represented directly by its MLE value.
    const FULL_LOCAL_ROWS: [usize; 3] = [1, 9, 10];
    let full_lows = FULL_LOCAL_ROWS.map(|row| selectors.low[row]);
    let (leading_odd, leading_odd_full) =
        crate::poseidon2::trace_round_descriptor(1).expect("frozen leading full round");
    debug_assert!(leading_odd_full);
    let full_low = full_lows.into_iter().fold(QM31::ZERO, QM31::add);
    let first_constants = core::array::from_fn(|lane| {
        let constants = FULL_LOCAL_ROWS.map(|row| {
            let (constant, full) =
                trace_round_constant(2 * row, lane).expect("frozen full even round");
            debug_assert!(full);
            constant
        });
        qm31_m31_dot(&full_lows, &constants)
    });
    let second_weights = [leading_low, full_lows[0], full_lows[1], full_lows[2]];
    let second_constants = core::array::from_fn(|lane| {
        let constants = [
            leading_odd[lane],
            trace_round_constant(2 * FULL_LOCAL_ROWS[0] + 1, lane)
                .expect("frozen full odd round")
                .0,
            trace_round_constant(2 * FULL_LOCAL_ROWS[1] + 1, lane)
                .expect("frozen full odd round")
                .0,
            trace_round_constant(2 * FULL_LOCAL_ROWS[2] + 1, lane)
                .expect("frozen full odd round")
                .0,
        ];
        qm31_m31_dot(&second_weights, &constants)
    });
    let first = apply_extension_full_round(
        core::array::from_fn(|lane| openings.c1[INTERFACE_COLUMN_START + lane]),
        first_constants,
    );
    accumulate_poseidon_first_category(block_selector.mul(full_low), openings, first, packed);

    let second = apply_extension_full_round(
        core::array::from_fn(|lane| openings.c1[FIRST_ROUND_OUTPUT_COLUMN_START + lane]),
        second_constants,
    );
    accumulate_poseidon_second_category(
        block_selector.mul(leading_low.add(full_low)),
        openings,
        second,
        packed,
    );

    // Local rows 2..=8 contain the fourteen partial rounds. Only lane zero
    // receives a round constant and an S-box.
    const INTERNAL_LOCAL_ROWS: [usize; 7] = [2, 3, 4, 5, 6, 7, 8];
    let internal_lows = INTERNAL_LOCAL_ROWS.map(|row| selectors.low[row]);
    let internal_low = internal_lows.into_iter().fold(QM31::ZERO, QM31::add);
    let first_internal_constants = INTERNAL_LOCAL_ROWS.map(|row| {
        let (constant, full) =
            trace_round_constant(2 * row, 0).expect("frozen internal even round");
        debug_assert!(!full);
        constant
    });
    let second_internal_constants = INTERNAL_LOCAL_ROWS.map(|row| {
        let (constant, full) =
            trace_round_constant(2 * row + 1, 0).expect("frozen internal odd round");
        debug_assert!(!full);
        constant
    });
    let first_constant = qm31_m31_dot(&internal_lows, &first_internal_constants);
    let second_constant = qm31_m31_dot(&internal_lows, &second_internal_constants);
    let first = apply_extension_internal_round(
        core::array::from_fn(|lane| openings.c1[INTERFACE_COLUMN_START + lane]),
        first_constant,
    );
    let second = apply_extension_internal_round(
        core::array::from_fn(|lane| openings.c1[FIRST_ROUND_OUTPUT_COLUMN_START + lane]),
        second_constant,
    );
    let selector = block_selector.mul(internal_low);
    accumulate_poseidon_first_category(selector, openings, first, packed);
    accumulate_poseidon_second_category(selector, openings, second, packed);
}

/// Pre-merge evaluator retained only as an independent Boolean-row reference.
/// It computes row zero's odd full round separately from rows 1/9/10.
#[cfg(test)]
fn evaluate_poseidon_constraints_reference(
    openings: &PointOpeningsV4,
    selectors: &TensorSelectors,
    block_selector: QM31,
    packed: &mut [QM31],
) {
    let mut first_input = core::array::from_fn(|lane| openings.c1[INTERFACE_COLUMN_START + lane]);
    for lane in 0..RATE {
        first_input[lane] = first_input[lane].add(openings.c1_xor11[lane]);
    }
    let second_input =
        core::array::from_fn(|lane| openings.c1[FIRST_ROUND_OUTPUT_COLUMN_START + lane]);
    let (first, second) = extension_round_pair(first_input, second_input, 0);
    accumulate_poseidon_category(
        block_selector.mul(selectors.low[0]),
        openings,
        first,
        second,
        packed,
    );

    let mut first_constants = [QM31::ZERO; POSEIDON2_WIDTH];
    let mut second_constants = [QM31::ZERO; POSEIDON2_WIDTH];
    let mut full_low = QM31::ZERO;
    for local_row in [1usize, 9, 10] {
        full_low = full_low.add(selectors.low[local_row]);
        let (even, even_full) =
            crate::poseidon2::trace_round_descriptor(2 * local_row).expect("frozen full round");
        let (odd, odd_full) =
            crate::poseidon2::trace_round_descriptor(2 * local_row + 1).expect("frozen full round");
        debug_assert!(even_full && odd_full);
        for lane in 0..POSEIDON2_WIDTH {
            first_constants[lane] =
                first_constants[lane].add(selectors.low[local_row].mul_m31(even[lane]));
            second_constants[lane] =
                second_constants[lane].add(selectors.low[local_row].mul_m31(odd[lane]));
        }
    }
    let first = apply_extension_full_round(
        core::array::from_fn(|lane| openings.c1[INTERFACE_COLUMN_START + lane]),
        first_constants,
    );
    let second = apply_extension_full_round(
        core::array::from_fn(|lane| openings.c1[FIRST_ROUND_OUTPUT_COLUMN_START + lane]),
        second_constants,
    );
    accumulate_poseidon_category(
        block_selector.mul(full_low),
        openings,
        first,
        second,
        packed,
    );

    let mut first_constant = QM31::ZERO;
    let mut second_constant = QM31::ZERO;
    let mut internal_low = QM31::ZERO;
    for local_row in 2usize..=8 {
        internal_low = internal_low.add(selectors.low[local_row]);
        let (even, even_full) =
            crate::poseidon2::trace_round_descriptor(2 * local_row).expect("frozen internal round");
        let (odd, odd_full) = crate::poseidon2::trace_round_descriptor(2 * local_row + 1)
            .expect("frozen internal round");
        debug_assert!(!even_full && !odd_full);
        first_constant = first_constant.add(selectors.low[local_row].mul_m31(even[0]));
        second_constant = second_constant.add(selectors.low[local_row].mul_m31(odd[0]));
    }
    let first = apply_extension_internal_round(
        core::array::from_fn(|lane| openings.c1[INTERFACE_COLUMN_START + lane]),
        first_constant,
    );
    let second = apply_extension_internal_round(
        core::array::from_fn(|lane| openings.c1[FIRST_ROUND_OUTPUT_COLUMN_START + lane]),
        second_constant,
    );
    accumulate_poseidon_category(
        block_selector.mul(internal_low),
        openings,
        first,
        second,
        packed,
    );
}

fn compress_opened_tuple(
    tuple: CopyTuple,
    tag: M31,
    openings: &[QM31; STATE_AND_INTERFACE_COLUMNS + 1],
    lambda: QM31,
) -> QM31 {
    let mut compressed = lift(tag);
    let mut power = lambda;
    for limb in tuple.limbs {
        if let TupleLimb::Cell(cell) = limb {
            compressed = compressed.add(power.mul(openings[cell.column as usize]));
        }
        power = power.mul(lambda);
    }
    compressed
}

const COPY_ROUTING_MATRIX_COUNT: usize = 4 * (2 + COPY_TERMINAL_PATTERN_COUNT);
const COPY_ROUTING_RANK: usize = 47;
const COPY_ROUTING_EXPANDED_FACTOR_SUPPORT: usize = 674;
const COPY_ROUTING_UNIQUE_LEFT_FACTOR_COUNT: usize = 33;
const COPY_ROUTING_UNIQUE_RIGHT_FACTOR_COUNT: usize = 31;
const COPY_ROUTING_UNIQUE_FACTOR_SUPPORT: usize = 639;
const COPY_ROUTING_UNIQUE_PAIR_COUNT: usize = 44;

#[derive(Clone, Copy)]
struct CopyRoutingPatternSupport {
    indices: [u8; COPY_TERMINAL_PATTERN_COUNT],
    len: u8,
}

const EMPTY_COPY_ROUTING_PATTERN_SUPPORT: CopyRoutingPatternSupport = CopyRoutingPatternSupport {
    indices: [0; COPY_TERMINAL_PATTERN_COUNT],
    len: 0,
};

/// Generate the per-slot support from the same frozen exceptional-link table
/// that generates the factorization. Runtime may then skip identically-zero
/// pattern matrices without a separately maintained, hand-written mask.
const fn build_copy_routing_pattern_supports() -> [CopyRoutingPatternSupport; 4] {
    let mut masks = [0u16; 4];
    let mut link_index = 0usize;
    while link_index < EXCEPTIONAL_COPY_TERMINAL_LINKS.len() {
        let link = EXCEPTIONAL_COPY_TERMINAL_LINKS[link_index];
        masks[link.producer_slot as usize] |= 1u16 << link.producer_pattern;
        // Exceptional consumers use the first consumer slot, matching the
        // generated routing matrices in build_copy_routing_factorization.
        masks[2] |= 1u16 << link.consumer_pattern;
        link_index += 1;
    }

    let mut supports = [EMPTY_COPY_ROUTING_PATTERN_SUPPORT; 4];
    let mut slot = 0usize;
    while slot < supports.len() {
        let mut pattern = 0usize;
        let mut len = 0usize;
        while pattern < COPY_TERMINAL_PATTERN_COUNT {
            if masks[slot] & (1u16 << pattern) != 0 {
                supports[slot].indices[len] = pattern as u8;
                len += 1;
            }
            pattern += 1;
        }
        supports[slot].len = len as u8;
        slot += 1;
    }
    supports
}

const COPY_ROUTING_PATTERN_SUPPORTS: [CopyRoutingPatternSupport; 4] =
    build_copy_routing_pattern_supports();

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CopyRoutingEntry {
    index: u8,
    coefficient: u32,
}

const EMPTY_COPY_ROUTING_ENTRY: CopyRoutingEntry = CopyRoutingEntry {
    index: 0,
    coefficient: 0,
};

#[derive(Clone, Copy)]
struct CopyRoutingFactor {
    start: u16,
    len: u8,
}

const EMPTY_COPY_ROUTING_FACTOR: CopyRoutingFactor = CopyRoutingFactor { start: 0, len: 0 };

#[derive(Clone, Copy)]
struct RawCopyRoutingTerm {
    matrix: u8,
    left_factor: u8,
    right_factor: u8,
}

const EMPTY_RAW_COPY_ROUTING_TERM: RawCopyRoutingTerm = RawCopyRoutingTerm {
    matrix: 0,
    left_factor: 0,
    right_factor: 0,
};

#[derive(Clone, Copy)]
struct CopyRoutingTerm {
    left_factor: u8,
    right_factor: u8,
    matrix_start: u8,
    matrix_len: u8,
}

const EMPTY_COPY_ROUTING_TERM: CopyRoutingTerm = CopyRoutingTerm {
    left_factor: 0,
    right_factor: 0,
    matrix_start: 0,
    matrix_len: 0,
};

struct CopyRoutingFactorization {
    terms: [CopyRoutingTerm; COPY_ROUTING_UNIQUE_PAIR_COUNT],
    matrices: [u8; COPY_ROUTING_RANK],
    left_factors: [CopyRoutingFactor; COPY_ROUTING_UNIQUE_LEFT_FACTOR_COUNT],
    right_factors: [CopyRoutingFactor; COPY_ROUTING_UNIQUE_RIGHT_FACTOR_COUNT],
    entries: [CopyRoutingEntry; COPY_ROUTING_UNIQUE_FACTOR_SUPPORT],
}

const fn m31_add_raw(left: u32, right: u32) -> u32 {
    let sum = left as u64 + right as u64;
    (sum % P as u64) as u32
}

const fn m31_sub_raw(left: u32, right: u32) -> u32 {
    ((left as u64 + P as u64 - right as u64) % P as u64) as u32
}

const fn m31_mul_raw(left: u32, right: u32) -> u32 {
    ((left as u64 * right as u64) % P as u64) as u32
}

const fn m31_pow_raw(mut base: u32, mut exponent: u32) -> u32 {
    let mut accumulator = 1u32;
    while exponent != 0 {
        if exponent & 1 == 1 {
            accumulator = m31_mul_raw(accumulator, base);
        }
        base = m31_mul_raw(base, base);
        exponent >>= 1;
    }
    accumulator
}

const fn build_copy_routing_factorization() -> CopyRoutingFactorization {
    let mut matrices = [[[0u32; 16]; 64]; COPY_ROUTING_MATRIX_COUNT];
    let mut link_index = 0usize;
    while link_index < EXCEPTIONAL_COPY_TERMINAL_LINKS.len() {
        let link = EXCEPTIONAL_COPY_TERMINAL_LINKS[link_index];
        let mut endpoint = 0usize;
        while endpoint < 2 {
            let (slot, row, pattern) = if endpoint == 0 {
                (
                    link.producer_slot as usize,
                    link.producer_row as usize,
                    link.producer_pattern as usize,
                )
            } else {
                (
                    2usize,
                    link.consumer_row as usize,
                    link.consumer_pattern as usize,
                )
            };
            let block = row >> 4;
            let local = row & 15;
            let base = slot * (2 + COPY_TERMINAL_PATTERN_COUNT);
            matrices[base][block][local] = m31_add_raw(matrices[base][block][local], 1);
            matrices[base + 1][block][local] =
                m31_add_raw(matrices[base + 1][block][local], link.tag.0);
            matrices[base + 2 + pattern][block][local] =
                m31_add_raw(matrices[base + 2 + pattern][block][local], 1);
            endpoint += 1;
        }
        link_index += 1;
    }

    // Gaussian elimination produces 47 outer products, but many use the same
    // block-side or local-side linear form. Keep one dense copy while the
    // const generator runs, then emit only the sparse unique forms. Runtime
    // terms reference compact factor IDs rather than re-evaluating duplicates.
    let mut raw_terms = [EMPTY_RAW_COPY_ROUTING_TERM; COPY_ROUTING_RANK];
    let mut unique_left = [[0u32; 64]; COPY_ROUTING_UNIQUE_LEFT_FACTOR_COUNT];
    let mut unique_right = [[0u32; 16]; COPY_ROUTING_UNIQUE_RIGHT_FACTOR_COUNT];
    let mut term_count = 0usize;
    let mut left_count = 0usize;
    let mut right_count = 0usize;
    let mut matrix_index = 0usize;
    while matrix_index < COPY_ROUTING_MATRIX_COUNT {
        loop {
            let mut pivot_row = 0usize;
            let mut pivot_column = 0usize;
            let mut found = false;
            let mut row = 0usize;
            while row < 64 && !found {
                let mut column = 0usize;
                while column < 16 {
                    if matrices[matrix_index][row][column] != 0 {
                        pivot_row = row;
                        pivot_column = column;
                        found = true;
                        break;
                    }
                    column += 1;
                }
                row += 1;
            }
            if !found {
                break;
            }

            let inverse = m31_pow_raw(matrices[matrix_index][pivot_row][pivot_column], P - 2);
            let mut left = [0u32; 64];
            let mut right = [0u32; 16];
            row = 0;
            while row < 64 {
                left[row] = matrices[matrix_index][row][pivot_column];
                row += 1;
            }
            let mut column = 0usize;
            while column < 16 {
                right[column] = m31_mul_raw(matrices[matrix_index][pivot_row][column], inverse);
                column += 1;
            }

            let mut left_id = 0usize;
            let mut left_found = false;
            while left_id < left_count {
                let mut coordinate = 0usize;
                let mut equal = true;
                while coordinate < 64 {
                    if unique_left[left_id][coordinate] != left[coordinate] {
                        equal = false;
                        break;
                    }
                    coordinate += 1;
                }
                if equal {
                    left_found = true;
                    break;
                }
                left_id += 1;
            }
            if !left_found {
                assert!(left_count < COPY_ROUTING_UNIQUE_LEFT_FACTOR_COUNT);
                unique_left[left_count] = left;
                left_id = left_count;
                left_count += 1;
            }

            let mut right_id = 0usize;
            let mut right_found = false;
            while right_id < right_count {
                let mut coordinate = 0usize;
                let mut equal = true;
                while coordinate < 16 {
                    if unique_right[right_id][coordinate] != right[coordinate] {
                        equal = false;
                        break;
                    }
                    coordinate += 1;
                }
                if equal {
                    right_found = true;
                    break;
                }
                right_id += 1;
            }
            if !right_found {
                assert!(right_count < COPY_ROUTING_UNIQUE_RIGHT_FACTOR_COUNT);
                unique_right[right_count] = right;
                right_id = right_count;
                right_count += 1;
            }

            assert!(term_count < COPY_ROUTING_RANK);
            raw_terms[term_count] = RawCopyRoutingTerm {
                matrix: matrix_index as u8,
                left_factor: left_id as u8,
                right_factor: right_id as u8,
            };
            term_count += 1;

            row = 0;
            while row < 64 {
                column = 0;
                while column < 16 {
                    matrices[matrix_index][row][column] = m31_sub_raw(
                        matrices[matrix_index][row][column],
                        m31_mul_raw(left[row], right[column]),
                    );
                    column += 1;
                }
                row += 1;
            }
        }
        matrix_index += 1;
    }
    assert!(term_count == COPY_ROUTING_RANK);
    assert!(left_count == COPY_ROUTING_UNIQUE_LEFT_FACTOR_COUNT);
    assert!(right_count == COPY_ROUTING_UNIQUE_RIGHT_FACTOR_COUNT);

    let mut entries = [EMPTY_COPY_ROUTING_ENTRY; COPY_ROUTING_UNIQUE_FACTOR_SUPPORT];
    let mut left_factors = [EMPTY_COPY_ROUTING_FACTOR; COPY_ROUTING_UNIQUE_LEFT_FACTOR_COUNT];
    let mut right_factors = [EMPTY_COPY_ROUTING_FACTOR; COPY_ROUTING_UNIQUE_RIGHT_FACTOR_COUNT];
    let mut entry_count = 0usize;
    let mut factor = 0usize;
    while factor < left_count {
        let start = entry_count;
        let mut coordinate = 0usize;
        while coordinate < 64 {
            let coefficient = unique_left[factor][coordinate];
            if coefficient != 0 {
                assert!(entry_count < COPY_ROUTING_UNIQUE_FACTOR_SUPPORT);
                entries[entry_count] = CopyRoutingEntry {
                    index: coordinate as u8,
                    coefficient,
                };
                entry_count += 1;
            }
            coordinate += 1;
        }
        left_factors[factor] = CopyRoutingFactor {
            start: start as u16,
            len: (entry_count - start) as u8,
        };
        factor += 1;
    }
    factor = 0;
    while factor < right_count {
        let start = entry_count;
        let mut coordinate = 0usize;
        while coordinate < 16 {
            let coefficient = unique_right[factor][coordinate];
            if coefficient != 0 {
                assert!(entry_count < COPY_ROUTING_UNIQUE_FACTOR_SUPPORT);
                entries[entry_count] = CopyRoutingEntry {
                    index: coordinate as u8,
                    coefficient,
                };
                entry_count += 1;
            }
            coordinate += 1;
        }
        right_factors[factor] = CopyRoutingFactor {
            start: start as u16,
            len: (entry_count - start) as u8,
        };
        factor += 1;
    }
    assert!(entry_count == COPY_ROUTING_UNIQUE_FACTOR_SUPPORT);

    // Three outer products are shared by more than one output matrix. Group
    // equal factor pairs and retain their destination list so those products
    // are also computed once. Duplicate destinations remain duplicated, which
    // preserves multiplicity if the generated layout ever contains one.
    let mut terms = [EMPTY_COPY_ROUTING_TERM; COPY_ROUTING_UNIQUE_PAIR_COUNT];
    let mut destinations = [0u8; COPY_ROUTING_RANK];
    let mut pair_count = 0usize;
    let mut destination_count = 0usize;
    let mut raw_index = 0usize;
    while raw_index < term_count {
        let candidate = raw_terms[raw_index];
        let mut previous = 0usize;
        let mut already_emitted = false;
        while previous < raw_index {
            let prior = raw_terms[previous];
            if prior.left_factor == candidate.left_factor
                && prior.right_factor == candidate.right_factor
            {
                already_emitted = true;
                break;
            }
            previous += 1;
        }
        if !already_emitted {
            assert!(pair_count < COPY_ROUTING_UNIQUE_PAIR_COUNT);
            let start = destination_count;
            let mut matching = 0usize;
            while matching < term_count {
                let term = raw_terms[matching];
                if term.left_factor == candidate.left_factor
                    && term.right_factor == candidate.right_factor
                {
                    assert!(destination_count < COPY_ROUTING_RANK);
                    destinations[destination_count] = term.matrix;
                    destination_count += 1;
                }
                matching += 1;
            }
            terms[pair_count] = CopyRoutingTerm {
                left_factor: candidate.left_factor,
                right_factor: candidate.right_factor,
                matrix_start: start as u8,
                matrix_len: (destination_count - start) as u8,
            };
            pair_count += 1;
        }
        raw_index += 1;
    }
    assert!(pair_count == COPY_ROUTING_UNIQUE_PAIR_COUNT);
    assert!(destination_count == COPY_ROUTING_RANK);

    CopyRoutingFactorization {
        terms,
        matrices: destinations,
        left_factors,
        right_factors,
        entries,
    }
}

const COPY_ROUTING_FACTORIZATION: CopyRoutingFactorization = build_copy_routing_factorization();

const fn fingerprint_u64(mut hash: u64, value: u64) -> u64 {
    let mut byte = 0usize;
    while byte < 8 {
        hash ^= (value >> (8 * byte)) & 0xff;
        hash = hash.wrapping_mul(0x100_0000_01b3);
        byte += 1;
    }
    hash
}

const fn copy_routing_layout_fingerprint() -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    let mut index = 0usize;
    while index < EXCEPTIONAL_COPY_TERMINAL_LINKS.len() {
        let link = EXCEPTIONAL_COPY_TERMINAL_LINKS[index];
        hash = fingerprint_u64(hash, link.id as u64);
        hash = fingerprint_u64(hash, link.tag.0 as u64);
        hash = fingerprint_u64(hash, link.producer_row as u64);
        hash = fingerprint_u64(hash, link.consumer_row as u64);
        hash = fingerprint_u64(hash, link.producer_pattern as u64);
        hash = fingerprint_u64(hash, link.consumer_pattern as u64);
        hash = fingerprint_u64(hash, link.producer_slot as u64);
        index += 1;
    }
    index = 0;
    while index < COPY_TERMINAL_PATTERN_COUNT {
        let pattern = copy_terminal_pattern(index);
        let mut limb = 0usize;
        while limb < POSEIDON2_WIDTH {
            hash = fingerprint_u64(hash, (pattern[limb] as i16 + 1) as u64);
            limb += 1;
        }
        index += 1;
    }
    hash
}

pub const COPY_ROUTING_LAYOUT_FINGERPRINT: u64 = copy_routing_layout_fingerprint();
pub const PINNED_COPY_ROUTING_LAYOUT_FINGERPRINT: u64 = 0x7797_3120_f60b_e58b;
const _: () = assert!(
    COPY_ROUTING_LAYOUT_FINGERPRINT == PINNED_COPY_ROUTING_LAYOUT_FINGERPRINT,
    "copy routing layout changed; review and deliberately repin the generated factorization"
);

#[inline(always)]
fn copy_routing_linear_form(entries: &[CopyRoutingEntry], selectors: &[QM31]) -> QM31 {
    // Four maximal M31 products fit in u64. Reduce once per four-entry block,
    // then reduce the small sum of canonical block results once per limb.
    // This is exactly the same M31-linear form as entry-by-entry scaling.
    let mut sums = [0u64; 4];
    for block in entries.chunks(4) {
        let mut raw = [0u64; 4];
        for entry in block {
            let selector = selectors[usize::from(entry.index)];
            let limbs = [
                selector.c0.a.0,
                selector.c0.b.0,
                selector.c1.a.0,
                selector.c1.b.0,
            ];
            for limb in 0..4 {
                raw[limb] += u64::from(limbs[limb]) * u64::from(entry.coefficient);
            }
        }
        for limb in 0..4 {
            sums[limb] += u64::from(M31::reduce_u64(raw[limb]).0);
        }
    }
    QM31 {
        c0: CM31::new(M31::reduce_u64(sums[0]), M31::reduce_u64(sums[1])),
        c1: CM31::new(M31::reduce_u64(sums[2]), M31::reduce_u64(sums[3])),
    }
}

#[inline(never)]
fn evaluate_exceptional_copy_routing(
    selectors: &TensorSelectors,
) -> [QM31; COPY_ROUTING_MATRIX_COUNT] {
    let left_values: [QM31; COPY_ROUTING_UNIQUE_LEFT_FACTOR_COUNT] =
        core::array::from_fn(|index| {
            let factor = COPY_ROUTING_FACTORIZATION.left_factors[index];
            let start = usize::from(factor.start);
            copy_routing_linear_form(
                &COPY_ROUTING_FACTORIZATION.entries[start..start + usize::from(factor.len)],
                &selectors.high,
            )
        });
    let right_values: [QM31; COPY_ROUTING_UNIQUE_RIGHT_FACTOR_COUNT] =
        core::array::from_fn(|index| {
            let factor = COPY_ROUTING_FACTORIZATION.right_factors[index];
            let start = usize::from(factor.start);
            copy_routing_linear_form(
                &COPY_ROUTING_FACTORIZATION.entries[start..start + usize::from(factor.len)],
                &selectors.low,
            )
        });
    let mut matrices = [QM31::ZERO; COPY_ROUTING_MATRIX_COUNT];
    for term in COPY_ROUTING_FACTORIZATION.terms {
        let product = left_values[usize::from(term.left_factor)]
            .mul(right_values[usize::from(term.right_factor)]);
        let start = usize::from(term.matrix_start);
        let end = start + usize::from(term.matrix_len);
        for &matrix in &COPY_ROUTING_FACTORIZATION.matrices[start..end] {
            let matrix = usize::from(matrix);
            matrices[matrix] = matrices[matrix].add(product);
        }
    }
    matrices
}

#[inline(never)]
fn evaluate_exceptional_copy_routing_direct(
    selectors: &TensorSelectors,
) -> [QM31; COPY_ROUTING_MATRIX_COUNT] {
    let mut matrices = [QM31::ZERO; COPY_ROUTING_MATRIX_COUNT];
    for link in EXCEPTIONAL_COPY_TERMINAL_LINKS {
        for (slot, row, pattern) in [
            (
                usize::from(link.producer_slot),
                usize::from(link.producer_row),
                usize::from(link.producer_pattern),
            ),
            (
                2usize,
                usize::from(link.consumer_row),
                usize::from(link.consumer_pattern),
            ),
        ] {
            let selector = selectors.high[row >> 4].mul(selectors.low[row & 15]);
            let base = slot * (2 + COPY_TERMINAL_PATTERN_COUNT);
            matrices[base] = matrices[base].add(selector);
            matrices[base + 1] = matrices[base + 1].add(selector.mul_m31(link.tag));
            matrices[base + 2 + pattern] = matrices[base + 2 + pattern].add(selector);
        }
    }
    matrices
}

/// Dot only the generated nonzero exceptional-pattern matrices for one slot.
/// The arity dispatch is constant-folded at each `SLOT` call site. Groups of
/// up to four products use the existing exact lazy-reduction primitives.
#[inline(always)]
fn exceptional_copy_pattern_dot<const SLOT: usize>(
    exceptional: &[QM31; COPY_ROUTING_MATRIX_COUNT],
    pattern_values: &[QM31; COPY_TERMINAL_PATTERN_COUNT],
) -> QM31 {
    let support = COPY_ROUTING_PATTERN_SUPPORTS[SLOT];
    let pair = |offset: usize| {
        let pattern = usize::from(support.indices[offset]);
        let base = SLOT * (2 + COPY_TERMINAL_PATTERN_COUNT) + 2;
        (exceptional[base + pattern], pattern_values[pattern])
    };
    let sum2 = |offset: usize| {
        let (left0, right0) = pair(offset);
        let (left1, right1) = pair(offset + 1);
        qm31_sum_products2([left0, left1], [right0, right1])
    };
    let sum3 = |offset: usize| {
        let (left0, right0) = pair(offset);
        let (left1, right1) = pair(offset + 1);
        let (left2, right2) = pair(offset + 2);
        qm31_sum_products3([left0, left1, left2], [right0, right1, right2])
    };
    let sum4 = |offset: usize| {
        let (left0, right0) = pair(offset);
        let (left1, right1) = pair(offset + 1);
        let (left2, right2) = pair(offset + 2);
        let (left3, right3) = pair(offset + 3);
        qm31_sum_products4(
            [left0, left1, left2, left3],
            [right0, right1, right2, right3],
        )
    };
    match support.len {
        0 => QM31::ZERO,
        1 => {
            let (left, right) = pair(0);
            left.mul(right)
        }
        2 => sum2(0),
        3 => sum3(0),
        4 => sum4(0),
        5 => {
            let (left, right) = pair(4);
            sum4(0).add(left.mul(right))
        }
        6 => sum4(0).add(sum2(4)),
        7 => sum4(0).add(sum3(4)),
        8 => sum4(0).add(sum4(4)),
        9 => {
            let (left, right) = pair(8);
            sum4(0).add(sum4(4)).add(left.mul(right))
        }
        10 => sum4(0).add(sum4(4)).add(sum2(8)),
        _ => unreachable!("generated copy-pattern support exceeds frozen pattern count"),
    }
}

#[inline(always)]
fn copy_lambda_powers(lambda: QM31) -> [QM31; POSEIDON2_WIDTH] {
    let mut powers = [QM31::ZERO; POSEIDON2_WIDTH];
    let mut power = lambda;
    for (index, output) in powers.iter_mut().enumerate() {
        *output = power;
        if index + 1 != POSEIDON2_WIDTH {
            power = power.mul(lambda);
        }
    }
    powers
}

/// Evaluate every frozen terminal tuple pattern with the four-product lazy
/// QM31 dot kernel. Besides the prefix reuse for patterns 0/2, the frozen
/// column layout gives the exact polynomial identities
///
///   pattern 1 = pattern 6 + lambda^8 * pattern 4
///   pattern 5 = pattern 6 + lambda^8 * pattern 3.
///
/// These identities hold for every opening vector and extension-field lambda,
/// including lambda zero; they are not Boolean-domain simplifications.
#[inline(never)]
fn copy_pattern_values_lazy(
    powers: &[QM31; POSEIDON2_WIDTH],
    openings: &[QM31; STATE_AND_INTERFACE_COLUMNS + 1],
) -> [QM31; COPY_TERMINAL_PATTERN_COUNT] {
    let mut pattern_values = [QM31::ZERO; COPY_TERMINAL_PATTERN_COUNT];
    pattern_values[2] = qm31_dot(
        &powers[..DIGEST_ELEMS],
        &openings
            [SECOND_ROUND_OUTPUT_COLUMN_START..SECOND_ROUND_OUTPUT_COLUMN_START + DIGEST_ELEMS],
    );
    pattern_values[0] = pattern_values[2].add(qm31_dot(
        &powers[DIGEST_ELEMS..],
        &openings[SECOND_ROUND_OUTPUT_COLUMN_START + DIGEST_ELEMS
            ..SECOND_ROUND_OUTPUT_COLUMN_START + POSEIDON2_WIDTH],
    ));
    pattern_values[6] = qm31_dot(
        &powers[..RATE],
        &openings[INTERFACE_COLUMN_START..INTERFACE_COLUMN_START + RATE],
    );
    pattern_values[3] = qm31_dot(
        &powers[..DIGEST_ELEMS],
        &openings[FIRST_ROUND_OUTPUT_COLUMN_START..FIRST_ROUND_OUTPUT_COLUMN_START + DIGEST_ELEMS],
    );
    pattern_values[4] = qm31_dot(
        &powers[..DIGEST_ELEMS],
        &openings[RATE..RATE + DIGEST_ELEMS],
    );
    let lambda_to_eight = powers[RATE - 1];
    pattern_values[1] = pattern_values[6].add(lambda_to_eight.mul(pattern_values[4]));
    pattern_values[5] = pattern_values[6].add(lambda_to_eight.mul(pattern_values[3]));
    pattern_values[7] = powers[0].mul(openings[VALUE_RECONSTRUCTION_COLUMN]);
    pattern_values[8] = powers[0].mul(openings[33]);
    pattern_values[9] = powers[0].mul(openings[VALUE_RECONSTRUCTION_COLUMN + 1]);
    pattern_values
}

#[inline(never)]
fn copy_terminal_rows_with_powers(
    selectors: &TensorSelectors,
    openings: &[QM31; STATE_AND_INTERFACE_COLUMNS + 1],
    powers: &[QM31; POSEIDON2_WIDTH],
) -> (CopyLogUpRowExtension, [QM31; 4]) {
    let exceptional = evaluate_exceptional_copy_routing(selectors);
    let pattern_values = copy_pattern_values_lazy(powers, openings);
    let mut weights = [QM31::ZERO; 4];
    let mut values = [QM31::ZERO; 4];

    // For id = 10*b + l, the regular producer endpoint is (b,l) and
    // consumer endpoint is (b,l+1). Their tag id+1 has tensor rank two:
    // (10*b+1) + l. This is algebraically identical to visiting all 490
    // links, including at non-Boolean extension points.
    let permutation_high = selectors.high_sum(0..PERMUTATION_COUNT);
    let tagged_high = (0..PERMUTATION_COUNT).fold(QM31::ZERO, |sum, block| {
        sum.add(selectors.high[block].mul_m31(M31((10 * block + 1) as u32)))
    });
    let producer_low =
        (0..ACTIVE_ROWS_PER_BLOCK - 1).fold(QM31::ZERO, |sum, local| sum.add(selectors.low[local]));
    let producer_tag_low = (0..ACTIVE_ROWS_PER_BLOCK - 1).fold(QM31::ZERO, |sum, local| {
        sum.add(selectors.low[local].mul_m31(M31(local as u32)))
    });
    let consumer_low = (0..ACTIVE_ROWS_PER_BLOCK - 1)
        .fold(QM31::ZERO, |sum, local| sum.add(selectors.low[local + 1]));
    let consumer_tag_low = (0..ACTIVE_ROWS_PER_BLOCK - 1).fold(QM31::ZERO, |sum, local| {
        sum.add(selectors.low[local + 1].mul_m31(M31(local as u32)))
    });
    weights[0] = permutation_high.mul(producer_low);
    weights[2] = permutation_high.mul(consumer_low);
    values[0] = qm31_dot(
        &[tagged_high, permutation_high, weights[0]],
        &[producer_low, producer_tag_low, pattern_values[0]],
    );
    values[2] = qm31_dot(
        &[tagged_high, permutation_high, weights[2]],
        &[consumer_low, consumer_tag_low, pattern_values[1]],
    );

    let exceptional_pattern_values = [
        exceptional_copy_pattern_dot::<0>(&exceptional, &pattern_values),
        exceptional_copy_pattern_dot::<1>(&exceptional, &pattern_values),
        exceptional_copy_pattern_dot::<2>(&exceptional, &pattern_values),
        exceptional_copy_pattern_dot::<3>(&exceptional, &pattern_values),
    ];

    for slot in 0..4 {
        let base = slot * (2 + COPY_TERMINAL_PATTERN_COUNT);
        weights[slot] = weights[slot].add(exceptional[base]);
        values[slot] = values[slot].add(exceptional[base + 1]);
        values[slot] = values[slot].add(exceptional_pattern_values[slot]);
    }
    (
        CopyLogUpRowExtension {
            producer_values: [values[0], values[1]],
            producer_weights: [weights[0], weights[1]],
            consumer_values: [values[2], values[3]],
            consumer_weights: [weights[2], weights[3]],
        },
        weights,
    )
}

#[cfg(test)]
fn copy_terminal_rows(
    selectors: &TensorSelectors,
    openings: &[QM31; STATE_AND_INTERFACE_COLUMNS + 1],
    lambda: QM31,
) -> (CopyLogUpRowExtension, [QM31; 4]) {
    copy_terminal_rows_with_powers(selectors, openings, &copy_lambda_powers(lambda))
}

#[inline(never)]
fn direct_range_copy_payloads(
    openings: &[QM31; STATE_AND_INTERFACE_COLUMNS + 1],
    lambda_powers: &[QM31; POSEIDON2_WIDTH],
) -> [QM31; 2] {
    let reconstruction_start =
        crate::direct_range_hiding_v4::DIRECT_RANGE_RECONSTRUCTION_COLUMN_START;
    [
        qm31_dot(
            &lambda_powers[..3],
            &openings[reconstruction_start..reconstruction_start + 3],
        ),
        qm31_dot(&lambda_powers[..3], &openings[..3]),
    ]
}

/// Pack the 30 bitness and three reconstruction residuals into nine QM31
/// coordinates. Each source residual is M31-valued on Boolean rows, so the
/// `(1,i,u,iu)` map is injective there. The row selector is applied once per
/// packed lane rather than once per source residual.
#[inline(never)]
fn direct_range_terminal_packed_lanes(
    openings: &[QM31; STATE_AND_INTERFACE_COLUMNS + 1],
    bit_selector: QM31,
) -> [QM31; DIRECT_RANGE_PACKED_LANE_COUNT] {
    let mut source = [QM31::ZERO; DIRECT_RANGE_SOURCE_RESIDUAL_COUNT];
    for column in 0..crate::direct_range_hiding_v4::DIRECT_RANGE_BITS_PER_ROW {
        let bit = openings[column];
        source[column] = bit.square().sub(bit);
    }
    for limb in 0..crate::direct_range_hiding_v4::DIRECT_RANGE_LIMBS_PER_ROW {
        let start = limb * crate::direct_range_hiding_v4::DIRECT_RANGE_BITS_PER_LIMB;
        let reconstructed = (0..crate::direct_range_hiding_v4::DIRECT_RANGE_BITS_PER_LIMB)
            .fold(QM31::ZERO, |sum, bit| {
                sum.add(openings[start + bit].mul_m31(M31(1 << bit)))
            });
        let committed = openings
            [crate::direct_range_hiding_v4::DIRECT_RANGE_RECONSTRUCTION_COLUMN_START + limb];
        source[crate::direct_range_hiding_v4::DIRECT_RANGE_BITS_PER_ROW + limb] =
            committed.sub(reconstructed);
    }
    core::array::from_fn(|group| {
        let start = 4 * group;
        let end = core::cmp::min(start + 4, source.len());
        bit_selector.mul(pack_base_values(&source[start..end]))
    })
}

#[derive(Clone, Copy)]
struct CopyLogUpRowExtension {
    producer_values: [QM31; 2],
    producer_weights: [QM31; 2],
    consumer_values: [QM31; 2],
    consumer_weights: [QM31; 2],
}

#[inline(never)]
fn copy_logup_residual_extension(row: CopyLogUpRowExtension, helper: QM31, chi: QM31) -> QM31 {
    let denominators = [
        chi.sub(row.producer_values[0]),
        chi.sub(row.producer_values[1]),
        chi.sub(row.consumer_values[0]),
        chi.sub(row.consumer_values[1]),
    ];

    // The cleared 2x2 LogUp numerator is
    //
    //   h*d0*d1*d2*d3 - wp0*d1*d2*d3 - wp1*d0*d2*d3
    //                    + wc0*d0*d1*d3 + wc1*d0*d1*d2.
    //
    // Group it as A*(h*B + C) - B*P, where A=d0*d1, B=d2*d3,
    // P=wp0*d1+wp1*d0, and C=wc0*d3+wc1*d2.  This is the exact same
    // polynomial over QM31 at every extension point, but uses nine generic
    // products instead of materializing five partial products and taking a
    // five-term generic dot (twelve products total).
    let product_01 = denominators[0].mul(denominators[1]);
    let product_23 = denominators[2].mul(denominators[3]);
    let producer_numerator =
        qm31_sum_products2(row.producer_weights, [denominators[1], denominators[0]]);
    let consumer_numerator =
        qm31_sum_products2(row.consumer_weights, [denominators[3], denominators[2]]);
    product_01
        .mul(helper.mul(product_23).add(consumer_numerator))
        .sub(product_23.mul(producer_numerator))
}

/// Evaluate the exact randomized constraint polynomial at an extension point.
/// This is the verifier's terminal oracle and the prover's sumcheck oracle.
pub fn evaluate_constraint_point(
    public: &SpendPublic,
    openings: &PointOpeningsV4,
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
) -> Result<QM31, ConstraintBuildError> {
    evaluate_constraint_point_with_trace(public, openings, point, lambda, chi, theta, None)
}

pub fn evaluate_constraint_point_with_trace(
    public: &SpendPublic,
    openings: &PointOpeningsV4,
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
    trace: Option<fn(u8)>,
) -> Result<QM31, ConstraintBuildError> {
    evaluate_constraint_point_internal(public, openings, point, lambda, chi, theta, trace, false)
}

/// Candidate profile-14 terminal oracle: direct 10-bit range constraints,
/// one padded copy helper, and no range helper.
pub fn evaluate_direct_range_hiding_constraint_point(
    public: &SpendPublic,
    openings: &PointOpeningsV4,
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
) -> Result<QM31, ConstraintBuildError> {
    evaluate_direct_range_hiding_constraint_point_with_trace(
        public, openings, point, lambda, chi, theta, None,
    )
}

pub fn evaluate_direct_range_hiding_constraint_point_with_trace(
    public: &SpendPublic,
    openings: &PointOpeningsV4,
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
    trace: Option<fn(u8)>,
) -> Result<QM31, ConstraintBuildError> {
    evaluate_constraint_point_internal(public, openings, point, lambda, chi, theta, trace, true)
}

#[cfg(test)]
fn dyadic_interval_selector(point: &[QM31; 10], start: usize, end: usize) -> QM31 {
    debug_assert!(start < end && end <= 1usize << point.len());
    let mut total = QM31::ZERO;
    let mut cursor = start;
    while cursor < end {
        let remaining = end - cursor;
        let mut block = if cursor == 0 {
            1usize << (usize::BITS - 1 - remaining.leading_zeros())
        } else {
            cursor & cursor.wrapping_neg()
        };
        while block > remaining {
            block >>= 1;
        }
        let free_bits = block.trailing_zeros() as usize;
        let fixed_bits = point.len() - free_bits;
        let mut weight = QM31::ONE;
        for (coordinate, value) in point[..fixed_bits].iter().enumerate() {
            let bit = (cursor >> (point.len() - 1 - coordinate)) & 1;
            weight = weight.mul(if bit == 0 {
                QM31::ONE.sub(*value)
            } else {
                *value
            });
        }
        total = total.add(weight);
        cursor += block;
    }
    total
}

fn evaluate_constraint_point_internal(
    public: &SpendPublic,
    openings: &PointOpeningsV4,
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
    trace: Option<fn(u8)>,
    direct_range_hiding: bool,
) -> Result<QM31, ConstraintBuildError> {
    let mark = |event| {
        if let Some(trace) = trace {
            trace(event);
        }
    };
    if public.fee >= VALUE_LIMIT {
        return Err(ConstraintBuildError::PublicFeeOutOfRange);
    }
    // Keep the 1,280-byte selector tensor off the SBF stack. This is also a
    // useful call-boundary anchor for the phase-specific terminal kernels.
    let selectors = Box::new(TensorSelectors::new(point));
    let block_selector = selectors.high_sum(0..PERMUTATION_COUNT);
    let mut direct_packed = Vec::with_capacity(DIRECT_RANGE_RANDOMIZED_CONSTRAINT_COUNT);
    direct_packed.resize(PACKED_BASE_CONSTRAINT_COUNT, QM31::ZERO);
    mark(0);

    evaluate_poseidon_constraints(&openings, &selectors, block_selector, &mut direct_packed);
    mark(1);

    let mut initial_high = QM31::ZERO;
    let mut weighted_domain_high = QM31::ZERO;
    let mut weighted_length_high = QM31::ZERO;
    for block in 0..PERMUTATION_COUNT {
        let schedule = permutation_block_schedule(block).expect("frozen block");
        if schedule.chunk_index == 0 {
            let expected = expected_initial_state(block);
            initial_high = initial_high.add(selectors.high[block]);
            weighted_domain_high =
                weighted_domain_high.add(selectors.high[block].mul_m31(expected[RATE]));
            weighted_length_high =
                weighted_length_high.add(selectors.high[block].mul_m31(expected[RATE + 1]));
        }
    }
    let initial_selector = initial_high.mul(selectors.low[0]);
    let weighted_domain = weighted_domain_high.mul(selectors.low[0]);
    let weighted_length = weighted_length_high.mul(selectors.low[0]);
    for lane_group in 0..POSEIDON2_WIDTH / 4 {
        let start = 4 * lane_group;
        let opened: [QM31; 4] = core::array::from_fn(|offset| openings.c1[start + offset]);
        let weighted = if start == RATE {
            [weighted_domain, weighted_length, QM31::ZERO, QM31::ZERO]
        } else {
            [QM31::ZERO; 4]
        };
        let group = INITIAL_STATE_START / 4 + lane_group;
        direct_packed[group] = direct_packed[group]
            .add(initial_selector.mul(pack_base_values(&opened)))
            .sub(pack_base_values(&weighted));
    }

    let padding_low = selectors.low[12]
        .add(selectors.low[13])
        .add(selectors.low[14])
        .add(selectors.low[15]);
    let padding_selector = block_selector.mul(padding_low);
    for column_group in 0..STATE_AND_INTERFACE_COLUMNS / 4 {
        let start = 4 * column_group;
        let opened: [QM31; 4] = core::array::from_fn(|offset| openings.c1[start + offset]);
        let group = PADDING_ZERO_START / 4 + column_group;
        direct_packed[group] =
            direct_packed[group].add(padding_selector.mul(pack_base_values(&opened)));
    }
    let short_absorption_selector = selectors.high[3]
        .add(selectors.high[48])
        .mul(selectors.low[ABSORPTION_ROW_IN_BLOCK]);
    let no_carry_high =
        selectors.high_sum((0..PERMUTATION_COUNT).filter(|block| !has_carry_payload(*block)));
    let no_carry_selector = no_carry_high.mul(selectors.low[ABSORPTION_ROW_IN_BLOCK]);
    let every_absorption_selector = block_selector.mul(selectors.low[ABSORPTION_ROW_IN_BLOCK]);
    for column_group in 0..STATE_AND_INTERFACE_COLUMNS / 4 {
        let start = 4 * column_group;
        let group = ABSORPTION_TAIL_START / 4 + column_group;
        let contribution = match column_group {
            0 => {
                let opened = [QM31::ZERO, QM31::ZERO, openings.c1[2], openings.c1[3]];
                short_absorption_selector.mul(pack_base_values(&opened))
            }
            1 => {
                let opened: [QM31; 4] = core::array::from_fn(|offset| openings.c1[start + offset]);
                short_absorption_selector.mul(pack_base_values(&opened))
            }
            2 | 3 => {
                let opened: [QM31; 4] = core::array::from_fn(|offset| openings.c1[start + offset]);
                no_carry_selector.mul(pack_base_values(&opened))
            }
            _ => {
                let opened: [QM31; 4] = core::array::from_fn(|offset| openings.c1[start + offset]);
                every_absorption_selector.mul(pack_base_values(&opened))
            }
        };
        direct_packed[group] = direct_packed[group].add(contribution);
    }

    let source_bindings = source_relation_layout();
    const SOURCE_BLOCKS: [usize; 9] = [0, 1, 44, 45, 46, 2, 3, 47, 48];
    let source_selectors: [QM31; 9] = core::array::from_fn(|index| {
        selectors.row(AUX_ABSORPTION_PRODUCER_ROW_START + SOURCE_BLOCKS[index])
    });
    let source_selector = |block: u8| {
        let index = SOURCE_BLOCKS
            .iter()
            .position(|candidate| *candidate == usize::from(block))
            .expect("frozen source block");
        source_selectors[index]
    };
    for (chunk_index, bindings) in source_bindings.chunks(4).enumerate() {
        let group = SOURCE_EQUALITY_START / 4 + chunk_index;
        let same_block = bindings
            .iter()
            .all(|binding| binding.block == bindings[0].block);
        if same_block {
            let values: [QM31; 4] = core::array::from_fn(|offset| {
                let binding = bindings[offset];
                openings.c1[usize::from(binding.left_column)]
                    .sub(openings.c1[usize::from(binding.right_column)])
            });
            let selector = source_selector(bindings[0].block);
            direct_packed[group] =
                direct_packed[group].add(selector.mul(pack_base_values(&values)));
        } else {
            for (coordinate, binding) in bindings.iter().enumerate() {
                let selector = source_selector(binding.block);
                let value = openings.c1[usize::from(binding.left_column)]
                    .sub(openings.c1[usize::from(binding.right_column)]);
                direct_packed[group] =
                    direct_packed[group].add(mul_tower_basis(selector.mul(value), coordinate));
            }
        }
    }

    let even_low = selectors.low[0]
        .add(selectors.low[2])
        .add(selectors.low[4])
        .add(selectors.low[6])
        .add(selectors.low[8])
        .add(selectors.low[10])
        .add(selectors.low[12])
        .add(selectors.low[14]);
    let merkle_selector = selectors.high[50]
        .mul(selectors.low[12].add(selectors.low[14]))
        .add(selectors.high[51].mul(even_low))
        .add(selectors.high[52].mul(even_low))
        .add(selectors.high[53].mul(selectors.low[0].add(selectors.low[2])));
    let bit = openings.c1[32];
    let mut merkle_values = Vec::with_capacity(1 + 2 * DIGEST_ELEMS);
    merkle_values.push(bit.mul(bit.sub(QM31::ONE)));
    let selections: [QM31; DIGEST_ELEMS] =
        core::array::from_fn(|limb| bit.mul(openings.c1[24 + limb].sub(openings.c1[16 + limb])));
    for limb in 0..DIGEST_ELEMS {
        let current = openings.c1[16 + limb];
        merkle_values.push(openings.c1[limb].sub(current.add(selections[limb])));
    }
    for limb in 0..DIGEST_ELEMS {
        let sibling = openings.c1[24 + limb];
        merkle_values.push(openings.c1[RATE + limb].sub(sibling.sub(selections[limb])));
    }
    for (chunk_index, values) in merkle_values[..16].chunks(4).enumerate() {
        let group = MERKLE_BIT_BOOLEAN_ID / 4 + chunk_index;
        direct_packed[group] =
            direct_packed[group].add(merkle_selector.mul(pack_base_values(values)));
    }

    let input_selector = selectors.row(INPUT_VALUE_RANGE_ROW);
    let output_selector = selectors.row(OUTPUT_VALUE_RANGE_ROW);
    let reconstruction = |values: &[QM31; STATE_AND_INTERFACE_COLUMNS + 1]| {
        values[0]
            .add(values[1].mul_m31(M31(1 << 10)))
            .add(values[2].mul_m31(M31(1 << 20)))
    };
    let reconstruction_residual = openings.c1[3].sub(reconstruction(&openings.c1));
    let balance_residual = openings.c1[3]
        .sub(openings.c1[4])
        .sub(lift(M31(public.fee)));
    let mixed_group = MERKLE_RIGHT_START.saturating_add(DIGEST_ELEMS - 1) / 4;
    debug_assert_eq!(mixed_group, INPUT_VALUE_RECONSTRUCTION_ID / 4);
    direct_packed[mixed_group] = direct_packed[mixed_group]
        .add(merkle_selector.mul(mul_tower_basis(merkle_values[16], 0)))
        .add(input_selector.mul(
            mul_tower_basis(reconstruction_residual, 1).add(mul_tower_basis(balance_residual, 3)),
        ))
        .add(output_selector.mul(mul_tower_basis(reconstruction_residual, 2)));

    for (start, block, digest) in [
        (PUBLIC_ANCHOR_START, 43usize, &public.anchor),
        (PUBLIC_NULLIFIER_START, 45usize, &public.nullifier),
        (PUBLIC_OUTPUT_START, 48usize, &public.output_commitment),
    ] {
        let selector = selectors.row(digest_row(block));
        for half in 0..2usize {
            let values: [QM31; 4] = core::array::from_fn(|offset| {
                let limb = 4 * half + offset;
                openings.c1[SECOND_ROUND_OUTPUT_COLUMN_START + limb].sub(lift(digest[limb]))
            });
            let group = start / 4 + half;
            direct_packed[group] =
                direct_packed[group].add(selector.mul(pack_base_values(&values)));
        }
    }
    let aux = witness_aux_layout();
    let asset_group = PUBLIC_INPUT_ASSET_ID / 4;
    direct_packed[asset_group] = direct_packed[asset_group]
        .add(
            selectors
                .row(usize::from(aux.input_asset_id.row))
                .mul(mul_tower_basis(
                    openings.c1[usize::from(aux.input_asset_id.column)].sub(lift(public.asset_id)),
                    0,
                )),
        )
        .add(
            selectors
                .row(AUX_ABSORPTION_PRODUCER_ROW_START + 47)
                .mul(mul_tower_basis(
                    openings.c1[34].sub(lift(public.asset_id)),
                    1,
                )),
        );
    mark(2);

    let lambda_powers = copy_lambda_powers(lambda);
    let (mut copy_row, mut copy_weights) =
        copy_terminal_rows_with_powers(&selectors, &openings.c1, &lambda_powers);
    if direct_range_hiding {
        let [reconstructed_value, source_value] =
            direct_range_copy_payloads(&openings.c1, &lambda_powers);
        let reconstructed = lift(M31(COPY_LINK_COUNT as u32 + 1)).add(reconstructed_value);
        let input_producer =
            selectors.row(crate::direct_range_hiding_v4::DIRECT_RANGE_BIT_ROW_START);
        copy_weights[0] = copy_weights[0].add(input_producer);
        copy_row.producer_values[0] =
            copy_row.producer_values[0].add(input_producer.mul(reconstructed));
        let input_consumer = selectors.row(INPUT_VALUE_RANGE_ROW);
        copy_weights[3] = copy_weights[3].add(input_consumer);
        let source = lift(M31(COPY_LINK_COUNT as u32 + 1)).add(source_value);
        copy_row.consumer_values[1] = copy_row.consumer_values[1].add(input_consumer.mul(source));

        let reconstructed = lift(M31(COPY_LINK_COUNT as u32 + 2)).add(reconstructed_value);
        let output_producer =
            selectors.row(crate::direct_range_hiding_v4::DIRECT_RANGE_BIT_ROW_START + 1);
        copy_weights[0] = copy_weights[0].add(output_producer);
        copy_row.producer_values[0] =
            copy_row.producer_values[0].add(output_producer.mul(reconstructed));
        let output_consumer = selectors.row(OUTPUT_VALUE_RANGE_ROW);
        copy_weights[2] = copy_weights[2].add(output_consumer);
        let source = lift(M31(COPY_LINK_COUNT as u32 + 2)).add(source_value);
        copy_row.consumer_values[0] = copy_row.consumer_values[0].add(output_consumer.mul(source));
        copy_row.producer_weights = [copy_weights[0], copy_weights[1]];
        copy_row.consumer_weights = [copy_weights[2], copy_weights[3]];
    }
    let mut copy_residual = copy_logup_residual_extension(copy_row, openings.c2[0], chi);
    let (direct_range_bit_selector, copy_helper_padding_selector) = if direct_range_hiding {
        selectors.direct_range_and_copy_padding()
    } else {
        (QM31::ZERO, QM31::ZERO)
    };
    if direct_range_hiding {
        copy_residual = QM31::ONE
            .sub(copy_helper_padding_selector)
            .mul(copy_residual);
    }
    mark(3);

    // The nine-lane direct-range terminal is 144 bytes.  Keep it off the
    // already dense SBF frame so the radix-eight evaluator call has a clean
    // frame boundary.
    let (direct_range_packed, range_residual) = if direct_range_hiding {
        (
            Box::new(direct_range_terminal_packed_lanes(
                &openings.c1,
                direct_range_bit_selector,
            )),
            QM31::ZERO,
        )
    } else {
        let producer_selector = input_selector.add(output_selector);
        let range_row = RangeLogUpRowExtension {
            producer_values: [openings.c1[0], openings.c1[1], openings.c1[2]],
            producer_weights: [producer_selector; 3],
            consumer_value: point
                .iter()
                .enumerate()
                .fold(QM31::ZERO, |sum, (coordinate, value)| {
                    sum.add(value.mul_m31(M31(1u32 << (9 - coordinate))))
                }),
            consumer_weight: openings.c1[MULTIPLICITY_COLUMN],
        };
        (
            Box::new([QM31::ZERO; DIRECT_RANGE_PACKED_LANE_COUNT]),
            range_logup_residual_extension(range_row, openings.c2[1], chi),
        )
    };
    mark(4);

    // Reverse Horner is exactly sum_i randomized[i] * theta^i. The direct-range
    // profile appends nine injectively packed lanes after the copy LogUp,
    // yielding one degree-72 polynomial instead of a nested degree-96 shape.
    let composition = if direct_range_hiding {
        compose_direct_range_terminal_packed_residuals_radix8(
            &mut direct_packed,
            copy_residual,
            direct_range_packed.as_ref(),
            theta,
        )
    } else {
        compose_terminal_packed_residuals(&direct_packed, copy_residual, range_residual, theta)
    };
    mark(5);
    Ok(composition)
}

pub fn payment_terminal_value(
    public: &SpendPublic,
    openings: &PointOpeningsV4,
    point: &[QM31; 10],
    batching: &PaymentConstraintChallenges,
    lambda: QM31,
    chi: QM31,
) -> Result<QM31, ConstraintBuildError> {
    payment_terminal_value_with_trace(public, openings, point, batching, lambda, chi, None)
}

pub fn payment_terminal_value_with_trace(
    public: &SpendPublic,
    openings: &PointOpeningsV4,
    point: &[QM31; 10],
    batching: &PaymentConstraintChallenges,
    lambda: QM31,
    chi: QM31,
    trace: Option<fn(u8)>,
) -> Result<QM31, ConstraintBuildError> {
    let equality =
        batching
            .zerocheck_point
            .iter()
            .zip(point)
            .fold(QM31::ONE, |product, (left, right)| {
                product.mul(
                    left.mul(*right)
                        .add(QM31::ONE.sub(*left).mul(QM31::ONE.sub(*right))),
                )
            });
    let composition = evaluate_constraint_point_with_trace(
        public,
        openings,
        point,
        lambda,
        chi,
        batching.theta,
        trace,
    )?;
    Ok(equality
        .mul(composition)
        .add(batching.mu.mul(openings.c2[0]))
        .add(batching.mu.square().mul(openings.c2[1])))
}

/// Unmasked payment terminal for the direct-range hiding profile. Only the
/// surviving copy helper belongs to the statement claim; C2 slot one is the
/// independent committed masking oracle.
pub fn direct_range_hiding_payment_terminal_value(
    public: &SpendPublic,
    openings: &DirectRangeHidingPointOpeningsV4,
    point: &[QM31; 10],
    batching: &PaymentConstraintChallenges,
    lambda: QM31,
    chi: QM31,
) -> Result<QM31, ConstraintBuildError> {
    direct_range_hiding_payment_terminal_value_with_trace(
        public, openings, point, batching, lambda, chi, None,
    )
}

pub fn direct_range_hiding_payment_terminal_value_with_trace(
    public: &SpendPublic,
    openings: &DirectRangeHidingPointOpeningsV4,
    point: &[QM31; 10],
    batching: &PaymentConstraintChallenges,
    lambda: QM31,
    chi: QM31,
    trace: Option<fn(u8)>,
) -> Result<QM31, ConstraintBuildError> {
    let constraint_openings = openings.constraint_openings();
    let equality =
        batching
            .zerocheck_point
            .iter()
            .zip(point)
            .fold(QM31::ONE, |product, (left, right)| {
                product.mul(
                    left.mul(*right)
                        .add(QM31::ONE.sub(*left).mul(QM31::ONE.sub(*right))),
                )
            });
    let composition = evaluate_direct_range_hiding_constraint_point_with_trace(
        public,
        &constraint_openings,
        point,
        lambda,
        chi,
        batching.theta,
        trace,
    )?;
    Ok(equality.mul(composition).add(batching.mu.mul(openings.h1)))
}

/// Bound terminal of the one-mask+C1-padding construction: `H(z)+eta*F(z)`.
pub fn direct_range_hiding_masked_terminal_value(
    public: &SpendPublic,
    openings: &DirectRangeHidingPointOpeningsV4,
    point: &[QM31; 10],
    batching: &PaymentConstraintChallenges,
    lambda: QM31,
    chi: QM31,
    eta: QM31,
) -> Result<QM31, ConstraintBuildError> {
    let original =
        direct_range_hiding_payment_terminal_value(public, openings, point, batching, lambda, chi)?;
    let mask = aspis_core::statement_hiding::payment_sparse_mask_value(
        &openings.c1,
        openings.payment_mask,
        point,
    );
    Ok(mask.add(eta.mul(original)))
}

#[derive(Clone, Copy)]
struct RangeLogUpRowExtension {
    producer_values: [QM31; 3],
    producer_weights: [QM31; 3],
    consumer_value: QM31,
    consumer_weight: QM31,
}

fn range_logup_residual_extension(row: RangeLogUpRowExtension, helper: QM31, chi: QM31) -> QM31 {
    let producer_denominators = row.producer_values.map(|value| chi.sub(value));
    let consumer_denominator = chi.sub(row.consumer_value);
    let producer_product = producer_denominators
        .iter()
        .copied()
        .fold(QM31::ONE, QM31::mul);
    let mut residual = helper.mul(consumer_denominator).mul(producer_product);
    for producer in 0..3 {
        let other = producer_denominators[(producer + 1) % 3]
            .mul(producer_denominators[(producer + 2) % 3]);
        residual = residual.sub(
            consumer_denominator
                .mul(other)
                .mul(row.producer_weights[producer]),
        );
    }
    residual.add(producer_product.mul(row.consumer_weight))
}

fn expected_initial_state(block: usize) -> [M31; POSEIDON2_WIDTH] {
    let schedule = permutation_block_schedule(block).expect("valid permutation block");
    let (domain, input_len) = match schedule.invocation {
        crate::trace_v4::HashInvocationKind::OwnerKey => (crate::spend::DOMAIN_OWNER_KEY, 8),
        crate::trace_v4::HashInvocationKind::Note => (crate::spend::DOMAIN_NOTE, 18),
        crate::trace_v4::HashInvocationKind::MerkleLevel(_) => {
            (crate::spend::DOMAIN_MERKLE_NODE, 16)
        }
        crate::trace_v4::HashInvocationKind::Nullifier => (crate::spend::DOMAIN_NULLIFIER, 16),
        crate::trace_v4::HashInvocationKind::Output => (crate::spend::DOMAIN_NOTE, 18),
    };
    let mut state = [M31::ZERO; POSEIDON2_WIDTH];
    state[RATE] = domain;
    state[RATE + 1] = M31(input_len);
    state
}

fn absorption_column_must_be_zero(block: usize, column: usize) -> bool {
    let schedule = permutation_block_schedule(block).expect("valid permutation block");
    if column < RATE {
        column >= usize::from(schedule.absorbed_len)
    } else if column < POSEIDON2_WIDTH {
        !has_carry_payload(block)
    } else {
        true
    }
}

fn digest_row(block: usize) -> usize {
    block * BLOCK_ROWS + ACTIVE_ROWS_PER_BLOCK - 1
}

/// Evaluate all 252 row constraints once, sharing the two Poseidon rounds.
#[cfg(not(target_os = "solana"))]
pub fn evaluate_constraint_row(
    context: &ConstraintContextV4<'_>,
    row: usize,
) -> Result<[QM31; CONSTRAINT_COUNT], ConstraintBuildError> {
    if row >= TRACE_ROWS
        || context
            .trace
            .c1
            .iter()
            .any(|column| column.len() != TRACE_ROWS)
        || context.helpers.h1.len() != TRACE_ROWS
        || context.helpers.h2.len() != TRACE_ROWS
        || context.helpers.copy_rows.len() != TRACE_ROWS
        || context.helpers.range_rows.len() != TRACE_ROWS
    {
        return Err(ConstraintBuildError::Shape);
    }
    if context.public.fee >= VALUE_LIMIT {
        return Err(ConstraintBuildError::PublicFeeOutOfRange);
    }
    let trace = context.trace;
    let mut residuals = [QM31::ZERO; CONSTRAINT_COUNT];

    if is_poseidon_active_row(row) {
        let local_row = row % BLOCK_ROWS;
        let mut input = core::array::from_fn(|lane| trace.c1[INTERFACE_COLUMN_START + lane][row]);
        if local_row == 0 {
            let absorption_row = row + ABSORPTION_ROW_IN_BLOCK;
            for lane in 0..RATE {
                input[lane] = input[lane].add(trace.c1[lane][absorption_row]);
            }
        }
        let first = evaluate_trace_round(input, 2 * local_row, local_row == 0)
            .ok_or(ConstraintBuildError::Shape)?;
        let second_input =
            core::array::from_fn(|lane| trace.c1[FIRST_ROUND_OUTPUT_COLUMN_START + lane][row]);
        let second = evaluate_trace_round(second_input, 2 * local_row + 1, false)
            .ok_or(ConstraintBuildError::Shape)?;
        for lane in 0..POSEIDON2_WIDTH {
            residuals[POSEIDON_FIRST_START + lane] =
                lift(trace.c1[FIRST_ROUND_OUTPUT_COLUMN_START + lane][row].sub(first[lane]));
            residuals[POSEIDON_SECOND_START + lane] =
                lift(trace.c1[SECOND_ROUND_OUTPUT_COLUMN_START + lane][row].sub(second[lane]));
        }
        if local_row == 0 {
            let block = row / BLOCK_ROWS;
            let schedule = permutation_block_schedule(block).ok_or(ConstraintBuildError::Shape)?;
            if schedule.chunk_index == 0 {
                let expected = expected_initial_state(block);
                for lane in 0..POSEIDON2_WIDTH {
                    residuals[INITIAL_STATE_START + lane] =
                        lift(trace.c1[INTERFACE_COLUMN_START + lane][row].sub(expected[lane]));
                }
            }
        }
    }

    if is_poseidon_padding_row(row) {
        for column in 0..STATE_AND_INTERFACE_COLUMNS {
            residuals[PADDING_ZERO_START + column] = lift(trace.c1[column][row]);
        }
    }
    if row < PERMUTATION_COUNT * BLOCK_ROWS && row % BLOCK_ROWS == ABSORPTION_ROW_IN_BLOCK {
        let block = row / BLOCK_ROWS;
        for column in 0..STATE_AND_INTERFACE_COLUMNS {
            if absorption_column_must_be_zero(block, column) {
                residuals[ABSORPTION_TAIL_START + column] = lift(trace.c1[column][row]);
            }
        }
    }

    for (binding_index, binding) in source_relation_layout().into_iter().enumerate() {
        if row == AUX_ABSORPTION_PRODUCER_ROW_START + usize::from(binding.block) {
            residuals[SOURCE_EQUALITY_START + binding_index] = lift(
                trace.c1[usize::from(binding.left_column)][row]
                    .sub(trace.c1[usize::from(binding.right_column)][row]),
            );
        }
    }

    for binding in merkle_boundary_layout() {
        if row != usize::from(binding.source_row) {
            continue;
        }
        let bit = read_cell(trace, binding.path_bit);
        residuals[MERKLE_BIT_BOOLEAN_ID] = lift(bit.mul(bit.sub(M31::ONE)));
        for limb in 0..DIGEST_ELEMS {
            let current = read_cell(trace, binding.current[limb]);
            let sibling = read_cell(trace, binding.sibling[limb]);
            let left_expected = current.add(bit.mul(sibling.sub(current)));
            let right_expected = sibling.add(bit.mul(current.sub(sibling)));
            residuals[MERKLE_LEFT_START + limb] =
                lift(read_cell(trace, binding.left[limb]).sub(left_expected));
            residuals[MERKLE_RIGHT_START + limb] =
                lift(read_cell(trace, binding.right[limb]).sub(right_expected));
        }
    }

    let aux = witness_aux_layout();
    if row == INPUT_VALUE_RANGE_ROW {
        let reconstructed = read_cell(trace, aux.input_value_limbs[0])
            .add(read_cell(trace, aux.input_value_limbs[1]).mul(M31(1 << 10)))
            .add(read_cell(trace, aux.input_value_limbs[2]).mul(M31(1 << 20)));
        residuals[INPUT_VALUE_RECONSTRUCTION_ID] =
            lift(read_cell(trace, aux.input_value_reconstruction).sub(reconstructed));
        residuals[BALANCE_ID] = lift(
            read_cell(trace, aux.input_value_reconstruction)
                .sub(read_cell(trace, aux.output_value_for_balance))
                .sub(M31(context.public.fee)),
        );
    }
    if row == OUTPUT_VALUE_RANGE_ROW {
        let reconstructed = read_cell(trace, aux.output_value_limbs[0])
            .add(read_cell(trace, aux.output_value_limbs[1]).mul(M31(1 << 10)))
            .add(read_cell(trace, aux.output_value_limbs[2]).mul(M31(1 << 20)));
        residuals[OUTPUT_VALUE_RECONSTRUCTION_ID] =
            lift(read_cell(trace, aux.output_value_reconstruction).sub(reconstructed));
    }

    let public_bindings = [
        (PUBLIC_ANCHOR_START, 43usize, &context.public.anchor),
        (PUBLIC_NULLIFIER_START, 45usize, &context.public.nullifier),
        (
            PUBLIC_OUTPUT_START,
            48usize,
            &context.public.output_commitment,
        ),
    ];
    for (start, block, public_digest) in public_bindings {
        if row == digest_row(block) {
            for limb in 0..DIGEST_ELEMS {
                residuals[start + limb] = lift(
                    trace.c1[SECOND_ROUND_OUTPUT_COLUMN_START + limb][row].sub(public_digest[limb]),
                );
            }
        }
    }
    if row == usize::from(aux.input_asset_id.row) {
        residuals[PUBLIC_INPUT_ASSET_ID] =
            lift(read_cell(trace, aux.input_asset_id).sub(context.public.asset_id));
    }
    let output_asset = TraceCell {
        row: (AUX_ABSORPTION_PRODUCER_ROW_START + 47) as u16,
        column: 34,
    };
    if row == usize::from(output_asset.row) {
        residuals[PUBLIC_OUTPUT_ASSET_ID] =
            lift(read_cell(trace, output_asset).sub(context.public.asset_id));
    }

    residuals[COPY_LOGUP_ID] = copy_logup_residual(
        context.helpers.copy_rows[row],
        context.helpers.h1[row],
        context.chi,
    );
    residuals[RANGE_LOGUP_ID] = range_logup_residual(
        context.helpers.range_rows[row],
        context.helpers.h2[row],
        context.chi,
    );
    Ok(residuals)
}

#[cfg(not(target_os = "solana"))]
pub fn compose_constraint_row(
    context: &ConstraintContextV4<'_>,
    row: usize,
    theta: QM31,
) -> Result<QM31, ConstraintBuildError> {
    let residuals = evaluate_constraint_row(context, row)?;
    Ok(compose_randomized_residuals(&residuals, None, theta))
}

#[cfg(not(target_os = "solana"))]
pub fn constraint_composition_table(
    context: &ConstraintContextV4<'_>,
    theta: QM31,
) -> Result<Vec<QM31>, ConstraintBuildError> {
    (0..TRACE_ROWS)
        .map(|row| compose_constraint_row(context, row, theta))
        .collect()
}

/// Boolean-row reference table for profile 14. This deliberately reuses the
/// original row evaluator for the 250 unchanged constraints, then replaces
/// the two helper slots with the padded-copy and direct-range rules. It is the
/// independent reference for the new terminal oracle.
#[cfg(not(target_os = "solana"))]
pub fn direct_range_hiding_composition_table(
    public: &SpendPublic,
    trace: &SpendTraceV4,
    helpers: &crate::direct_range_hiding_v4::DirectRangeHidingHelpersV4,
    chi: QM31,
    theta: QM31,
) -> Result<Vec<QM31>, ConstraintBuildError> {
    if helpers.copy_rows.len() != TRACE_ROWS || helpers.h1.len() != TRACE_ROWS {
        return Err(ConstraintBuildError::Shape);
    }
    let empty_range = RangeLogUpRow {
        producer_values: [QM31::ZERO; 3],
        producer_weights: [M31::ZERO; 3],
        consumer_value: QM31::ZERO,
        consumer_weight: M31::ZERO,
    };
    let adapter = PaymentHelpersV4 {
        copy_rows: helpers.copy_rows.clone(),
        range_rows: vec![empty_range; TRACE_ROWS],
        h1: helpers.h1.clone(),
        h2: vec![QM31::ZERO; TRACE_ROWS],
    };
    let context = ConstraintContextV4 {
        public,
        trace,
        helpers: &adapter,
        chi,
    };
    let direct_base_adjustments = [QM31::ZERO; PACKED_BASE_CONSTRAINT_COUNT];
    (0..TRACE_ROWS)
        .map(|row| {
            let mut residuals = evaluate_constraint_row(&context, row)?;
            if row >= crate::direct_range_hiding_v4::COPY_HELPER_PADDING_ROW_START {
                residuals[COPY_LOGUP_ID] = QM31::ZERO;
            }
            residuals[RANGE_LOGUP_ID] = QM31::ZERO;
            let mut direct_source = [QM31::ZERO; DIRECT_RANGE_SOURCE_RESIDUAL_COUNT];
            if (crate::direct_range_hiding_v4::DIRECT_RANGE_BIT_ROW_START
                ..crate::direct_range_hiding_v4::COPY_HELPER_PADDING_ROW_START)
                .contains(&row)
            {
                for column in 0..crate::direct_range_hiding_v4::DIRECT_RANGE_BITS_PER_ROW {
                    let bit = trace.c1[column][row];
                    direct_source[column] = lift(bit.mul(bit).sub(bit));
                }
                for limb in 0..crate::direct_range_hiding_v4::DIRECT_RANGE_LIMBS_PER_ROW {
                    let start = limb * crate::direct_range_hiding_v4::DIRECT_RANGE_BITS_PER_LIMB;
                    let reconstructed = (0
                        ..crate::direct_range_hiding_v4::DIRECT_RANGE_BITS_PER_LIMB)
                        .fold(M31::ZERO, |sum, bit| {
                            sum.add(trace.c1[start + bit][row].mul(M31(1 << bit)))
                        });
                    let committed = trace.c1
                        [crate::direct_range_hiding_v4::DIRECT_RANGE_RECONSTRUCTION_COLUMN_START
                            + limb][row];
                    direct_source
                        [crate::direct_range_hiding_v4::DIRECT_RANGE_BITS_PER_ROW + limb] =
                        lift(committed.sub(reconstructed));
                }
            }
            let direct_range_packed = core::array::from_fn(|group| {
                let start = 4 * group;
                let end = core::cmp::min(start + 4, direct_source.len());
                pack_base_values(&direct_source[start..end])
            });
            Ok(compose_direct_range_randomized_residuals(
                &residuals,
                &direct_base_adjustments,
                &direct_range_packed,
                theta,
            ))
        })
        .collect()
}

pub fn helper_sums(helpers: &PaymentHelpersV4) -> Result<[QM31; 2], ConstraintBuildError> {
    if helpers.h1.len() != TRACE_ROWS || helpers.h2.len() != TRACE_ROWS {
        return Err(ConstraintBuildError::Shape);
    }
    Ok([
        helpers.h1.iter().copied().fold(QM31::ZERO, QM31::add),
        helpers.h2.iter().copied().fold(QM31::ZERO, QM31::add),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spend::{
        derive_nullifier, derive_owner_key, merkle_root, note_commitment, output_commitment,
        MerklePath, SpendWitness,
    };
    use crate::trace_v4::build_spend_trace_v4;

    fn digest(seed: u32) -> [M31; DIGEST_ELEMS] {
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
            siblings: (0..20).map(|level| digest(1_000 + level * 29)).collect(),
            index: 0x5_4321,
        };
        let anchor = merkle_root(note, &path).unwrap();
        let nullifier = derive_nullifier(&nullifier_key, &input_salt);
        let output = output_commitment(&output_owner_key, value_out, asset_id, &output_salt);
        (
            SpendPublic {
                anchor,
                nullifier,
                output_commitment: output,
                asset_id,
                fee,
            },
            SpendWitness {
                nullifier_key,
                input_salt,
                output_salt,
                output_owner_key,
                input_asset_id: asset_id,
                value,
                value_out,
                merkle_path: path,
            },
        )
    }

    fn challenge(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed + 1), M31(seed + 3)),
            c1: CM31::new(M31(seed + 5), M31(seed + 7)),
        }
    }

    fn boolean_point(row: usize) -> [QM31; 10] {
        core::array::from_fn(|coordinate| {
            if (row >> (9 - coordinate)) & 1 == 0 {
                QM31::ZERO
            } else {
                QM31::ONE
            }
        })
    }

    fn external_linear_extension_reference(state: &mut [QM31; POSEIDON2_WIDTH]) {
        for values in state.chunks_exact_mut(4) {
            let input: [QM31; 4] = values.try_into().unwrap();
            values.copy_from_slice(&[
                input[0]
                    .add(input[0])
                    .add(input[1].mul_m31(M31(3)))
                    .add(input[2])
                    .add(input[3]),
                input[0]
                    .add(input[1].add(input[1]))
                    .add(input[2].mul_m31(M31(3)))
                    .add(input[3]),
                input[0]
                    .add(input[1])
                    .add(input[2].add(input[2]))
                    .add(input[3].mul_m31(M31(3))),
                input[0]
                    .mul_m31(M31(3))
                    .add(input[1])
                    .add(input[2])
                    .add(input[3].add(input[3])),
            ]);
        }
        let sums: [QM31; 4] = core::array::from_fn(|column| {
            (0..4).fold(QM31::ZERO, |sum, row| sum.add(state[row * 4 + column]))
        });
        for (index, value) in state.iter_mut().enumerate() {
            *value = value.add(sums[index & 3]);
        }
    }

    fn internal_linear_extension_reference(state: &mut [QM31; POSEIDON2_WIDTH]) {
        const SHIFTS: [u8; 15] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16];
        let part_sum = state[1..].iter().copied().fold(QM31::ZERO, QM31::add);
        let full_sum = part_sum.add(state[0]);
        state[0] = part_sum.sub(state[0]);
        for lane in 1..POSEIDON2_WIDTH {
            state[lane] = full_sum.add(state[lane].mul_m31(M31(1u32 << SHIFTS[lane - 1])));
        }
    }

    #[test]
    fn lazy_extension_poseidon_linear_layers_match_reference_off_domain() {
        for seed in 1..=64u32 {
            let state = core::array::from_fn(|lane| challenge(seed * 1_003 + lane as u32 * 97));
            let mut expected = state;
            let mut actual = state;
            external_linear_extension_reference(&mut expected);
            external_linear_extension(&mut actual);
            assert_eq!(actual, expected, "external seed={seed}");

            let mut expected = state;
            let mut actual = state;
            internal_linear_extension_reference(&mut expected);
            internal_linear_extension(&mut actual);
            assert_eq!(actual, expected, "internal seed={seed}");
        }
    }

    fn poseidon_openings(seed: u32) -> PointOpeningsV4 {
        PointOpeningsV4 {
            c1: core::array::from_fn(|column| challenge(seed + 17 * column as u32)),
            c1_xor11: core::array::from_fn(|column| challenge(seed + 10_003 + 19 * column as u32)),
            c2: [challenge(seed + 20_003), challenge(seed + 20_021)],
        }
    }

    fn affine_poseidon_openings(seed: u32, value: QM31) -> PointOpeningsV4 {
        let affine = |offset: u32, index: usize| {
            challenge(seed + offset + 29 * index as u32)
                .add(value.mul(challenge(seed + offset + 10_003 + 31 * index as u32)))
        };
        PointOpeningsV4 {
            c1: core::array::from_fn(|column| affine(0, column)),
            c1_xor11: core::array::from_fn(|column| affine(30_007, column)),
            c2: [affine(60_013, 0), affine(60_013, 1)],
        }
    }

    #[test]
    fn merged_full_second_round_matches_old_air_on_all_boolean_rows() {
        for row in 0..TRACE_ROWS {
            let point = boolean_point(row);
            let selectors = TensorSelectors::new(&point);
            let block_selector = selectors.high_sum(0..PERMUTATION_COUNT);
            let openings = poseidon_openings(100_000 + row as u32 * 101);
            let mut expected = [QM31::ZERO; PACKED_BASE_CONSTRAINT_COUNT];
            let mut actual = [QM31::ZERO; PACKED_BASE_CONSTRAINT_COUNT];
            evaluate_poseidon_constraints_reference(
                &openings,
                &selectors,
                block_selector,
                &mut expected,
            );
            evaluate_poseidon_constraints(&openings, &selectors, block_selector, &mut actual);
            assert_eq!(actual, expected, "Boolean row {row}");
        }
    }

    #[test]
    fn merged_full_second_round_stays_within_the_sumcheck_degree_wire() {
        assert_eq!(POSEIDON_PREPROCESSED_INDIVIDUAL_DEGREE, 6);
        assert!(
            POSEIDON_PREPROCESSED_INDIVIDUAL_DEGREE
                < aspis_core::statement_sumcheck::PAYMENT_SUMCHECK_FULL_COEFFICIENTS
        );

        // Restrict every point coordinate and every opening to an arbitrary
        // affine line. Seven forward differences must vanish for an
        // individual-degree-six polynomial. This tests the actual compiled
        // evaluator, including selector interpolation and residual packing.
        for coordinate in 0..10 {
            let base_point = core::array::from_fn(|index| {
                challenge(400_000 + coordinate as u32 * 1_003 + index as u32 * 37)
            });
            let mut evaluations = Vec::new();
            for sample in 0..=POSEIDON_PREPROCESSED_INDIVIDUAL_DEGREE + 1 {
                let value = lift(M31(sample as u32));
                let mut point = base_point;
                point[coordinate] = value;
                let selectors = TensorSelectors::new(&point);
                let block_selector = selectors.high_sum(0..PERMUTATION_COUNT);
                let openings =
                    affine_poseidon_openings(500_000 + coordinate as u32 * 70_001, value);
                let mut packed = [QM31::ZERO; PACKED_BASE_CONSTRAINT_COUNT];
                evaluate_poseidon_constraints(&openings, &selectors, block_selector, &mut packed);
                evaluations.push(packed);
            }
            for _ in 0..=POSEIDON_PREPROCESSED_INDIVIDUAL_DEGREE {
                evaluations = evaluations
                    .windows(2)
                    .map(|pair| core::array::from_fn(|index| pair[1][index].sub(pair[0][index])))
                    .collect();
            }
            assert_eq!(evaluations.len(), 1);
            assert!(
                evaluations[0].iter().all(|value| *value == QM31::ZERO),
                "coordinate {coordinate} exceeded individual degree six"
            );
        }
    }

    fn reference_copy_terminal_rows(
        selectors: &TensorSelectors,
        openings: &[QM31; STATE_AND_INTERFACE_COLUMNS + 1],
        lambda: QM31,
    ) -> CopyLogUpRowExtension {
        let mut powers = [QM31::ZERO; POSEIDON2_WIDTH];
        let mut power = lambda;
        for output in &mut powers {
            *output = power;
            power = power.mul(lambda);
        }
        let mut pattern_values = [QM31::ZERO; COPY_TERMINAL_PATTERN_COUNT];
        for (pattern_index, output) in pattern_values.iter_mut().enumerate() {
            for (limb, column) in copy_terminal_pattern(pattern_index).into_iter().enumerate() {
                if column >= 0 {
                    *output = output.add(powers[limb].mul(openings[column as usize]));
                }
            }
        }
        let mut weights = [QM31::ZERO; 4];
        let mut values = [QM31::ZERO; 4];
        visit_copy_terminal_links(|link| {
            for (slot, row, pattern) in [
                (
                    usize::from(link.producer_slot),
                    usize::from(link.producer_row),
                    usize::from(link.producer_pattern),
                ),
                (
                    2usize,
                    usize::from(link.consumer_row),
                    usize::from(link.consumer_pattern),
                ),
            ] {
                let selector = selectors.row(row);
                weights[slot] = weights[slot].add(selector);
                values[slot] =
                    values[slot].add(selector.mul(lift(link.tag).add(pattern_values[pattern])));
            }
        });
        CopyLogUpRowExtension {
            producer_values: [values[0], values[1]],
            producer_weights: [weights[0], weights[1]],
            consumer_values: [values[2], values[3]],
            consumer_weights: [weights[2], weights[3]],
        }
    }

    fn reference_copy_logup_residual_extension(
        row: CopyLogUpRowExtension,
        helper: QM31,
        chi: QM31,
    ) -> QM31 {
        let denominators = [
            chi.sub(row.producer_values[0]),
            chi.sub(row.producer_values[1]),
            chi.sub(row.consumer_values[0]),
            chi.sub(row.consumer_values[1]),
        ];
        let product_without = |excluded: usize| {
            (0..4)
                .filter(|&index| index != excluded)
                .fold(QM31::ONE, |product, index| product.mul(denominators[index]))
        };
        let all = denominators.iter().copied().fold(QM31::ONE, QM31::mul);
        helper
            .mul(all)
            .sub(product_without(0).mul(row.producer_weights[0]))
            .sub(product_without(1).mul(row.producer_weights[1]))
            .add(product_without(2).mul(row.consumer_weights[0]))
            .add(product_without(3).mul(row.consumer_weights[1]))
    }

    fn reference_direct_range_copy_payloads(
        openings: &[QM31; STATE_AND_INTERFACE_COLUMNS + 1],
        lambda: QM31,
    ) -> [QM31; 2] {
        let start = crate::direct_range_hiding_v4::DIRECT_RANGE_RECONSTRUCTION_COLUMN_START;
        let evaluate = |columns: core::ops::Range<usize>| {
            let mut power = lambda;
            columns.fold(QM31::ZERO, |sum, column| {
                let result = sum.add(power.mul(openings[column]));
                power = power.mul(lambda);
                result
            })
        };
        [evaluate(start..start + 3), evaluate(0..3)]
    }

    #[test]
    fn tensor_factored_copy_terminal_matches_link_stream_off_domain() {
        for seed in [400u32, 800, 1_200] {
            let point = core::array::from_fn(|coordinate| challenge(seed + 31 * coordinate as u32));
            let selectors = TensorSelectors::new(&point);
            assert_eq!(
                evaluate_exceptional_copy_routing_direct(&selectors),
                evaluate_exceptional_copy_routing(&selectors),
            );
            let openings =
                core::array::from_fn(|column| challenge(seed + 101 + 13 * column as u32));
            let lambda = challenge(seed + 2_000);
            let (optimized, _) = copy_terminal_rows(&selectors, &openings, lambda);
            let reference = reference_copy_terminal_rows(&selectors, &openings, lambda);
            assert_eq!(optimized.producer_values, reference.producer_values);
            assert_eq!(optimized.producer_weights, reference.producer_weights);
            assert_eq!(optimized.consumer_values, reference.consumer_values);
            assert_eq!(optimized.consumer_weights, reference.consumer_weights);
            let helper = challenge(seed + 3_000);
            let chi = challenge(seed + 4_000);
            assert_eq!(
                copy_logup_residual_extension(optimized, helper, chi),
                reference_copy_logup_residual_extension(reference, helper, chi),
            );
        }
    }

    fn random_m31(random: &mut impl std::io::Read) -> M31 {
        loop {
            let mut bytes = [0u8; 4];
            random.read_exact(&mut bytes).expect("OS random source");
            let candidate = u32::from_le_bytes(bytes);
            if candidate < P {
                return M31(candidate);
            }
        }
    }

    fn random_qm31(random: &mut impl std::io::Read) -> QM31 {
        QM31 {
            c0: CM31::new(random_m31(random), random_m31(random)),
            c1: CM31::new(random_m31(random), random_m31(random)),
        }
    }

    #[test]
    fn tensor_direct_range_intervals_match_dyadic_reference_off_domain_and_at_boundaries() {
        let mut random = std::fs::File::open("/dev/urandom").expect("OS random source");
        for _ in 0..50 {
            let point = core::array::from_fn(|_| random_qm31(&mut random));
            let selectors = TensorSelectors::new(&point);
            let (direct_range, padding) = selectors.direct_range_and_copy_padding();
            assert_eq!(
                direct_range,
                dyadic_interval_selector(
                    &point,
                    crate::direct_range_hiding_v4::DIRECT_RANGE_BIT_ROW_START,
                    crate::direct_range_hiding_v4::COPY_HELPER_PADDING_ROW_START,
                )
            );
            assert_eq!(
                padding,
                dyadic_interval_selector(
                    &point,
                    crate::direct_range_hiding_v4::COPY_HELPER_PADDING_ROW_START,
                    TRACE_ROWS,
                )
            );
        }

        let bit_start = crate::direct_range_hiding_v4::DIRECT_RANGE_BIT_ROW_START;
        let padding_start = crate::direct_range_hiding_v4::COPY_HELPER_PADDING_ROW_START;
        for row in [
            bit_start - 1,
            bit_start,
            bit_start + 1,
            padding_start,
            TRACE_ROWS - 1,
        ] {
            let point = boolean_point(row);
            let (direct_range, padding) =
                TensorSelectors::new(&point).direct_range_and_copy_padding();
            assert_eq!(
                direct_range,
                if (bit_start..padding_start).contains(&row) {
                    QM31::ONE
                } else {
                    QM31::ZERO
                },
                "direct-range boundary row {row}",
            );
            assert_eq!(
                padding,
                if (padding_start..TRACE_ROWS).contains(&row) {
                    QM31::ONE
                } else {
                    QM31::ZERO
                },
                "padding boundary row {row}",
            );
        }
    }

    #[test]
    fn compiled_copy_routing_matches_independent_walk_at_50_random_qm31_points() {
        let mut random = std::fs::File::open("/dev/urandom").expect("OS random source");
        for _ in 0..50 {
            let point = core::array::from_fn(|_| random_qm31(&mut random));
            let selectors = TensorSelectors::new(&point);
            let openings = core::array::from_fn(|_| random_qm31(&mut random));
            let lambda = random_qm31(&mut random);
            let (compiled, _) = copy_terminal_rows(&selectors, &openings, lambda);
            let walked = reference_copy_terminal_rows(&selectors, &openings, lambda);
            assert_eq!(compiled.producer_values, walked.producer_values);
            assert_eq!(compiled.producer_weights, walked.producer_weights);
            assert_eq!(compiled.consumer_values, walked.consumer_values);
            assert_eq!(compiled.consumer_weights, walked.consumer_weights);
            let helper = random_qm31(&mut random);
            let chi = random_qm31(&mut random);
            assert_eq!(
                copy_logup_residual_extension(compiled, helper, chi),
                reference_copy_logup_residual_extension(walked, helper, chi),
            );
        }
    }

    #[test]
    fn generated_exceptional_pattern_support_is_exact_and_sparse() {
        let mut expected_masks = [0u16; 4];
        visit_copy_exceptional_terminal_links(|link| {
            expected_masks[usize::from(link.producer_slot)] |=
                1u16 << usize::from(link.producer_pattern);
            expected_masks[2] |= 1u16 << usize::from(link.consumer_pattern);
        });
        for (slot, support) in COPY_ROUTING_PATTERN_SUPPORTS.iter().enumerate() {
            let generated_mask = support.indices[..usize::from(support.len)]
                .iter()
                .fold(0u16, |mask, &pattern| mask | (1u16 << pattern));
            assert_eq!(generated_mask, expected_masks[slot], "slot {slot}");
            assert!(support.indices[..usize::from(support.len)]
                .windows(2)
                .all(|pair| pair[0] < pair[1]));
        }
        // A frozen cost guard: only thirteen of the forty possible
        // slot-pattern products are nonzero in the exceptional layout.
        assert_eq!(
            COPY_ROUTING_PATTERN_SUPPORTS.map(|support| support.len),
            [7, 1, 5, 0]
        );
    }

    #[test]
    fn compiled_copy_routing_matches_padding_lambda_zero_and_cross_vectors() {
        let mut points = Vec::new();
        for block in [0usize, 3, 24, 48] {
            for local in 12usize..16 {
                points.push(boolean_point(block * BLOCK_ROWS + local));
            }
        }
        points.push(core::array::from_fn(|coordinate| {
            challenge(9_000 + 19 * coordinate as u32)
        }));

        let mut opening_vectors = Vec::new();
        opening_vectors.push([QM31::ZERO; STATE_AND_INTERFACE_COLUMNS + 1]);
        for column in 0..STATE_AND_INTERFACE_COLUMNS + 1 {
            let mut unit = [QM31::ZERO; STATE_AND_INTERFACE_COLUMNS + 1];
            unit[column] = challenge(10_000 + column as u32);
            opening_vectors.push(unit);
        }
        let mut cross = [QM31::ZERO; STATE_AND_INTERFACE_COLUMNS + 1];
        for (left, right, value) in [
            (0usize, 32usize, challenge(11_001)),
            (3, 33, challenge(11_101)),
            (8, 16, challenge(11_201)),
            (4, 34, challenge(11_301)),
        ] {
            cross[left] = value;
            cross[right] = value.neg();
        }
        opening_vectors.push(cross);

        for point in points {
            let selectors = TensorSelectors::new(&point);
            for openings in &opening_vectors {
                for lambda in [QM31::ZERO, QM31::ONE, challenge(12_000)] {
                    let (compiled, _) = copy_terminal_rows(&selectors, openings, lambda);
                    let walked = reference_copy_terminal_rows(&selectors, openings, lambda);
                    assert_eq!(compiled.producer_values, walked.producer_values);
                    assert_eq!(compiled.producer_weights, walked.producer_weights);
                    assert_eq!(compiled.consumer_values, walked.consumer_values);
                    assert_eq!(compiled.consumer_weights, walked.consumer_weights);
                    assert_eq!(
                        direct_range_copy_payloads(openings, &copy_lambda_powers(lambda)),
                        reference_direct_range_copy_payloads(openings, lambda),
                    );
                    let helper = challenge(13_000);
                    let chi = challenge(14_000);
                    assert_eq!(
                        copy_logup_residual_extension(compiled, helper, chi),
                        reference_copy_logup_residual_extension(walked, helper, chi),
                    );
                }
            }
        }
    }

    fn matrix_rank(mut matrix: Vec<Vec<M31>>) -> usize {
        let rows = matrix.len();
        let columns = matrix[0].len();
        let mut rank = 0usize;
        for column in 0..columns {
            let Some(pivot) = (rank..rows).find(|&row| matrix[row][column] != M31::ZERO) else {
                continue;
            };
            matrix.swap(rank, pivot);
            let inverse = matrix[rank][column].inv();
            for entry in column..columns {
                matrix[rank][entry] = matrix[rank][entry].mul(inverse);
            }
            for row in 0..rows {
                if row == rank || matrix[row][column] == M31::ZERO {
                    continue;
                }
                let factor = matrix[row][column];
                for entry in column..columns {
                    matrix[row][entry] = matrix[row][entry].sub(factor.mul(matrix[rank][entry]));
                }
            }
            rank += 1;
        }
        rank
    }

    fn outer_factor_support(mut matrix: Vec<Vec<M31>>) -> (usize, usize) {
        let mut rank = 0usize;
        let mut support = 0usize;
        loop {
            let pivot = (0..64).find_map(|row| {
                (0..16)
                    .find(|&column| matrix[row][column] != M31::ZERO)
                    .map(|column| (row, column))
            });
            let Some((pivot_row, pivot_column)) = pivot else {
                return (rank, support);
            };
            let inverse = matrix[pivot_row][pivot_column].inv();
            let left = (0..64)
                .map(|row| matrix[row][pivot_column])
                .collect::<Vec<_>>();
            let right = (0..16)
                .map(|column| matrix[pivot_row][column].mul(inverse))
                .collect::<Vec<_>>();
            support += left.iter().filter(|&&value| value != M31::ZERO).count();
            support += right.iter().filter(|&&value| value != M31::ZERO).count();
            for row in 0..64 {
                for column in 0..16 {
                    matrix[row][column] = matrix[row][column].sub(left[row].mul(right[column]));
                }
            }
            rank += 1;
        }
    }

    #[test]
    fn exceptional_copy_routing_has_low_tensor_rank() {
        let mut matrices =
            vec![vec![vec![M31::ZERO; 16]; 64]; 4 * (2 + COPY_TERMINAL_PATTERN_COUNT)];
        visit_copy_exceptional_terminal_links(|link| {
            for (slot, row, pattern) in [
                (
                    usize::from(link.producer_slot),
                    usize::from(link.producer_row),
                    usize::from(link.producer_pattern),
                ),
                (
                    2usize,
                    usize::from(link.consumer_row),
                    usize::from(link.consumer_pattern),
                ),
            ] {
                let block = row >> 4;
                let local = row & 15;
                matrices[slot * (2 + COPY_TERMINAL_PATTERN_COUNT)][block][local] =
                    matrices[slot * (2 + COPY_TERMINAL_PATTERN_COUNT)][block][local].add(M31::ONE);
                matrices[slot * (2 + COPY_TERMINAL_PATTERN_COUNT) + 1][block][local] = matrices
                    [slot * (2 + COPY_TERMINAL_PATTERN_COUNT) + 1][block][local]
                    .add(link.tag);
                let index = slot * (2 + COPY_TERMINAL_PATTERN_COUNT) + 2 + pattern;
                matrices[index][block][local] = matrices[index][block][local].add(M31::ONE);
            }
        });
        let ranks = matrices
            .iter()
            .cloned()
            .map(matrix_rank)
            .collect::<Vec<_>>();
        let supports = matrices
            .into_iter()
            .map(outer_factor_support)
            .collect::<Vec<_>>();
        let nonzero = ranks.iter().filter(|&&rank| rank != 0).count();
        let total = ranks.iter().sum::<usize>();
        let support = supports.iter().map(|(_, support)| support).sum::<usize>();
        assert_eq!(total, COPY_ROUTING_RANK);
        assert_eq!(support, COPY_ROUTING_EXPANDED_FACTOR_SUPPORT);
        assert_eq!(nonzero, 19);
        assert!(supports.iter().all(|(rank, _)| *rank <= 7));
    }

    #[test]
    fn inspect_copy_routing_simultaneous_subspaces() {
        let mut matrices =
            vec![vec![vec![M31::ZERO; 16]; 64]; 4 * (2 + COPY_TERMINAL_PATTERN_COUNT)];
        visit_copy_exceptional_terminal_links(|link| {
            for (slot, row, pattern) in [
                (
                    usize::from(link.producer_slot),
                    usize::from(link.producer_row),
                    usize::from(link.producer_pattern),
                ),
                (
                    2usize,
                    usize::from(link.consumer_row),
                    usize::from(link.consumer_pattern),
                ),
            ] {
                let block = row >> 4;
                let local = row & 15;
                let base = slot * (2 + COPY_TERMINAL_PATTERN_COUNT);
                matrices[base][block][local] = matrices[base][block][local].add(M31::ONE);
                matrices[base + 1][block][local] = matrices[base + 1][block][local].add(link.tag);
                matrices[base + 2 + pattern][block][local] =
                    matrices[base + 2 + pattern][block][local].add(M31::ONE);
            }
        });
        for slot in 0..4 {
            let base = slot * (2 + COPY_TERMINAL_PATTERN_COUNT);
            let left = (0..64)
                .map(|row| {
                    (0..2 + COPY_TERMINAL_PATTERN_COUNT)
                        .flat_map(|matrix| matrices[base + matrix][row].iter().copied())
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let right = (0..2 + COPY_TERMINAL_PATTERN_COUNT)
                .flat_map(|matrix| matrices[base + matrix].iter().cloned())
                .collect::<Vec<_>>();
            let local_slice_rank = (0..16)
                .map(|local| {
                    (0..2 + COPY_TERMINAL_PATTERN_COUNT)
                        .map(|matrix| {
                            (0..64)
                                .map(|block| matrices[base + matrix][block][local])
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>()
                })
                .map(matrix_rank)
                .sum::<usize>();
            let block_slice_rank = (0..64)
                .map(|block| {
                    (0..2 + COPY_TERMINAL_PATTERN_COUNT)
                        .map(|matrix| matrices[base + matrix][block].clone())
                        .collect::<Vec<_>>()
                })
                .map(matrix_rank)
                .sum::<usize>();
            std::println!(
                "slot {slot}: common_left={} common_right={} local_basis_rank={} block_basis_rank={}",
                matrix_rank(left),
                matrix_rank(right),
                local_slice_rank,
                block_slice_rank,
            );
        }
        let lefts = COPY_ROUTING_FACTORIZATION
            .left_factors
            .iter()
            .map(|factor| {
                let start = usize::from(factor.start);
                COPY_ROUTING_FACTORIZATION.entries[start..start + usize::from(factor.len)]
                    .iter()
                    .map(|entry| (entry.index, entry.coefficient))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let rights = COPY_ROUTING_FACTORIZATION
            .right_factors
            .iter()
            .map(|factor| {
                let start = usize::from(factor.start);
                COPY_ROUTING_FACTORIZATION.entries[start..start + usize::from(factor.len)]
                    .iter()
                    .map(|entry| (entry.index, entry.coefficient))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        std::println!(
            "factor terms={} unique_left={} unique_right={} unique_pairs={} unique_left_support={} unique_right_support={}",
            COPY_ROUTING_RANK,
            lefts.len(),
            rights.len(),
            COPY_ROUTING_FACTORIZATION.terms.len(),
            lefts.iter().map(Vec::len).sum::<usize>(),
            rights.iter().map(Vec::len).sum::<usize>(),
        );
    }

    #[test]
    fn copy_routing_layout_fingerprint_is_pinned() {
        assert_eq!(
            COPY_ROUTING_LAYOUT_FINGERPRINT,
            PINNED_COPY_ROUTING_LAYOUT_FINGERPRINT
        );
    }

    #[test]
    fn copy_routing_factor_coefficients_are_classified() {
        let ones = COPY_ROUTING_FACTORIZATION
            .entries
            .iter()
            .filter(|entry| entry.coefficient == 1)
            .count();
        let small = COPY_ROUTING_FACTORIZATION
            .entries
            .iter()
            .filter(|entry| entry.coefficient <= 1024)
            .count();
        assert_eq!((ones, small), (361, 511));
    }

    #[test]
    fn copy_routing_unique_factor_metadata_is_compact_and_total() {
        let factor_slice = |factor: CopyRoutingFactor| {
            let start = usize::from(factor.start);
            &COPY_ROUTING_FACTORIZATION.entries[start..start + usize::from(factor.len)]
        };

        let mut next_start = 0usize;
        let mut left_support = 0usize;
        for (index, factor) in COPY_ROUTING_FACTORIZATION
            .left_factors
            .iter()
            .copied()
            .enumerate()
        {
            assert_eq!(usize::from(factor.start), next_start, "left factor {index}");
            assert_ne!(factor.len, 0, "left factor {index}");
            let entries = factor_slice(factor);
            assert!(entries.windows(2).all(|pair| pair[0].index < pair[1].index));
            assert!(entries.iter().all(|entry| usize::from(entry.index) < 64));
            next_start += entries.len();
            left_support += entries.len();
        }
        assert_eq!(left_support, 515);

        let right_start = next_start;
        let mut right_support = 0usize;
        for (index, factor) in COPY_ROUTING_FACTORIZATION
            .right_factors
            .iter()
            .copied()
            .enumerate()
        {
            assert_eq!(
                usize::from(factor.start),
                next_start,
                "right factor {index}"
            );
            assert_ne!(factor.len, 0, "right factor {index}");
            let entries = factor_slice(factor);
            assert!(entries.windows(2).all(|pair| pair[0].index < pair[1].index));
            assert!(entries.iter().all(|entry| usize::from(entry.index) < 16));
            next_start += entries.len();
            right_support += entries.len();
        }
        assert_eq!(right_start, 515);
        assert_eq!(right_support, 124);
        assert_eq!(next_start, COPY_ROUTING_UNIQUE_FACTOR_SUPPORT);

        for left in 0..COPY_ROUTING_UNIQUE_LEFT_FACTOR_COUNT {
            for right in left + 1..COPY_ROUTING_UNIQUE_LEFT_FACTOR_COUNT {
                assert_ne!(
                    factor_slice(COPY_ROUTING_FACTORIZATION.left_factors[left]),
                    factor_slice(COPY_ROUTING_FACTORIZATION.left_factors[right]),
                );
            }
        }
        for left in 0..COPY_ROUTING_UNIQUE_RIGHT_FACTOR_COUNT {
            for right in left + 1..COPY_ROUTING_UNIQUE_RIGHT_FACTOR_COUNT {
                assert_ne!(
                    factor_slice(COPY_ROUTING_FACTORIZATION.right_factors[left]),
                    factor_slice(COPY_ROUTING_FACTORIZATION.right_factors[right]),
                );
            }
        }

        let mut destination_end = 0usize;
        for (index, term) in COPY_ROUTING_FACTORIZATION.terms.iter().enumerate() {
            assert!(usize::from(term.left_factor) < COPY_ROUTING_UNIQUE_LEFT_FACTOR_COUNT);
            assert!(usize::from(term.right_factor) < COPY_ROUTING_UNIQUE_RIGHT_FACTOR_COUNT);
            assert_eq!(
                usize::from(term.matrix_start),
                destination_end,
                "term {index}"
            );
            assert_ne!(term.matrix_len, 0, "term {index}");
            destination_end += usize::from(term.matrix_len);
            assert!(COPY_ROUTING_FACTORIZATION.matrices
                [usize::from(term.matrix_start)..destination_end]
                .iter()
                .all(|matrix| usize::from(*matrix) < COPY_ROUTING_MATRIX_COUNT));
            for previous in &COPY_ROUTING_FACTORIZATION.terms[..index] {
                assert_ne!(
                    (term.left_factor, term.right_factor),
                    (previous.left_factor, previous.right_factor),
                );
            }
        }
        assert_eq!(destination_end, COPY_ROUTING_RANK);
    }

    #[test]
    fn registry_is_stable_and_fits_the_soundness_cap() {
        let registry = constraint_registry();
        assert_eq!(registry.len(), 252);
        assert_eq!(registry[0].id.wire_value(), 0);
        assert_eq!(registry[251].id.wire_value(), 251);
        assert_eq!(registry[251].kind, ConstraintKind::RangeLogUp);
        assert_eq!(RANDOMIZED_CLAIM_COUNT, 67);
        assert_eq!(DIRECT_RANGE_SOURCE_RESIDUAL_COUNT, 33);
        assert_eq!(DIRECT_RANGE_CONSTRAINT_SOURCE_COUNT, 284);
        assert_eq!(DIRECT_RANGE_PACKED_LANE_COUNT, 9);
        assert_eq!(DIRECT_RANGE_GLOBAL_HELPER_SUM_CLAIMS, 1);
        assert_eq!(DIRECT_RANGE_RANDOMIZED_CONSTRAINT_COUNT, 73);
        assert_eq!(DIRECT_RANGE_RANDOMIZED_CLAIM_COUNT, 74);
        assert_eq!(DIRECT_RANGE_THETA_COLLISION_DEGREE, 72);
        assert_eq!(source_relation_layout().len(), 60);
    }

    #[test]
    fn four_base_residuals_pack_injectively_into_qm31() {
        let coordinates = [M31(11), M31(22), M31(33), M31(44)];
        let packed = coordinates
            .into_iter()
            .enumerate()
            .fold(QM31::ZERO, |sum, (coordinate, value)| {
                sum.add(mul_tower_basis(lift(value), coordinate))
            });
        assert_eq!(packed.c0.a, coordinates[0]);
        assert_eq!(packed.c0.b, coordinates[1]);
        assert_eq!(packed.c1.a, coordinates[2]);
        assert_eq!(packed.c1.b, coordinates[3]);
        assert_ne!(packed, QM31::ZERO);
    }

    #[test]
    fn direct_range_packing_has_single_bit_and_reconstruction_teeth() {
        let mut openings = [QM31::ZERO; STATE_AND_INTERFACE_COLUMNS + 1];
        openings[0] = lift(M31(2));
        openings[crate::direct_range_hiding_v4::DIRECT_RANGE_RECONSTRUCTION_COLUMN_START] =
            lift(M31(2));
        let packed = direct_range_terminal_packed_lanes(&openings, QM31::ONE);
        assert_eq!(packed[0].c0.a, M31(2)); // 2^2 - 2
        assert!(packed[1..].iter().all(|value| *value == QM31::ZERO));

        openings = [QM31::ZERO; STATE_AND_INTERFACE_COLUMNS + 1];
        openings[crate::direct_range_hiding_v4::DIRECT_RANGE_RECONSTRUCTION_COLUMN_START] =
            lift(M31(7));
        let packed = direct_range_terminal_packed_lanes(&openings, QM31::ONE);
        // Source residual 30 is coordinate two of packed lane seven.
        assert_eq!(packed[7].c1.a, M31(7));
        assert_ne!(packed[7], QM31::ZERO);

        // A valid one-bit reconstruction has an exactly zero packed image.
        openings[0] = QM31::ONE;
        openings[crate::direct_range_hiding_v4::DIRECT_RANGE_RECONSTRUCTION_COLUMN_START] =
            QM31::ONE;
        assert!(direct_range_terminal_packed_lanes(&openings, QM31::ONE)
            .iter()
            .all(|value| *value == QM31::ZERO));

        // Every packed source coordinate occupies a unique outer theta lane
        // and tower coordinate; no source residual is silently discarded.
        let theta = challenge(901_001);
        let empty_residuals = [QM31::ZERO; CONSTRAINT_COUNT];
        let empty_base = [QM31::ZERO; PACKED_BASE_CONSTRAINT_COUNT];
        for source_index in 0..DIRECT_RANGE_SOURCE_RESIDUAL_COUNT {
            let mut source = [QM31::ZERO; DIRECT_RANGE_SOURCE_RESIDUAL_COUNT];
            source[source_index] = lift(M31(11));
            let lanes = core::array::from_fn(|group| {
                let start = 4 * group;
                let end = core::cmp::min(start + 4, source.len());
                pack_base_values(&source[start..end])
            });
            assert_ne!(lanes[source_index / 4], QM31::ZERO);
            assert_ne!(
                compose_direct_range_randomized_residuals(
                    &empty_residuals,
                    &empty_base,
                    &lanes,
                    theta,
                ),
                QM31::ZERO,
                "source residual {source_index} disappeared",
            );
        }
    }

    #[test]
    fn terminal_packed_horner_matches_generic_composition_at_edge_challenges() {
        let residuals = [QM31::ZERO; CONSTRAINT_COUNT];
        let direct_packed: [QM31; PACKED_BASE_CONSTRAINT_COUNT] =
            core::array::from_fn(|index| challenge(920_001 + 17 * index as u32));
        let direct_range: [QM31; DIRECT_RANGE_PACKED_LANE_COUNT] =
            core::array::from_fn(|index| challenge(930_001 + 19 * index as u32));
        let copy = challenge(940_001);
        let range = challenge(940_101);
        let mut ordinary_residuals = residuals;
        ordinary_residuals[COPY_LOGUP_ID] = copy;
        ordinary_residuals[RANGE_LOGUP_ID] = range;
        let mut direct_residuals = residuals;
        direct_residuals[COPY_LOGUP_ID] = copy;

        for theta in [QM31::ZERO, QM31::ONE, QM31::ONE.neg(), challenge(950_001)] {
            assert_eq!(
                compose_terminal_packed_residuals(&direct_packed, copy, range, theta),
                compose_randomized_residuals(&ordinary_residuals, Some(&direct_packed), theta,),
            );
            assert_eq!(
                compose_direct_range_terminal_packed_residuals(
                    &direct_packed,
                    copy,
                    &direct_range,
                    theta,
                ),
                compose_direct_range_randomized_residuals(
                    &direct_residuals,
                    &direct_packed,
                    &direct_range,
                    theta,
                ),
            );
            let mut radix8_coefficients =
                Vec::with_capacity(DIRECT_RANGE_RANDOMIZED_CONSTRAINT_COUNT);
            radix8_coefficients.extend_from_slice(&direct_packed);
            assert_eq!(
                compose_direct_range_terminal_packed_residuals_radix8(
                    &mut radix8_coefficients,
                    copy,
                    &direct_range,
                    theta,
                ),
                compose_direct_range_terminal_packed_residuals(
                    &direct_packed,
                    copy,
                    &direct_range,
                    theta,
                ),
            );
            assert_eq!(
                radix8_coefficients.len(),
                DIRECT_RANGE_RANDOMIZED_CONSTRAINT_COUNT
            );
        }
    }

    #[test]
    fn honest_payment_trace_zeroes_every_registered_polynomial() {
        let (public, witness) = fixture();
        let trace = build_spend_trace_v4(&public, &witness).unwrap();
        let lambda = challenge(100);
        let chi = challenge(200);
        let helpers = build_payment_helpers_v4(&trace, lambda, chi).unwrap();
        verify_payment_helpers_v4(&helpers, chi).unwrap();
        assert_eq!(helper_sums(&helpers).unwrap(), [QM31::ZERO; 2]);
        let context = ConstraintContextV4 {
            public: &public,
            trace: &trace,
            helpers: &helpers,
            chi,
        };
        for row in 0..TRACE_ROWS {
            let residuals = evaluate_constraint_row(&context, row).unwrap();
            assert_eq!(residuals, [QM31::ZERO; CONSTRAINT_COUNT], "row {row}");
        }
        assert!(constraint_composition_table(&context, challenge(300))
            .unwrap()
            .into_iter()
            .all(|value| value == QM31::ZERO));
    }

    #[test]
    fn balance_copy_and_range_mutations_have_teeth() {
        let (public, witness) = fixture();
        let trace = build_spend_trace_v4(&public, &witness).unwrap();
        let lambda = challenge(100);
        let chi = challenge(200);

        let aux = witness_aux_layout();
        let mut bad_balance = trace.clone();
        bad_balance.c1[aux.output_value_for_balance.column as usize]
            [aux.output_value_for_balance.row as usize] = bad_balance.c1
            [aux.output_value_for_balance.column as usize]
            [aux.output_value_for_balance.row as usize]
            .add(M31::ONE);
        let helpers = build_payment_helpers_v4(&bad_balance, lambda, chi).unwrap();
        let context = ConstraintContextV4 {
            public: &public,
            trace: &bad_balance,
            helpers: &helpers,
            chi,
        };
        assert_ne!(
            evaluate_constraint_row(&context, INPUT_VALUE_RANGE_ROW).unwrap()[BALANCE_ID],
            QM31::ZERO
        );
        assert_ne!(helper_sums(&helpers).unwrap()[0], QM31::ZERO);

        let mut bad_limb = trace;
        let cell = aux.input_value_limbs[0];
        bad_limb.c1[cell.column as usize][cell.row as usize] =
            bad_limb.c1[cell.column as usize][cell.row as usize].add(M31::ONE);
        let helpers = build_payment_helpers_v4(&bad_limb, lambda, chi).unwrap();
        let context = ConstraintContextV4 {
            public: &public,
            trace: &bad_limb,
            helpers: &helpers,
            chi,
        };
        let residuals = evaluate_constraint_row(&context, INPUT_VALUE_RANGE_ROW).unwrap();
        assert_ne!(residuals[INPUT_VALUE_RECONSTRUCTION_ID], QM31::ZERO);
    }

    #[test]
    fn terminal_oracle_matches_every_boolean_row_formula_class() {
        let (public, witness) = fixture();
        let mut trace = build_spend_trace_v4(&public, &witness).unwrap();
        // Make the comparison non-vacuous in several independent classes.
        trace.c1[17][0] = trace.c1[17][0].add(M31(9));
        trace.c1[7][ABSORPTION_ROW_IN_BLOCK] = trace.c1[7][ABSORPTION_ROW_IN_BLOCK].add(M31(3));
        trace.c1[0][INPUT_VALUE_RANGE_ROW] = trace.c1[0][INPUT_VALUE_RANGE_ROW].add(M31(5));
        let lambda = challenge(100);
        let chi = challenge(200);
        let theta = challenge(300);
        let helpers = build_payment_helpers_v4(&trace, lambda, chi).unwrap();
        let context = ConstraintContextV4 {
            public: &public,
            trace: &trace,
            helpers: &helpers,
            chi,
        };
        for row in [
            0usize,
            ABSORPTION_ROW_IN_BLOCK,
            INPUT_VALUE_RANGE_ROW,
            OUTPUT_VALUE_RANGE_ROW,
            AUX_ABSORPTION_PRODUCER_ROW_START + 2,
            AUX_ABSORPTION_PRODUCER_ROW_START + 47,
            TRACE_ROWS - 1,
        ] {
            let point = boolean_point(row);
            let openings = trace_openings_at_point(&trace, &helpers, &point).unwrap();
            assert_eq!(
                evaluate_constraint_point(&public, &openings, &point, lambda, chi, theta).unwrap(),
                compose_constraint_row(&context, row, theta).unwrap(),
                "row {row}"
            );
        }
    }

    #[test]
    fn direct_range_terminal_matches_independent_table_on_every_boolean_row() {
        let (public, witness) = fixture();
        let mut trace = build_spend_trace_v4(&public, &witness).unwrap();
        crate::direct_range_hiding_v4::apply_direct_range_witness_v4(&mut trace).unwrap();
        // A non-Boolean bit makes the comparison non-vacuous without changing
        // the copy-helper multiset.
        trace.c1[0][crate::direct_range_hiding_v4::DIRECT_RANGE_BIT_ROW_START] = M31(2);
        let lambda = challenge(810_001);
        let chi = challenge(820_001);
        let theta = challenge(830_001);
        let helper_masks =
            vec![QM31::ZERO; crate::direct_range_hiding_v4::COPY_HELPER_MASK_VARIABLES];
        let payment_mask = vec![QM31::ZERO; TRACE_ROWS];
        let helpers = crate::direct_range_hiding_v4::build_direct_range_hiding_helpers_v4(
            &trace,
            lambda,
            chi,
            &helper_masks,
            &payment_mask,
        )
        .unwrap();
        let table =
            direct_range_hiding_composition_table(&public, &trace, &helpers, chi, theta).unwrap();
        assert_ne!(
            table[crate::direct_range_hiding_v4::DIRECT_RANGE_BIT_ROW_START],
            QM31::ZERO,
        );
        for row in 0..TRACE_ROWS {
            let point = boolean_point(row);
            let openings = direct_range_hiding_trace_openings_at_point(&trace, &helpers, &point)
                .expect("fixed direct-range shape");
            let terminal = evaluate_direct_range_hiding_constraint_point(
                &public,
                &openings.constraint_openings(),
                &point,
                lambda,
                chi,
                theta,
            )
            .unwrap();
            assert_eq!(terminal, table[row], "Boolean row {row}");
        }
    }
}
