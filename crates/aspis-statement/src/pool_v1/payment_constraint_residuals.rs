//! Host algebraic residuals for the frozen Pool V1 payment trace.
//!
//! This module checks the concrete 16-column, 1,024-row trace in
//! [`super::payment_trace`] without calling a hash function as a black box.
//! Every Poseidon residual is obtained from the same two-round M31 equations
//! used by the deployed trace machinery. The remaining residuals bind the
//! sponge schedule, private Merkle ordering, value decompositions,
//! conservation equations, public digests, source aliases, and all cells
//! declared to be padding by the frozen layout.
//!
//! This is only an executable host algebraic foundation. It is not a Tag-73
//! constraint registry, terminal oracle, prover, transcript binding, verifier
//! profile, or Pool-program authorization claim. In particular, Pool identity,
//! deployment domain, anchor sequence, withdrawal destination, nullifier
//! freshness, and runtime account authorization remain public/runtime checks;
//! this module consumes the already-decoded payment public values which enter
//! the algebraic relation.

use alloc::vec::Vec;

use aspis_core::field::M31;

use crate::{
    poseidon2::{
        evaluate_trace_round_pair, Digest, DIGEST_ELEMS, MERKLE_NODE_COMPRESSION_V3_TWEAK,
        POSEIDON2_WIDTH, RATE,
    },
    spend::{DOMAIN_NOTE, DOMAIN_NULLIFIER, DOMAIN_OWNER_KEY, VALUE_LIMIT},
    state_only_trace::StateOnlyTraceFoundation,
};

use super::{
    payment_relation::{PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1},
    payment_trace::{
        POOL_V1_PAYMENT_AUX_ROW_END, POOL_V1_PAYMENT_DIRECTION_BITS,
        POOL_V1_PAYMENT_DIRECTION_ROW_START, POOL_V1_PAYMENT_TRACE_BLOCKS,
        POOL_V1_PAYMENT_TRACE_BLOCK_ROWS, POOL_V1_PAYMENT_TRACE_C1_COLUMNS,
        POOL_V1_PAYMENT_TRACE_ROWS, POOL_V1_PAYMENT_TRACE_TWO_ROUND_ROWS_PER_BLOCK,
        POOL_V1_PAYMENT_VALUE_BITS, POOL_V1_PAYMENT_VALUE_COUNT, POOL_V1_PAYMENT_VALUE_ROW_START,
    },
};

/// A Poseidon S-box is `x^5`; composing the two rounds represented by one
/// active trace row therefore has intrinsic degree `5 * 5 = 25`.
pub const POOL_V1_PAYMENT_POSEIDON_SBOX_DEGREE: usize = 5;
pub const POOL_V1_PAYMENT_TWO_ROUND_INTRINSIC_DEGREE: usize =
    POOL_V1_PAYMENT_POSEIDON_SBOX_DEGREE * POOL_V1_PAYMENT_POSEIDON_SBOX_DEGREE;
/// Both Booleanity and selected-child path ordering are quadratic.
pub const POOL_V1_PAYMENT_BOOLEAN_INTRINSIC_DEGREE: usize = 2;
pub const POOL_V1_PAYMENT_PATH_ORDERING_INTRINSIC_DEGREE: usize = 2;
/// Schedule, aliases, recomposition, conservation, public binding, and zero
/// padding are affine residuals.
pub const POOL_V1_PAYMENT_AFFINE_INTRINSIC_DEGREE: usize = 1;

const fn max_degree(left: usize, right: usize) -> usize {
    if left > right {
        left
    } else {
        right
    }
}

/// Maximum intrinsic degree of any residual in this module.
pub const POOL_V1_PAYMENT_MAX_INTRINSIC_DEGREE: usize = max_degree(
    POOL_V1_PAYMENT_TWO_ROUND_INTRINSIC_DEGREE,
    max_degree(
        POOL_V1_PAYMENT_BOOLEAN_INTRINSIC_DEGREE,
        max_degree(
            POOL_V1_PAYMENT_PATH_ORDERING_INTRINSIC_DEGREE,
            POOL_V1_PAYMENT_AFFINE_INTRINSIC_DEGREE,
        ),
    ),
);
/// A future Boolean-row selector would add one to the intrinsic bound.
pub const POOL_V1_PAYMENT_SELECTED_ORACLE_INDIVIDUAL_DEGREE: usize =
    POOL_V1_PAYMENT_MAX_INTRINSIC_DEGREE + 1;
/// A future outer zerocheck equality factor would add one more.
pub const POOL_V1_PAYMENT_ZEROCHECK_INDIVIDUAL_DEGREE: usize =
    POOL_V1_PAYMENT_SELECTED_ORACLE_INDIVIDUAL_DEGREE + 1;

pub const POOL_V1_PAYMENT_POSEIDON_RESIDUAL_COUNT: usize =
    POOL_V1_PAYMENT_TRACE_BLOCKS * POOL_V1_PAYMENT_TRACE_TWO_ROUND_ROWS_PER_BLOCK * POSEIDON2_WIDTH;
pub const POOL_V1_PAYMENT_PATH_ORDERING_RESIDUAL_COUNT: usize =
    POOL_V1_PAYMENT_DIRECTION_BITS * DIGEST_ELEMS;
pub const POOL_V1_PAYMENT_VALUE_BOOLEAN_RESIDUAL_COUNT: usize =
    POOL_V1_PAYMENT_VALUE_COUNT * POOL_V1_PAYMENT_VALUE_BITS;

const POOL_V1_PAYMENT_TRANSFER_SCHEDULE_RESIDUAL_COUNT: usize = 626;
const POOL_V1_PAYMENT_WITHDRAWAL_SCHEDULE_RESIDUAL_COUNT: usize = 548;
const POOL_V1_PAYMENT_TRANSFER_ALIAS_RESIDUAL_COUNT: usize = 27;
const POOL_V1_PAYMENT_WITHDRAWAL_ALIAS_RESIDUAL_COUNT: usize = 26;
const POOL_V1_PAYMENT_TRANSFER_PUBLIC_RESIDUAL_COUNT: usize = 4 * DIGEST_ELEMS;
const POOL_V1_PAYMENT_WITHDRAWAL_PUBLIC_RESIDUAL_COUNT: usize = 3 * DIGEST_ELEMS;
const POOL_V1_PAYMENT_TRANSFER_ZERO_PADDING_RESIDUAL_COUNT: usize = 6_626;
const POOL_V1_PAYMENT_WITHDRAWAL_ZERO_PADDING_RESIDUAL_COUNT: usize = 6_722;

const _: () = assert!(POSEIDON2_WIDTH == 16);
const _: () = assert!(DIGEST_ELEMS == 8);
const _: () = assert!(RATE == 8);
const _: () = assert!(POOL_V1_PAYMENT_MAX_INTRINSIC_DEGREE == 25);
const _: () = assert!(POOL_V1_PAYMENT_SELECTED_ORACLE_INDIVIDUAL_DEGREE == 26);
const _: () = assert!(POOL_V1_PAYMENT_ZEROCHECK_INDIVIDUAL_DEGREE == 27);
const _: () = assert!(POOL_V1_PAYMENT_POSEIDON_RESIDUAL_COUNT == 8_624);
const _: () = assert!(POOL_V1_PAYMENT_PATH_ORDERING_RESIDUAL_COUNT == 160);
const _: () = assert!(POOL_V1_PAYMENT_VALUE_BOOLEAN_RESIDUAL_COUNT == 90);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PaymentResidualClassV1 {
    PoseidonRoundPairs,
    SpongeSchedule,
    SourceAliases,
    DirectionBooleanity,
    PathOrdering,
    ValueBooleanity,
    ValueRecomposition,
    Conservation,
    PublicBindings,
    ZeroPadding,
}

/// Complete, unrandomized host residual vector split by semantic class.
///
/// The split is diagnostic only. A future proof profile must choose and bind
/// an injective packing/randomization scheme rather than treating
/// [`Self::all_zero`] as a verifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoolV1PaymentConstraintResidualsV1 {
    pub poseidon_round_pairs: Vec<M31>,
    pub sponge_schedule: Vec<M31>,
    pub source_aliases: Vec<M31>,
    pub direction_booleanity: [M31; POOL_V1_PAYMENT_DIRECTION_BITS],
    pub path_ordering: Vec<M31>,
    pub value_booleanity: [[M31; POOL_V1_PAYMENT_VALUE_BITS]; POOL_V1_PAYMENT_VALUE_COUNT],
    pub value_recomposition: [M31; POOL_V1_PAYMENT_VALUE_COUNT],
    pub conservation: M31,
    pub public_bindings: Vec<M31>,
    pub zero_padding: Vec<M31>,
}

impl PoolV1PaymentConstraintResidualsV1 {
    fn slice_is_zero(values: &[M31]) -> bool {
        values.iter().all(|value| *value == M31::ZERO)
    }

    pub fn class_is_zero(&self, class: PoolV1PaymentResidualClassV1) -> bool {
        match class {
            PoolV1PaymentResidualClassV1::PoseidonRoundPairs => {
                Self::slice_is_zero(&self.poseidon_round_pairs)
            }
            PoolV1PaymentResidualClassV1::SpongeSchedule => {
                Self::slice_is_zero(&self.sponge_schedule)
            }
            PoolV1PaymentResidualClassV1::SourceAliases => {
                Self::slice_is_zero(&self.source_aliases)
            }
            PoolV1PaymentResidualClassV1::DirectionBooleanity => {
                Self::slice_is_zero(&self.direction_booleanity)
            }
            PoolV1PaymentResidualClassV1::PathOrdering => Self::slice_is_zero(&self.path_ordering),
            PoolV1PaymentResidualClassV1::ValueBooleanity => self
                .value_booleanity
                .iter()
                .flatten()
                .all(|value| *value == M31::ZERO),
            PoolV1PaymentResidualClassV1::ValueRecomposition => {
                Self::slice_is_zero(&self.value_recomposition)
            }
            PoolV1PaymentResidualClassV1::Conservation => self.conservation == M31::ZERO,
            PoolV1PaymentResidualClassV1::PublicBindings => {
                Self::slice_is_zero(&self.public_bindings)
            }
            PoolV1PaymentResidualClassV1::ZeroPadding => Self::slice_is_zero(&self.zero_padding),
        }
    }

    pub fn all_zero(&self) -> bool {
        [
            PoolV1PaymentResidualClassV1::PoseidonRoundPairs,
            PoolV1PaymentResidualClassV1::SpongeSchedule,
            PoolV1PaymentResidualClassV1::SourceAliases,
            PoolV1PaymentResidualClassV1::DirectionBooleanity,
            PoolV1PaymentResidualClassV1::PathOrdering,
            PoolV1PaymentResidualClassV1::ValueBooleanity,
            PoolV1PaymentResidualClassV1::ValueRecomposition,
            PoolV1PaymentResidualClassV1::Conservation,
            PoolV1PaymentResidualClassV1::PublicBindings,
            PoolV1PaymentResidualClassV1::ZeroPadding,
        ]
        .into_iter()
        .all(|class| self.class_is_zero(class))
    }

    pub fn residual_count(&self) -> usize {
        self.poseidon_round_pairs.len()
            + self.sponge_schedule.len()
            + self.source_aliases.len()
            + self.direction_booleanity.len()
            + self.path_ordering.len()
            + POOL_V1_PAYMENT_VALUE_BOOLEAN_RESIDUAL_COUNT
            + self.value_recomposition.len()
            + 1
            + self.public_bindings.len()
            + self.zero_padding.len()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PaymentConstraintResidualErrorV1 {
    Shape,
    InvalidWithdrawalAmount,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PaymentVariant {
    PrivateTransfer,
    Withdrawal,
}

#[derive(Clone, Copy)]
struct ConstraintPublic {
    variant: PaymentVariant,
    anchor: Digest,
    nullifier: Digest,
    asset_id: M31,
    recipient_commitment: Option<Digest>,
    change_commitment: Digest,
    withdrawal_amount: Option<u32>,
}

#[inline(always)]
fn cell(trace: &StateOnlyTraceFoundation, block: usize, local_row: usize, lane: usize) -> M31 {
    trace.c1[lane][block * POOL_V1_PAYMENT_TRACE_BLOCK_ROWS + local_row]
}

#[inline(always)]
fn row_cell(trace: &StateOnlyTraceFoundation, row: usize, column: usize) -> M31 {
    trace.c1[column][row]
}

#[inline(always)]
fn direction_cell(trace: &StateOnlyTraceFoundation, level: usize) -> M31 {
    row_cell(
        trace,
        POOL_V1_PAYMENT_DIRECTION_ROW_START + level / POSEIDON2_WIDTH,
        level % POSEIDON2_WIDTH,
    )
}

#[inline(always)]
fn value_bit_cell(trace: &StateOnlyTraceFoundation, value: usize, bit: usize) -> M31 {
    let row_start = POOL_V1_PAYMENT_VALUE_ROW_START + 2 * value;
    row_cell(
        trace,
        row_start + bit / POSEIDON2_WIDTH,
        bit % POSEIDON2_WIDTH,
    )
}

fn append_equal(left: M31, right: M31, output: &mut Vec<M31>) {
    output.push(left.sub(right));
}

fn append_digest_equal(left: &Digest, right: &Digest, output: &mut Vec<M31>) {
    for lane in 0..DIGEST_ELEMS {
        append_equal(left[lane], right[lane], output);
    }
}

fn trace_digest(trace: &StateOnlyTraceFoundation, block: usize) -> Digest {
    core::array::from_fn(|lane| cell(trace, block, 11, lane))
}

fn append_poseidon_residuals(trace: &StateOnlyTraceFoundation, output: &mut Vec<M31>) {
    for block in 0..POOL_V1_PAYMENT_TRACE_BLOCKS {
        for local_row in 0..POOL_V1_PAYMENT_TRACE_TWO_ROUND_ROWS_PER_BLOCK {
            let mut input = core::array::from_fn(|lane| cell(trace, block, local_row, lane));
            if local_row == 0 {
                for lane in 0..RATE {
                    input[lane] = input[lane].add(cell(trace, block, 12, lane));
                }
            }
            let (_, expected) = evaluate_trace_round_pair(input, local_row)
                .expect("frozen local Poseidon row is in 0..11");
            for lane in 0..POSEIDON2_WIDTH {
                append_equal(
                    cell(trace, block, local_row + 1, lane),
                    expected[lane],
                    output,
                );
            }
        }
    }
}

fn append_sponge_schedule(
    trace: &StateOnlyTraceFoundation,
    block_start: usize,
    domain: M31,
    input_length: usize,
    chunk_lengths: &[usize],
    output: &mut Vec<M31>,
) {
    debug_assert_eq!(chunk_lengths.iter().sum::<usize>(), input_length);
    debug_assert!(chunk_lengths.iter().all(|length| *length <= RATE));
    let mut initial = [M31::ZERO; POSEIDON2_WIDTH];
    initial[RATE] = domain;
    initial[RATE + 1] = M31(input_length as u32);
    for lane in 0..POSEIDON2_WIDTH {
        append_equal(cell(trace, block_start, 0, lane), initial[lane], output);
    }
    for offset in 1..chunk_lengths.len() {
        for lane in 0..POSEIDON2_WIDTH {
            append_equal(
                cell(trace, block_start + offset, 0, lane),
                cell(trace, block_start + offset - 1, 11, lane),
                output,
            );
        }
    }
    for (offset, chunk_length) in chunk_lengths.iter().copied().enumerate() {
        for lane in chunk_length..POSEIDON2_WIDTH {
            output.push(cell(trace, block_start + offset, 12, lane));
        }
    }
}

fn append_node_schedule(trace: &StateOnlyTraceFoundation, output: &mut Vec<M31>) {
    for block in 4..24 {
        for lane in 0..RATE {
            output.push(cell(trace, block, 0, lane));
        }
        for lane in RATE..POSEIDON2_WIDTH {
            output.push(cell(trace, block, 12, lane));
        }
    }
}

fn append_all_schedule_residuals(
    trace: &StateOnlyTraceFoundation,
    variant: PaymentVariant,
    output: &mut Vec<M31>,
) {
    append_sponge_schedule(trace, 0, DOMAIN_OWNER_KEY, 8, &[8], output);
    append_sponge_schedule(trace, 1, DOMAIN_NOTE, 18, &[8, 8, 2], output);
    append_node_schedule(trace, output);
    append_sponge_schedule(trace, 24, DOMAIN_NULLIFIER, 16, &[8, 8], output);
    if variant == PaymentVariant::PrivateTransfer {
        append_sponge_schedule(trace, 26, DOMAIN_NOTE, 18, &[8, 8, 2], output);
    }
    append_sponge_schedule(trace, 29, DOMAIN_NOTE, 18, &[8, 8, 2], output);
}

fn append_source_alias_residuals(
    trace: &StateOnlyTraceFoundation,
    public: ConstraintPublic,
    output: &mut Vec<M31>,
) {
    // Owner-key output is the first chunk of the input-note preimage.
    for lane in 0..DIGEST_ELEMS {
        append_equal(cell(trace, 0, 11, lane), cell(trace, 1, 12, lane), output);
    }
    // The same nullifier key feeds owner-key and nullifier sponges.
    for lane in 0..DIGEST_ELEMS {
        append_equal(cell(trace, 0, 12, lane), cell(trace, 24, 12, lane), output);
    }
    // The input-note salt spans the final six lanes of block 2 and the first
    // two lanes of block 3; the nullifier sponge holds it contiguously.
    for lane in 0..6 {
        append_equal(
            cell(trace, 2, 12, 2 + lane),
            cell(trace, 25, 12, lane),
            output,
        );
    }
    for lane in 6..DIGEST_ELEMS {
        append_equal(
            cell(trace, 3, 12, lane - 6),
            cell(trace, 25, 12, lane),
            output,
        );
    }
    // Every real note preimage uses the statement's one public asset.
    append_equal(cell(trace, 2, 12, 1), public.asset_id, output);
    if public.variant == PaymentVariant::PrivateTransfer {
        append_equal(cell(trace, 27, 12, 1), public.asset_id, output);
    }
    append_equal(cell(trace, 30, 12, 1), public.asset_id, output);
}

fn append_path_ordering_residuals(
    trace: &StateOnlyTraceFoundation,
    direction_booleanity: &mut [M31; POOL_V1_PAYMENT_DIRECTION_BITS],
    path_ordering: &mut Vec<M31>,
) {
    for level in 0..POOL_V1_PAYMENT_DIRECTION_BITS {
        let bit = direction_cell(trace, level);
        direction_booleanity[level] = bit.mul(bit.sub(M31::ONE));
        let block = 4 + level;
        let previous_block = block - 1;
        for lane in 0..DIGEST_ELEMS {
            let current = cell(trace, previous_block, 11, lane);
            let left = cell(trace, block, 12, lane);
            let right = if lane + 1 == DIGEST_ELEMS {
                cell(trace, block, 0, RATE + lane).sub(MERKLE_NODE_COMPRESSION_V3_TWEAK)
            } else {
                cell(trace, block, 0, RATE + lane)
            };
            // bit=0 selects left=current; bit=1 selects right=current.
            path_ordering.push(left.sub(current).add(bit.mul(right.sub(left))));
        }
    }
}

fn value_source_cells(
    trace: &StateOnlyTraceFoundation,
    public: ConstraintPublic,
) -> [M31; POOL_V1_PAYMENT_VALUE_COUNT] {
    [
        cell(trace, 2, 12, 0),
        match public.withdrawal_amount {
            Some(amount) => M31(amount),
            None => cell(trace, 27, 12, 0),
        },
        cell(trace, 30, 12, 0),
    ]
}

fn evaluate_value_residuals(
    trace: &StateOnlyTraceFoundation,
    public: ConstraintPublic,
) -> (
    [[M31; POOL_V1_PAYMENT_VALUE_BITS]; POOL_V1_PAYMENT_VALUE_COUNT],
    [M31; POOL_V1_PAYMENT_VALUE_COUNT],
    M31,
) {
    let value_booleanity = core::array::from_fn(|value| {
        core::array::from_fn(|bit| {
            let bit = value_bit_cell(trace, value, bit);
            bit.mul(bit.sub(M31::ONE))
        })
    });
    let reconstructed: [M31; POOL_V1_PAYMENT_VALUE_COUNT] = core::array::from_fn(|value| {
        (0..POOL_V1_PAYMENT_VALUE_BITS).fold(M31::ZERO, |sum, bit| {
            sum.add(value_bit_cell(trace, value, bit).mul(M31(1u32 << bit)))
        })
    });
    let source = value_source_cells(trace, public);
    let value_recomposition = core::array::from_fn(|value| source[value].sub(reconstructed[value]));
    let conservation = source[0].sub(source[1]).sub(source[2]);
    (value_booleanity, value_recomposition, conservation)
}

fn append_public_binding_residuals(
    trace: &StateOnlyTraceFoundation,
    public: ConstraintPublic,
    output: &mut Vec<M31>,
) {
    append_digest_equal(&trace_digest(trace, 23), &public.anchor, output);
    append_digest_equal(&trace_digest(trace, 25), &public.nullifier, output);
    if let Some(recipient) = public.recipient_commitment {
        append_digest_equal(&trace_digest(trace, 28), &recipient, output);
    }
    append_digest_equal(&trace_digest(trace, 31), &public.change_commitment, output);
}

fn append_fixed_zero_block(trace: &StateOnlyTraceFoundation, block: usize, output: &mut Vec<M31>) {
    for lane in 0..POSEIDON2_WIDTH {
        output.push(cell(trace, block, 0, lane));
        output.push(cell(trace, block, 12, lane));
    }
}

fn append_zero_padding_residuals(
    trace: &StateOnlyTraceFoundation,
    variant: PaymentVariant,
    output: &mut Vec<M31>,
) {
    // Every block's nonsemantic local rows are exactly zero.
    for block in 0..POOL_V1_PAYMENT_TRACE_BLOCKS {
        for local_row in 13..POOL_V1_PAYMENT_TRACE_BLOCK_ROWS {
            for lane in 0..POSEIDON2_WIDTH {
                output.push(cell(trace, block, local_row, lane));
            }
        }
    }

    // Withdrawal has no hidden recipient preimage.
    if variant == PaymentVariant::Withdrawal {
        for block in 26..=28 {
            append_fixed_zero_block(trace, block, output);
        }
    }
    // The common tail is seventeen independent zero-input permutations.
    for block in 32..POOL_V1_PAYMENT_TRACE_BLOCKS {
        append_fixed_zero_block(trace, block, output);
    }

    // Unused direction/value slots and every row after the payment auxiliary
    // region are fixed zero, so no extra witness can hide there.
    for column in 4..POSEIDON2_WIDTH {
        output.push(row_cell(
            trace,
            POOL_V1_PAYMENT_DIRECTION_ROW_START + 1,
            column,
        ));
    }
    for value in 0..POOL_V1_PAYMENT_VALUE_COUNT {
        for column in 14..POSEIDON2_WIDTH {
            output.push(row_cell(
                trace,
                POOL_V1_PAYMENT_VALUE_ROW_START + 2 * value + 1,
                column,
            ));
        }
    }
    for row in POOL_V1_PAYMENT_AUX_ROW_END..POOL_V1_PAYMENT_TRACE_ROWS {
        for column in 0..POSEIDON2_WIDTH {
            output.push(row_cell(trace, row, column));
        }
    }
}

fn evaluate_payment_constraint_residuals(
    trace: &StateOnlyTraceFoundation,
    public: ConstraintPublic,
) -> Result<PoolV1PaymentConstraintResidualsV1, PoolV1PaymentConstraintResidualErrorV1> {
    if trace.c1.len() != POOL_V1_PAYMENT_TRACE_C1_COLUMNS
        || trace
            .c1
            .iter()
            .any(|column| column.len() != POOL_V1_PAYMENT_TRACE_ROWS)
    {
        return Err(PoolV1PaymentConstraintResidualErrorV1::Shape);
    }
    if let Some(amount) = public.withdrawal_amount {
        if amount >= VALUE_LIMIT {
            return Err(PoolV1PaymentConstraintResidualErrorV1::InvalidWithdrawalAmount);
        }
    }

    let mut poseidon_round_pairs = Vec::with_capacity(POOL_V1_PAYMENT_POSEIDON_RESIDUAL_COUNT);
    append_poseidon_residuals(trace, &mut poseidon_round_pairs);

    let expected_schedule = match public.variant {
        PaymentVariant::PrivateTransfer => POOL_V1_PAYMENT_TRANSFER_SCHEDULE_RESIDUAL_COUNT,
        PaymentVariant::Withdrawal => POOL_V1_PAYMENT_WITHDRAWAL_SCHEDULE_RESIDUAL_COUNT,
    };
    let mut sponge_schedule = Vec::with_capacity(expected_schedule);
    append_all_schedule_residuals(trace, public.variant, &mut sponge_schedule);

    let expected_aliases = match public.variant {
        PaymentVariant::PrivateTransfer => POOL_V1_PAYMENT_TRANSFER_ALIAS_RESIDUAL_COUNT,
        PaymentVariant::Withdrawal => POOL_V1_PAYMENT_WITHDRAWAL_ALIAS_RESIDUAL_COUNT,
    };
    let mut source_aliases = Vec::with_capacity(expected_aliases);
    append_source_alias_residuals(trace, public, &mut source_aliases);

    let mut direction_booleanity = [M31::ZERO; POOL_V1_PAYMENT_DIRECTION_BITS];
    let mut path_ordering = Vec::with_capacity(POOL_V1_PAYMENT_PATH_ORDERING_RESIDUAL_COUNT);
    append_path_ordering_residuals(trace, &mut direction_booleanity, &mut path_ordering);

    let (value_booleanity, value_recomposition, conservation) =
        evaluate_value_residuals(trace, public);

    let expected_public = match public.variant {
        PaymentVariant::PrivateTransfer => POOL_V1_PAYMENT_TRANSFER_PUBLIC_RESIDUAL_COUNT,
        PaymentVariant::Withdrawal => POOL_V1_PAYMENT_WITHDRAWAL_PUBLIC_RESIDUAL_COUNT,
    };
    let mut public_bindings = Vec::with_capacity(expected_public);
    append_public_binding_residuals(trace, public, &mut public_bindings);

    let expected_zero_padding = match public.variant {
        PaymentVariant::PrivateTransfer => POOL_V1_PAYMENT_TRANSFER_ZERO_PADDING_RESIDUAL_COUNT,
        PaymentVariant::Withdrawal => POOL_V1_PAYMENT_WITHDRAWAL_ZERO_PADDING_RESIDUAL_COUNT,
    };
    let mut zero_padding = Vec::with_capacity(expected_zero_padding);
    append_zero_padding_residuals(trace, public.variant, &mut zero_padding);

    debug_assert_eq!(
        poseidon_round_pairs.len(),
        POOL_V1_PAYMENT_POSEIDON_RESIDUAL_COUNT
    );
    debug_assert_eq!(sponge_schedule.len(), expected_schedule);
    debug_assert_eq!(source_aliases.len(), expected_aliases);
    debug_assert_eq!(
        path_ordering.len(),
        POOL_V1_PAYMENT_PATH_ORDERING_RESIDUAL_COUNT
    );
    debug_assert_eq!(public_bindings.len(), expected_public);
    debug_assert_eq!(zero_padding.len(), expected_zero_padding);

    Ok(PoolV1PaymentConstraintResidualsV1 {
        poseidon_round_pairs,
        sponge_schedule,
        source_aliases,
        direction_booleanity,
        path_ordering,
        value_booleanity,
        value_recomposition,
        conservation,
        public_bindings,
        zero_padding,
    })
}

pub fn evaluate_pool_v1_private_transfer_constraint_residuals_v1(
    public: &PoolV1PrivateTransferPublicV1,
    trace: &StateOnlyTraceFoundation,
) -> Result<PoolV1PaymentConstraintResidualsV1, PoolV1PaymentConstraintResidualErrorV1> {
    evaluate_payment_constraint_residuals(
        trace,
        ConstraintPublic {
            variant: PaymentVariant::PrivateTransfer,
            anchor: public.anchor_root,
            nullifier: public.nullifier,
            asset_id: public.asset_id,
            recipient_commitment: Some(public.recipient_commitment),
            change_commitment: public.change_commitment,
            withdrawal_amount: None,
        },
    )
}

pub fn evaluate_pool_v1_withdrawal_constraint_residuals_v1(
    public: &PoolV1WithdrawalPublicV1,
    trace: &StateOnlyTraceFoundation,
) -> Result<PoolV1PaymentConstraintResidualsV1, PoolV1PaymentConstraintResidualErrorV1> {
    evaluate_payment_constraint_residuals(
        trace,
        ConstraintPublic {
            variant: PaymentVariant::Withdrawal,
            anchor: public.anchor_root,
            nullifier: public.nullifier,
            asset_id: public.asset_id,
            recipient_commitment: None,
            change_commitment: public.change_commitment,
            withdrawal_amount: Some(public.amount),
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        derive_owner_key,
        pool_v1::{
            build_pool_v1_private_transfer_trace_v1, build_pool_v1_withdrawal_trace_v1,
            pool_v1_membership_root_v1, pool_v1_note_commitment, pool_v1_nullifier,
            PoolV1InputNoteWitnessV1, PoolV1MembershipWitnessV1, PoolV1OutputNoteWitnessV1,
            PoolV1PaymentRelationContextV1, PoolV1PaymentRuntimeBindingV1, PoolV1PaymentTraceV1,
            PoolV1PrivateTransferWitnessV1, PoolV1WithdrawalWitnessV1,
        },
    };

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn input(value: u32) -> PoolV1InputNoteWitnessV1 {
        PoolV1InputNoteWitnessV1 {
            nullifier_key: digest(10),
            salt: digest(100),
            value,
            membership: PoolV1MembershipWitnessV1 {
                siblings: core::array::from_fn(|level| digest(1_000 + level as u32 * 100)),
                index: 0x5_4321,
            },
        }
    }

    fn output(seed: u32, value: u32) -> PoolV1OutputNoteWitnessV1 {
        PoolV1OutputNoteWitnessV1 {
            owner_key: digest(seed),
            salt: digest(seed + 100),
            value,
        }
    }

    fn transfer_fixture() -> (
        PoolV1PrivateTransferPublicV1,
        PoolV1PrivateTransferWitnessV1,
    ) {
        let witness = PoolV1PrivateTransferWitnessV1 {
            input: input(1_000),
            recipient: output(300, 600),
            change: output(500, 400),
        };
        let asset_id = M31(77);
        let owner_key = derive_owner_key(&witness.input.nullifier_key);
        let leaf = pool_v1_note_commitment(
            &owner_key,
            witness.input.value,
            asset_id,
            &witness.input.salt,
        );
        let public = PoolV1PrivateTransferPublicV1 {
            pool: [1u8; 32],
            deployment_domain: [2u8; 32],
            anchor_sequence: 42,
            anchor_root: pool_v1_membership_root_v1(leaf, &witness.input.membership).unwrap(),
            nullifier: pool_v1_nullifier(&witness.input.nullifier_key, &witness.input.salt),
            asset_id,
            recipient_commitment: pool_v1_note_commitment(
                &witness.recipient.owner_key,
                witness.recipient.value,
                asset_id,
                &witness.recipient.salt,
            ),
            change_commitment: pool_v1_note_commitment(
                &witness.change.owner_key,
                witness.change.value,
                asset_id,
                &witness.change.salt,
            ),
        };
        (public, witness)
    }

    fn withdrawal_fixture() -> (PoolV1WithdrawalPublicV1, PoolV1WithdrawalWitnessV1) {
        let witness = PoolV1WithdrawalWitnessV1 {
            input: input(1_000),
            change: output(700, 750),
        };
        let asset_id = M31(77);
        let owner_key = derive_owner_key(&witness.input.nullifier_key);
        let leaf = pool_v1_note_commitment(
            &owner_key,
            witness.input.value,
            asset_id,
            &witness.input.salt,
        );
        let public = PoolV1WithdrawalPublicV1 {
            pool: [1u8; 32],
            deployment_domain: [2u8; 32],
            anchor_sequence: 42,
            anchor_root: pool_v1_membership_root_v1(leaf, &witness.input.membership).unwrap(),
            nullifier: pool_v1_nullifier(&witness.input.nullifier_key, &witness.input.salt),
            asset_id,
            amount: 250,
            destination_token_account: [9u8; 32],
            change_commitment: pool_v1_note_commitment(
                &witness.change.owner_key,
                witness.change.value,
                asset_id,
                &witness.change.salt,
            ),
        };
        (public, witness)
    }

    fn transfer_context<'a>(
        public: &PoolV1PrivateTransferPublicV1,
    ) -> PoolV1PaymentRelationContextV1<'a> {
        PoolV1PaymentRelationContextV1 {
            runtime_binding: PoolV1PaymentRuntimeBindingV1 {
                pool: public.pool,
                deployment_domain: public.deployment_domain,
                anchor_sequence: public.anchor_sequence,
                anchor_root: public.anchor_root,
                asset_id: public.asset_id,
            },
            spent_nullifiers: &[],
        }
    }

    fn withdrawal_context<'a>(
        public: &PoolV1WithdrawalPublicV1,
    ) -> PoolV1PaymentRelationContextV1<'a> {
        PoolV1PaymentRelationContextV1 {
            runtime_binding: PoolV1PaymentRuntimeBindingV1 {
                pool: public.pool,
                deployment_domain: public.deployment_domain,
                anchor_sequence: public.anchor_sequence,
                anchor_root: public.anchor_root,
                asset_id: public.asset_id,
            },
            spent_nullifiers: &[],
        }
    }

    fn built_transfer() -> (PoolV1PrivateTransferPublicV1, PoolV1PaymentTraceV1) {
        let (public, witness) = transfer_fixture();
        let trace =
            build_pool_v1_private_transfer_trace_v1(&public, &witness, transfer_context(&public))
                .unwrap();
        (public, trace)
    }

    fn built_withdrawal() -> (PoolV1WithdrawalPublicV1, PoolV1PaymentTraceV1) {
        let (public, witness) = withdrawal_fixture();
        let trace =
            build_pool_v1_withdrawal_trace_v1(&public, &witness, withdrawal_context(&public))
                .unwrap();
        (public, trace)
    }

    fn assert_class_nonzero(
        residuals: &PoolV1PaymentConstraintResidualsV1,
        class: PoolV1PaymentResidualClassV1,
    ) {
        assert!(
            !residuals.class_is_zero(class),
            "class unexpectedly zero: {class:?}"
        );
        assert!(!residuals.all_zero());
    }

    fn set_value_bits(trace: &mut StateOnlyTraceFoundation, value: usize, integer: u32) {
        for bit in 0..POOL_V1_PAYMENT_VALUE_BITS {
            let row = POOL_V1_PAYMENT_VALUE_ROW_START + 2 * value + bit / POSEIDON2_WIDTH;
            let column = bit % POSEIDON2_WIDTH;
            trace.c1[column][row] = M31((integer >> bit) & 1);
        }
    }

    #[test]
    fn honest_variants_have_exactly_zero_complete_residuals_and_degree_25() {
        assert_eq!(POOL_V1_PAYMENT_TWO_ROUND_INTRINSIC_DEGREE, 5 * 5);
        assert_eq!(POOL_V1_PAYMENT_MAX_INTRINSIC_DEGREE, 25);
        assert_eq!(POOL_V1_PAYMENT_SELECTED_ORACLE_INDIVIDUAL_DEGREE, 26);
        assert_eq!(POOL_V1_PAYMENT_ZEROCHECK_INDIVIDUAL_DEGREE, 27);

        let (public, trace) = built_transfer();
        let residuals =
            evaluate_pool_v1_private_transfer_constraint_residuals_v1(&public, &trace.trace)
                .unwrap();
        assert!(residuals.all_zero(), "transfer residuals={residuals:?}");
        assert_eq!(residuals.poseidon_round_pairs.len(), 8_624);
        assert_eq!(residuals.sponge_schedule.len(), 626);
        assert_eq!(residuals.source_aliases.len(), 27);
        assert_eq!(residuals.path_ordering.len(), 160);
        assert_eq!(residuals.public_bindings.len(), 32);
        assert_eq!(residuals.zero_padding.len(), 6_626);
        assert_eq!(residuals.residual_count(), 16_209);

        let (public, trace) = built_withdrawal();
        let residuals =
            evaluate_pool_v1_withdrawal_constraint_residuals_v1(&public, &trace.trace).unwrap();
        assert!(residuals.all_zero(), "withdrawal residuals={residuals:?}");
        assert_eq!(residuals.sponge_schedule.len(), 548);
        assert_eq!(residuals.source_aliases.len(), 26);
        assert_eq!(residuals.public_bindings.len(), 24);
        assert_eq!(residuals.zero_padding.len(), 6_722);
        assert_eq!(residuals.residual_count(), 16_218);
    }

    #[test]
    fn every_private_transfer_semantic_class_has_a_detected_mutation() {
        let (public, honest) = built_transfer();

        let mut trace = honest.clone();
        trace.trace.c1[7][10 * 16 + 6] = trace.trace.c1[7][10 * 16 + 6].add(M31::ONE);
        let residuals =
            evaluate_pool_v1_private_transfer_constraint_residuals_v1(&public, &trace.trace)
                .unwrap();
        assert_class_nonzero(&residuals, PoolV1PaymentResidualClassV1::PoseidonRoundPairs);

        let mut trace = honest.clone();
        trace.trace.c1[0][2 * 16] = trace.trace.c1[0][2 * 16].add(M31::ONE);
        let residuals =
            evaluate_pool_v1_private_transfer_constraint_residuals_v1(&public, &trace.trace)
                .unwrap();
        assert_class_nonzero(&residuals, PoolV1PaymentResidualClassV1::SpongeSchedule);

        let mut trace = honest.clone();
        trace.trace.c1[0][24 * 16 + 12] = trace.trace.c1[0][24 * 16 + 12].add(M31::ONE);
        let residuals =
            evaluate_pool_v1_private_transfer_constraint_residuals_v1(&public, &trace.trace)
                .unwrap();
        assert_class_nonzero(&residuals, PoolV1PaymentResidualClassV1::SourceAliases);

        let mut trace = honest.clone();
        trace.trace.c1[0][POOL_V1_PAYMENT_DIRECTION_ROW_START] = M31(2);
        let residuals =
            evaluate_pool_v1_private_transfer_constraint_residuals_v1(&public, &trace.trace)
                .unwrap();
        assert_class_nonzero(
            &residuals,
            PoolV1PaymentResidualClassV1::DirectionBooleanity,
        );

        let mut trace = honest.clone();
        let bit = &mut trace.trace.c1[0][POOL_V1_PAYMENT_DIRECTION_ROW_START];
        *bit = M31::ONE.sub(*bit);
        let residuals =
            evaluate_pool_v1_private_transfer_constraint_residuals_v1(&public, &trace.trace)
                .unwrap();
        assert!(residuals.class_is_zero(PoolV1PaymentResidualClassV1::DirectionBooleanity));
        assert_class_nonzero(&residuals, PoolV1PaymentResidualClassV1::PathOrdering);

        let mut trace = honest.clone();
        trace.trace.c1[0][POOL_V1_PAYMENT_VALUE_ROW_START] = M31(2);
        let residuals =
            evaluate_pool_v1_private_transfer_constraint_residuals_v1(&public, &trace.trace)
                .unwrap();
        assert_class_nonzero(&residuals, PoolV1PaymentResidualClassV1::ValueBooleanity);

        let mut trace = honest.clone();
        let bit = &mut trace.trace.c1[0][POOL_V1_PAYMENT_VALUE_ROW_START];
        *bit = M31::ONE.sub(*bit);
        let residuals =
            evaluate_pool_v1_private_transfer_constraint_residuals_v1(&public, &trace.trace)
                .unwrap();
        assert!(residuals.class_is_zero(PoolV1PaymentResidualClassV1::ValueBooleanity));
        assert_class_nonzero(&residuals, PoolV1PaymentResidualClassV1::ValueRecomposition);

        for mutate in 0..4 {
            let mut changed = public;
            match mutate {
                0 => changed.anchor_root[0] = changed.anchor_root[0].add(M31::ONE),
                1 => changed.nullifier[0] = changed.nullifier[0].add(M31::ONE),
                2 => {
                    changed.recipient_commitment[0] = changed.recipient_commitment[0].add(M31::ONE)
                }
                3 => changed.change_commitment[0] = changed.change_commitment[0].add(M31::ONE),
                _ => unreachable!(),
            }
            let residuals =
                evaluate_pool_v1_private_transfer_constraint_residuals_v1(&changed, &honest.trace)
                    .unwrap();
            assert_class_nonzero(&residuals, PoolV1PaymentResidualClassV1::PublicBindings);
        }

        let mut trace = honest.clone();
        trace.trace.c1[0][32 * 16] = M31::ONE;
        let residuals =
            evaluate_pool_v1_private_transfer_constraint_residuals_v1(&public, &trace.trace)
                .unwrap();
        assert_class_nonzero(&residuals, PoolV1PaymentResidualClassV1::ZeroPadding);
    }

    #[test]
    fn withdrawal_amount_conservation_and_recipient_padding_mutations_are_detected() {
        let (public, honest) = built_withdrawal();

        let mut changed_public = public;
        changed_public.amount += 1;
        let mut changed_trace = honest.clone();
        set_value_bits(&mut changed_trace.trace, 1, changed_public.amount);
        let residuals = evaluate_pool_v1_withdrawal_constraint_residuals_v1(
            &changed_public,
            &changed_trace.trace,
        )
        .unwrap();
        assert!(residuals.class_is_zero(PoolV1PaymentResidualClassV1::ValueBooleanity));
        assert!(residuals.class_is_zero(PoolV1PaymentResidualClassV1::ValueRecomposition));
        assert_class_nonzero(&residuals, PoolV1PaymentResidualClassV1::Conservation);

        let mut trace = honest.clone();
        trace.trace.c1[0][26 * 16] = M31::ONE;
        let residuals =
            evaluate_pool_v1_withdrawal_constraint_residuals_v1(&public, &trace.trace).unwrap();
        assert_class_nonzero(&residuals, PoolV1PaymentResidualClassV1::ZeroPadding);
    }
}
