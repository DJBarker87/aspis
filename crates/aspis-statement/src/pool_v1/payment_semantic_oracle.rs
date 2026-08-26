//! Three-view non-Poseidon oracle for the Pool V1 Tag-73 payment trace.
//!
//! This compiles the routed payment trace into the frozen
//! `(z, successor(z), xor12(z))` opening geometry.  The 94 base-field
//! residual lanes pack injectively into 24 QM31 lanes; the single copy LogUp
//! residual is lane 25.  Together with the four frozen Poseidon lanes this
//! fits the existing 29-lane theta composition without adding a proof claim.
//! This remains a host/compiler foundation until the prover and deployed
//! verifier select it from an authenticated Pool profile.

use alloc::vec::Vec;

use aspis_core::field::{qm31_pack_base4, CM31, M31, QM31};

use crate::{
    constraints_v4::multilinear_evaluate_qm31,
    logup::{build_copy_logup_helper, CopyLogUpRow, LogUpError},
    poseidon2::{Digest, DIGEST_ELEMS, POSEIDON2_WIDTH, RATE},
    state_only_poseidon::{state_only_poseidon_openings_at_point, StateOnlyPoseidonOpenings},
    state_only_trace::StateOnlyTraceFoundation,
};

use super::{
    payment_relation::{PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1},
    payment_semantic_registry::{
        build_pool_v1_payment_semantic_registry_v1, pool_v1_payment_aux_cell_is_used_v1,
        pool_v1_payment_conservation_aux_v1, pool_v1_payment_copy_rows_v1,
        pool_v1_payment_path_aux_v1, pool_v1_payment_value_aux_v1, PoolV1PaymentCopyTupleV1,
        PoolV1PaymentSemanticRegistryErrorV1, PoolV1PaymentSemanticRegistryV1,
        PoolV1PaymentTupleLimbV1, POOL_V1_PAYMENT_BASE_SEMANTIC_LANES,
        POOL_V1_PAYMENT_PACKED_BASE_LANES, POOL_V1_PAYMENT_RANDOMIZED_SEMANTIC_LANES,
        POOL_V1_PAYMENT_SEMANTIC_LANES, POOL_V1_PAYMENT_THETA_LANES,
    },
    payment_trace::{
        PoolV1PaymentTraceVariantV1, POOL_V1_PAYMENT_TRACE_BLOCKS,
        POOL_V1_PAYMENT_TRACE_BLOCK_ROWS, POOL_V1_PAYMENT_TRACE_PERMUTATION_ROWS,
        POOL_V1_PAYMENT_TRACE_ROWS,
    },
};

pub const POOL_V1_PAYMENT_INITIAL_LANES: usize = 16;
pub const POOL_V1_PAYMENT_ABSORPTION_ZERO_LANES: usize = 16;
pub const POOL_V1_PAYMENT_MERKLE_LANES: usize = 1 + 2 * DIGEST_ELEMS;
pub const POOL_V1_PAYMENT_DIRECT_RANGE_LANES: usize = 3 * 10 + 3;
pub const POOL_V1_PAYMENT_VALUE_LANES: usize = 2;
pub const POOL_V1_PAYMENT_PUBLIC_DIGEST_LANES: usize = DIGEST_ELEMS;
pub const POOL_V1_PAYMENT_PUBLIC_SCALAR_LANES: usize = 2;

/// Successor composition gives degree ten per trace opening.  The range
/// Booleanity branch therefore has degree twenty; its row selector raises the
/// bound to 21 and the outer zerocheck equality to 22.  The separate frozen
/// two-round Poseidon oracle still dominates the complete relation at 27.
pub const POOL_V1_PAYMENT_SEMANTIC_ORACLE_INDIVIDUAL_DEGREE: usize = 21;
pub const POOL_V1_PAYMENT_SEMANTIC_ZEROCHECK_INDIVIDUAL_DEGREE: usize = 22;

const _: () = assert!(
    POOL_V1_PAYMENT_INITIAL_LANES
        + POOL_V1_PAYMENT_ABSORPTION_ZERO_LANES
        + POOL_V1_PAYMENT_MERKLE_LANES
        + POOL_V1_PAYMENT_DIRECT_RANGE_LANES
        + POOL_V1_PAYMENT_VALUE_LANES
        + POOL_V1_PAYMENT_PUBLIC_DIGEST_LANES
        + POOL_V1_PAYMENT_PUBLIC_SCALAR_LANES
        == POOL_V1_PAYMENT_BASE_SEMANTIC_LANES
);
const _: () = assert!(POOL_V1_PAYMENT_BASE_SEMANTIC_LANES == 94);
const _: () = assert!(POOL_V1_PAYMENT_PACKED_BASE_LANES == 24);
const _: () = assert!(POOL_V1_PAYMENT_RANDOMIZED_SEMANTIC_LANES == 25);
const _: () = assert!(POOL_V1_PAYMENT_SEMANTIC_LANES == 95);
const _: () = assert!(POOL_V1_PAYMENT_THETA_LANES == 29);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PaymentSemanticOpeningsV1 {
    pub c1: StateOnlyPoseidonOpenings,
    pub h1_z: QM31,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoolV1PaymentSemanticPreparedV1 {
    registry: PoolV1PaymentSemanticRegistryV1,
}

impl PoolV1PaymentSemanticPreparedV1 {
    pub fn variant(&self) -> PoolV1PaymentTraceVariantV1 {
        self.registry.variant
    }

    pub fn registry(&self) -> &PoolV1PaymentSemanticRegistryV1 {
        &self.registry
    }
}

pub fn prepare_pool_v1_payment_semantic_oracle_v1(
    variant: PoolV1PaymentTraceVariantV1,
) -> Result<PoolV1PaymentSemanticPreparedV1, PoolV1PaymentSemanticErrorV1> {
    let registry = build_pool_v1_payment_semantic_registry_v1(variant)?;
    Ok(PoolV1PaymentSemanticPreparedV1 { registry })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoolV1PaymentSemanticResidualsV1 {
    pub initial: [QM31; POOL_V1_PAYMENT_INITIAL_LANES],
    pub absorption_zero: [QM31; POOL_V1_PAYMENT_ABSORPTION_ZERO_LANES],
    pub merkle: [QM31; POOL_V1_PAYMENT_MERKLE_LANES],
    pub direct_range: [QM31; POOL_V1_PAYMENT_DIRECT_RANGE_LANES],
    pub value: [QM31; POOL_V1_PAYMENT_VALUE_LANES],
    pub public_digest: [QM31; POOL_V1_PAYMENT_PUBLIC_DIGEST_LANES],
    pub public_scalar: [QM31; POOL_V1_PAYMENT_PUBLIC_SCALAR_LANES],
    pub copy: QM31,
}

impl PoolV1PaymentSemanticResidualsV1 {
    pub fn all_zero(&self) -> bool {
        self.initial
            .iter()
            .chain(&self.absorption_zero)
            .chain(&self.merkle)
            .chain(&self.direct_range)
            .chain(&self.value)
            .chain(&self.public_digest)
            .chain(&self.public_scalar)
            .all(|value| *value == QM31::ZERO)
            && self.copy == QM31::ZERO
    }

    pub fn packed_base_lanes(&self) -> [QM31; POOL_V1_PAYMENT_PACKED_BASE_LANES] {
        let source = self
            .initial
            .iter()
            .chain(&self.absorption_zero)
            .chain(&self.merkle)
            .chain(&self.direct_range)
            .chain(&self.value)
            .chain(&self.public_digest)
            .chain(&self.public_scalar)
            .copied()
            .collect::<Vec<_>>();
        debug_assert_eq!(source.len(), POOL_V1_PAYMENT_BASE_SEMANTIC_LANES);
        core::array::from_fn(|group| {
            let start = 4 * group;
            let end = core::cmp::min(start + 4, source.len());
            qm31_pack_base4(&source[start..end])
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PaymentSemanticErrorV1 {
    Shape,
    WrongVariant,
    InvalidPublicAmount,
    Registry(PoolV1PaymentSemanticRegistryErrorV1),
    CopyEndpointOverflow { row: u16 },
    LogUp(LogUpError),
}

impl From<PoolV1PaymentSemanticRegistryErrorV1> for PoolV1PaymentSemanticErrorV1 {
    fn from(error: PoolV1PaymentSemanticRegistryErrorV1) -> Self {
        Self::Registry(error)
    }
}

impl From<LogUpError> for PoolV1PaymentSemanticErrorV1 {
    fn from(error: LogUpError) -> Self {
        Self::LogUp(error)
    }
}

#[derive(Clone, Copy)]
struct SemanticPublicV1 {
    variant: PoolV1PaymentTraceVariantV1,
    anchor: Digest,
    nullifier: Digest,
    asset_id: M31,
    recipient: Option<Digest>,
    change: Digest,
    withdrawal_amount: Option<u32>,
}

#[inline(always)]
fn lift(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}

#[derive(Clone)]
struct SelectorsV1 {
    high: [QM31; 64],
    low: [QM31; 16],
}

impl SelectorsV1 {
    fn expand<const N: usize>(coordinates: &[QM31]) -> [QM31; N] {
        let mut weights = [QM31::ZERO; N];
        weights[0] = QM31::ONE;
        let mut len = 1usize;
        for coordinate in coordinates {
            for index in (0..len).rev() {
                let parent = weights[index];
                let right = parent.mul(*coordinate);
                weights[2 * index] = parent.sub(right);
                weights[2 * index + 1] = right;
            }
            len *= 2;
        }
        weights
    }

    fn at_point(point: &[QM31; 10]) -> Self {
        Self {
            high: Self::expand(&point[..6]),
            low: Self::expand(&point[6..]),
        }
    }

    #[inline(always)]
    fn row(&self, row: usize) -> QM31 {
        self.high[row >> 4].mul(self.low[row & 15])
    }
}

fn first_sponge(block: usize, variant: PoolV1PaymentTraceVariantV1) -> Option<(M31, usize)> {
    use crate::spend::{DOMAIN_NOTE, DOMAIN_NULLIFIER, DOMAIN_OWNER_KEY};
    match block {
        0 => Some((DOMAIN_OWNER_KEY, 8)),
        1 => Some((DOMAIN_NOTE, 18)),
        24 => Some((DOMAIN_NULLIFIER, 16)),
        26 if variant == PoolV1PaymentTraceVariantV1::PrivateTransfer => Some((DOMAIN_NOTE, 18)),
        29 => Some((DOMAIN_NOTE, 18)),
        _ => None,
    }
}

fn fixed_zero_block(block: usize, variant: PoolV1PaymentTraceVariantV1) -> bool {
    (32..49).contains(&block)
        || (variant == PoolV1PaymentTraceVariantV1::Withdrawal && (26..=28).contains(&block))
}

fn expected_initial_limb(
    block: usize,
    lane: usize,
    variant: PoolV1PaymentTraceVariantV1,
) -> Option<M31> {
    if let Some((domain, length)) = first_sponge(block, variant) {
        let mut state = [M31::ZERO; POSEIDON2_WIDTH];
        state[RATE] = domain;
        state[RATE + 1] = M31(length as u32);
        return Some(state[lane]);
    }
    if (4..24).contains(&block) {
        return (lane < RATE).then_some(M31::ZERO);
    }
    fixed_zero_block(block, variant).then_some(M31::ZERO)
}

fn absorption_length(block: usize, variant: PoolV1PaymentTraceVariantV1) -> usize {
    match block {
        0 | 1 | 2 | 4..=25 | 26 | 27 | 29 | 30 => {
            if variant == PoolV1PaymentTraceVariantV1::Withdrawal && (26..=27).contains(&block) {
                0
            } else {
                8
            }
        }
        3 | 28 | 31 => {
            if variant == PoolV1PaymentTraceVariantV1::Withdrawal && block == 28 {
                0
            } else {
                2
            }
        }
        32..=48 => 0,
        _ => 0,
    }
}

#[derive(Clone, Copy)]
struct CopyRowExtensionV1 {
    producer_values: [QM31; 2],
    producer_weights: [QM31; 2],
    consumer_values: [QM31; 2],
    consumer_weights: [QM31; 2],
}

fn copy_residual(row: CopyRowExtensionV1, helper: QM31, chi: QM31) -> QM31 {
    let d = [
        chi.sub(row.producer_values[0]),
        chi.sub(row.producer_values[1]),
        chi.sub(row.consumer_values[0]),
        chi.sub(row.consumer_values[1]),
    ];
    let producer_denominator = d[0].mul(d[1]);
    let consumer_denominator = d[2].mul(d[3]);
    let producer_numerator = row.producer_weights[0]
        .mul(d[1])
        .add(row.producer_weights[1].mul(d[0]));
    let consumer_numerator = row.consumer_weights[0]
        .mul(d[3])
        .add(row.consumer_weights[1].mul(d[2]));
    producer_denominator
        .mul(helper.mul(consumer_denominator).add(consumer_numerator))
        .sub(consumer_denominator.mul(producer_numerator))
}

fn compressed_opened_tuple(
    tuple: PoolV1PaymentCopyTupleV1,
    tag: M31,
    selector: QM31,
    openings: &[QM31; POSEIDON2_WIDTH],
    powers: &[QM31; POSEIDON2_WIDTH],
) -> QM31 {
    let mut value = selector.mul_m31(tag);
    for (limb, power) in tuple.limbs.into_iter().zip(powers) {
        let opened = match limb {
            PoolV1PaymentTupleLimbV1::Zero => QM31::ZERO,
            PoolV1PaymentTupleLimbV1::Constant(constant) => lift(constant),
            PoolV1PaymentTupleLimbV1::AffineCell {
                cell,
                scale,
                offset,
            } => openings[usize::from(cell.column)]
                .mul_m31(scale)
                .add(lift(offset)),
        };
        value = value.add(selector.mul(opened).mul(*power));
    }
    value
}

fn copy_terminal(
    prepared: &PoolV1PaymentSemanticPreparedV1,
    openings: &[QM31; POSEIDON2_WIDTH],
    selectors: &SelectorsV1,
    lambda: QM31,
) -> Result<CopyRowExtensionV1, PoolV1PaymentSemanticErrorV1> {
    let mut powers = [QM31::ZERO; POSEIDON2_WIDTH];
    let mut power = lambda;
    for output in &mut powers {
        *output = power;
        power = power.mul(lambda);
    }
    let mut row = CopyRowExtensionV1 {
        producer_values: [QM31::ZERO; 2],
        producer_weights: [QM31::ZERO; 2],
        consumer_values: [QM31::ZERO; 2],
        consumer_weights: [QM31::ZERO; 2],
    };
    let mut producer_arity = [0u8; POOL_V1_PAYMENT_TRACE_ROWS];
    let mut consumer_arity = [0u8; POOL_V1_PAYMENT_TRACE_ROWS];
    for link in &prepared.registry.links {
        for (tuple, arity, values, weights) in [
            (
                link.producer,
                &mut producer_arity,
                &mut row.producer_values,
                &mut row.producer_weights,
            ),
            (
                link.consumer,
                &mut consumer_arity,
                &mut row.consumer_values,
                &mut row.consumer_weights,
            ),
        ] {
            let endpoint_row = usize::from(tuple.row);
            let slot = usize::from(arity[endpoint_row]);
            if slot >= 2 {
                return Err(PoolV1PaymentSemanticErrorV1::CopyEndpointOverflow { row: tuple.row });
            }
            arity[endpoint_row] += 1;
            let selector = selectors.row(endpoint_row);
            weights[slot] = weights[slot].add(selector);
            values[slot] = values[slot].add(compressed_opened_tuple(
                tuple, link.tag, selector, openings, &powers,
            ));
        }
    }
    Ok(row)
}

fn evaluate_prepared(
    public: SemanticPublicV1,
    openings: &PoolV1PaymentSemanticOpeningsV1,
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    prepared: &PoolV1PaymentSemanticPreparedV1,
) -> Result<PoolV1PaymentSemanticResidualsV1, PoolV1PaymentSemanticErrorV1> {
    if public.variant != prepared.variant() {
        return Err(PoolV1PaymentSemanticErrorV1::WrongVariant);
    }
    if public
        .withdrawal_amount
        .is_some_and(|amount| amount == 0 || amount >= (1 << 30))
    {
        return Err(PoolV1PaymentSemanticErrorV1::InvalidPublicAmount);
    }
    let selectors = SelectorsV1::at_point(point);

    let mut initial = [QM31::ZERO; POOL_V1_PAYMENT_INITIAL_LANES];
    for block in 0..49 {
        let selector = selectors.row(block * POOL_V1_PAYMENT_TRACE_BLOCK_ROWS);
        for lane in 0..POSEIDON2_WIDTH {
            if let Some(expected) = expected_initial_limb(block, lane, public.variant) {
                initial[lane] =
                    initial[lane].add(selector.mul(openings.c1.z[lane].sub(lift(expected))));
            }
        }
    }
    // The auxiliary region has a sparse declared layout. Fold every unused
    // cell into the corresponding column lane; at a Boolean row the selectors
    // are disjoint, so zero of this lane fixes that cell to zero without
    // allocating another semantic lane.
    for row in POOL_V1_PAYMENT_TRACE_PERMUTATION_ROWS..POOL_V1_PAYMENT_TRACE_ROWS {
        let selector = selectors.row(row);
        for lane in 0..POSEIDON2_WIDTH {
            if !pool_v1_payment_aux_cell_is_used_v1(row, lane) {
                initial[lane] = initial[lane].add(selector.mul(openings.c1.z[lane]));
            }
        }
    }

    let mut absorption_zero = [QM31::ZERO; POOL_V1_PAYMENT_ABSORPTION_ZERO_LANES];
    for block in 0..49 {
        let selector = selectors.row(block * POOL_V1_PAYMENT_TRACE_BLOCK_ROWS + 12);
        let absorbed = absorption_length(block, public.variant);
        for lane in absorbed..POSEIDON2_WIDTH {
            absorption_zero[lane] = absorption_zero[lane].add(selector.mul(openings.c1.z[lane]));
        }
    }
    // Rows 13..15 of every permutation block are canonical padding. They are
    // outside the two-round Poseidon oracle and must not carry free witness
    // values.
    for block in 0..POOL_V1_PAYMENT_TRACE_BLOCKS {
        for local_row in 13..POOL_V1_PAYMENT_TRACE_BLOCK_ROWS {
            let selector = selectors.row(block * POOL_V1_PAYMENT_TRACE_BLOCK_ROWS + local_row);
            for lane in 0..POSEIDON2_WIDTH {
                absorption_zero[lane] =
                    absorption_zero[lane].add(selector.mul(openings.c1.z[lane]));
            }
        }
    }

    let merkle_selector = (0..20).fold(QM31::ZERO, |sum, level| {
        sum.add(selectors.row(usize::from(
            pool_v1_payment_path_aux_v1(level).unwrap().bit.row,
        )))
    });
    let bit = openings.c1.z[0];
    let mut merkle = [QM31::ZERO; POOL_V1_PAYMENT_MERKLE_LANES];
    merkle[0] = merkle_selector.mul(bit.mul(bit.sub(QM31::ONE)));
    for lane in 0..DIGEST_ELEMS {
        let current = openings.c1.z[1 + lane];
        let sibling = openings.c1.xor12_z[lane];
        let delta = sibling.sub(current);
        merkle[1 + lane] =
            merkle_selector.mul(openings.c1.succ_z[lane].sub(current.add(bit.mul(delta))));
        merkle[1 + DIGEST_ELEMS + lane] =
            merkle_selector.mul(openings.c1.succ_z[RATE + lane].sub(sibling.sub(bit.mul(delta))));
    }

    let value_selectors: [QM31; 3] = core::array::from_fn(|value| {
        selectors.row(usize::from(
            pool_v1_payment_value_aux_v1(value).unwrap().source.row,
        ))
    });
    let range_selector = value_selectors.iter().copied().fold(QM31::ZERO, QM31::add);
    let views = [&openings.c1.z, &openings.c1.succ_z, &openings.c1.xor12_z];
    let mut direct_range = [QM31::ZERO; POOL_V1_PAYMENT_DIRECT_RANGE_LANES];
    for (view_index, view) in views.into_iter().enumerate() {
        for bit_index in 0..10 {
            direct_range[view_index * 10 + bit_index] =
                range_selector.mul(view[bit_index].mul(view[bit_index].sub(QM31::ONE)));
        }
    }

    let reconstructed_value = (0..10).fold(QM31::ZERO, |sum, bit_index| {
        sum.add(openings.c1.z[bit_index].mul_m31(M31(1 << bit_index)))
            .add(openings.c1.succ_z[bit_index].mul_m31(M31(1 << (10 + bit_index))))
            .add(openings.c1.xor12_z[bit_index].mul_m31(M31(1 << (20 + bit_index))))
    });
    direct_range[30] = value_selectors
        .iter()
        .copied()
        .fold(QM31::ZERO, |sum, selector| {
            sum.add(selector.mul(openings.c1.z[10].sub(reconstructed_value)))
        });
    // Only the base-row view carries the full 30-bit source in column ten.
    direct_range[31] = range_selector.mul(openings.c1.succ_z[10]);
    direct_range[32] = range_selector.mul(openings.c1.xor12_z[10]);

    let conservation_aux = pool_v1_payment_conservation_aux_v1();
    let conservation_selector = selectors.row(usize::from(conservation_aux.input.row));
    let value = [
        conservation_selector.mul(openings.c1.z[0].sub(openings.c1.z[1]).sub(openings.c1.z[2])),
        conservation_selector.mul(openings.c1.succ_z[0].sub(openings.c1.succ_z[1])),
    ];

    let mut public_digest = [QM31::ZERO; POOL_V1_PAYMENT_PUBLIC_DIGEST_LANES];
    let digest_rows = [
        (23usize, Some(public.anchor)),
        (25, Some(public.nullifier)),
        (28, public.recipient),
        (31, Some(public.change)),
    ];
    for (block, digest) in digest_rows {
        let Some(digest) = digest else {
            continue;
        };
        let selector = selectors.row(block * POOL_V1_PAYMENT_TRACE_BLOCK_ROWS + 11);
        for lane in 0..DIGEST_ELEMS {
            public_digest[lane] =
                public_digest[lane].add(selector.mul(openings.c1.z[lane].sub(lift(digest[lane]))));
        }
    }

    let input_asset_selector = selectors.row(2 * 16 + 12);
    let mut output_scalar = selectors
        .row(30 * 16 + 12)
        .mul(openings.c1.z[1].sub(lift(public.asset_id)));
    if public.variant == PoolV1PaymentTraceVariantV1::PrivateTransfer {
        output_scalar = output_scalar.add(
            selectors
                .row(27 * 16 + 12)
                .mul(openings.c1.z[1].sub(lift(public.asset_id))),
        );
    } else if let Some(amount) = public.withdrawal_amount {
        output_scalar =
            output_scalar.add(value_selectors[1].mul(openings.c1.z[10].sub(lift(M31(amount)))));
    }
    let public_scalar = [
        input_asset_selector.mul(openings.c1.z[1].sub(lift(public.asset_id))),
        output_scalar,
    ];

    let terminal = copy_terminal(prepared, &openings.c1.z, &selectors, lambda)?;
    // The cleared LogUp equation must hold on every row. On a row with no
    // producer or consumer endpoints its four weights are zero, so this
    // reduces to `chi^4 * h1 = 0`. Masking those rows would leave arbitrary
    // helper values available to cancel an active-row mismatch while keeping
    // the separately checked global helper sum equal to zero.
    let copy = copy_residual(terminal, openings.h1_z, chi);

    Ok(PoolV1PaymentSemanticResidualsV1 {
        initial,
        absorption_zero,
        merkle,
        direct_range,
        value,
        public_digest,
        public_scalar,
        copy,
    })
}

pub fn evaluate_pool_v1_private_transfer_semantic_oracle_v1(
    public: &PoolV1PrivateTransferPublicV1,
    openings: &PoolV1PaymentSemanticOpeningsV1,
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    prepared: &PoolV1PaymentSemanticPreparedV1,
) -> Result<PoolV1PaymentSemanticResidualsV1, PoolV1PaymentSemanticErrorV1> {
    evaluate_prepared(
        SemanticPublicV1 {
            variant: PoolV1PaymentTraceVariantV1::PrivateTransfer,
            anchor: public.anchor_root,
            nullifier: public.nullifier,
            asset_id: public.asset_id,
            recipient: Some(public.recipient_commitment),
            change: public.change_commitment,
            withdrawal_amount: None,
        },
        openings,
        point,
        lambda,
        chi,
        prepared,
    )
}

pub fn evaluate_pool_v1_withdrawal_semantic_oracle_v1(
    public: &PoolV1WithdrawalPublicV1,
    openings: &PoolV1PaymentSemanticOpeningsV1,
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    prepared: &PoolV1PaymentSemanticPreparedV1,
) -> Result<PoolV1PaymentSemanticResidualsV1, PoolV1PaymentSemanticErrorV1> {
    evaluate_prepared(
        SemanticPublicV1 {
            variant: PoolV1PaymentTraceVariantV1::Withdrawal,
            anchor: public.anchor_root,
            nullifier: public.nullifier,
            asset_id: public.asset_id,
            recipient: None,
            change: public.change_commitment,
            withdrawal_amount: Some(public.amount),
        },
        openings,
        point,
        lambda,
        chi,
        prepared,
    )
}

pub fn build_pool_v1_payment_copy_helper_v1(
    prepared: &PoolV1PaymentSemanticPreparedV1,
    trace: &StateOnlyTraceFoundation,
    lambda: QM31,
    chi: QM31,
) -> Result<Vec<QM31>, PoolV1PaymentSemanticErrorV1> {
    if trace
        .c1
        .iter()
        .any(|column| column.len() != POOL_V1_PAYMENT_TRACE_ROWS)
    {
        return Err(PoolV1PaymentSemanticErrorV1::Shape);
    }
    let rows: Vec<CopyLogUpRow> = pool_v1_payment_copy_rows_v1(&prepared.registry, trace, lambda)?;
    Ok(build_copy_logup_helper(&rows, chi)?)
}

pub fn pool_v1_payment_semantic_openings_at_point_v1(
    trace: &StateOnlyTraceFoundation,
    h1: &[QM31],
    point: &[QM31; 10],
) -> Option<PoolV1PaymentSemanticOpeningsV1> {
    Some(PoolV1PaymentSemanticOpeningsV1 {
        c1: state_only_poseidon_openings_at_point(&trace.c1, point)?,
        h1_z: multilinear_evaluate_qm31(h1, point)?,
    })
}

pub fn pool_v1_payment_copy_helper_sum_v1(h1: &[QM31]) -> Option<QM31> {
    (h1.len() == POOL_V1_PAYMENT_TRACE_ROWS).then(|| h1.iter().copied().fold(QM31::ZERO, QM31::add))
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
            PoolV1PaymentRelationContextV1, PoolV1PaymentRuntimeBindingV1,
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
        PoolV1PaymentRelationContextV1<'static>,
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
        let anchor_root = pool_v1_membership_root_v1(leaf, &witness.input.membership).unwrap();
        let public = PoolV1PrivateTransferPublicV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            anchor_sequence: 42,
            anchor_root,
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
        let context = PoolV1PaymentRelationContextV1 {
            runtime_binding: PoolV1PaymentRuntimeBindingV1 {
                pool: public.pool,
                deployment_domain: public.deployment_domain,
                anchor_sequence: public.anchor_sequence,
                anchor_root: public.anchor_root,
                asset_id: public.asset_id,
            },
            spent_nullifiers: &[],
        };
        (public, witness, context)
    }

    fn withdrawal_fixture() -> (
        PoolV1WithdrawalPublicV1,
        PoolV1WithdrawalWitnessV1,
        PoolV1PaymentRelationContextV1<'static>,
    ) {
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
        let anchor_root = pool_v1_membership_root_v1(leaf, &witness.input.membership).unwrap();
        let public = PoolV1WithdrawalPublicV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            anchor_sequence: 42,
            anchor_root,
            nullifier: pool_v1_nullifier(&witness.input.nullifier_key, &witness.input.salt),
            asset_id,
            amount: 250,
            destination_token_account: [9; 32],
            change_commitment: pool_v1_note_commitment(
                &witness.change.owner_key,
                witness.change.value,
                asset_id,
                &witness.change.salt,
            ),
        };
        let context = PoolV1PaymentRelationContextV1 {
            runtime_binding: PoolV1PaymentRuntimeBindingV1 {
                pool: public.pool,
                deployment_domain: public.deployment_domain,
                anchor_sequence: public.anchor_sequence,
                anchor_root: public.anchor_root,
                asset_id: public.asset_id,
            },
            spent_nullifiers: &[],
        };
        (public, witness, context)
    }

    fn challenges() -> (QM31, QM31) {
        (
            QM31 {
                c0: CM31::new(M31(123), M31(456)),
                c1: CM31::new(M31(789), M31(1_011)),
            },
            QM31 {
                c0: CM31::new(M31(1_213), M31(1_415)),
                c1: CM31::new(M31(1_617), M31(1_819)),
            },
        )
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

    #[test]
    fn honest_variants_zero_all_95_semantic_lanes_on_every_boolean_row() {
        let (lambda, chi) = challenges();

        let (public, witness, context) = transfer_fixture();
        let trace = build_pool_v1_private_transfer_trace_v1(&public, &witness, context).unwrap();
        let prepared = prepare_pool_v1_payment_semantic_oracle_v1(
            PoolV1PaymentTraceVariantV1::PrivateTransfer,
        )
        .unwrap();
        let h1 =
            build_pool_v1_payment_copy_helper_v1(&prepared, &trace.trace, lambda, chi).unwrap();
        assert_eq!(pool_v1_payment_copy_helper_sum_v1(&h1), Some(QM31::ZERO));
        for row in 0..POOL_V1_PAYMENT_TRACE_ROWS {
            let point = boolean_point(row);
            let openings =
                pool_v1_payment_semantic_openings_at_point_v1(&trace.trace, &h1, &point).unwrap();
            let residuals = evaluate_pool_v1_private_transfer_semantic_oracle_v1(
                &public, &openings, &point, lambda, chi, &prepared,
            )
            .unwrap();
            assert!(residuals.all_zero(), "transfer row {row}: {residuals:?}");
            assert_eq!(residuals.packed_base_lanes().len(), 24);
        }

        let (public, witness, context) = withdrawal_fixture();
        let trace = build_pool_v1_withdrawal_trace_v1(&public, &witness, context).unwrap();
        let prepared =
            prepare_pool_v1_payment_semantic_oracle_v1(PoolV1PaymentTraceVariantV1::Withdrawal)
                .unwrap();
        let h1 =
            build_pool_v1_payment_copy_helper_v1(&prepared, &trace.trace, lambda, chi).unwrap();
        assert_eq!(pool_v1_payment_copy_helper_sum_v1(&h1), Some(QM31::ZERO));
        for row in 0..POOL_V1_PAYMENT_TRACE_ROWS {
            let point = boolean_point(row);
            let openings =
                pool_v1_payment_semantic_openings_at_point_v1(&trace.trace, &h1, &point).unwrap();
            let residuals = evaluate_pool_v1_withdrawal_semantic_oracle_v1(
                &public, &openings, &point, lambda, chi, &prepared,
            )
            .unwrap();
            assert!(residuals.all_zero(), "withdrawal row {row}: {residuals:?}");
        }
    }

    #[test]
    fn withdrawal_amount_is_bound_at_its_exact_routed_row() {
        let (lambda, chi) = challenges();
        let (public, witness, context) = withdrawal_fixture();
        let trace = build_pool_v1_withdrawal_trace_v1(&public, &witness, context).unwrap();
        let prepared =
            prepare_pool_v1_payment_semantic_oracle_v1(PoolV1PaymentTraceVariantV1::Withdrawal)
                .unwrap();
        let h1 =
            build_pool_v1_payment_copy_helper_v1(&prepared, &trace.trace, lambda, chi).unwrap();
        let amount_row = usize::from(pool_v1_payment_value_aux_v1(1).unwrap().source.row);
        let point = boolean_point(amount_row);
        let openings =
            pool_v1_payment_semantic_openings_at_point_v1(&trace.trace, &h1, &point).unwrap();
        let mut changed = public;
        changed.amount += 1;
        let residuals = evaluate_pool_v1_withdrawal_semantic_oracle_v1(
            &changed, &openings, &point, lambda, chi, &prepared,
        )
        .unwrap();
        assert!(!residuals.all_zero());
        assert_ne!(residuals.public_scalar[1], QM31::ZERO);

        changed.amount = 0;
        assert_eq!(
            evaluate_pool_v1_withdrawal_semantic_oracle_v1(
                &changed, &openings, &point, lambda, chi, &prepared,
            ),
            Err(PoolV1PaymentSemanticErrorV1::InvalidPublicAmount)
        );
    }

    #[test]
    fn inactive_copy_helper_rows_are_constrained_even_when_their_sum_is_zero() {
        let (lambda, chi) = challenges();
        let (public, witness, context) = transfer_fixture();
        let trace = build_pool_v1_private_transfer_trace_v1(&public, &witness, context).unwrap();
        let prepared = prepare_pool_v1_payment_semantic_oracle_v1(
            PoolV1PaymentTraceVariantV1::PrivateTransfer,
        )
        .unwrap();
        let mut active = [false; POOL_V1_PAYMENT_TRACE_ROWS];
        for link in &prepared.registry().links {
            active[usize::from(link.producer.row)] = true;
            active[usize::from(link.consumer.row)] = true;
        }
        let inactive = active
            .iter()
            .enumerate()
            .filter_map(|(row, is_active)| (!is_active).then_some(row))
            .take(2)
            .collect::<Vec<_>>();
        assert_eq!(inactive.len(), 2);

        let mut h1 = alloc::vec![QM31::ZERO; POOL_V1_PAYMENT_TRACE_ROWS];
        h1[inactive[0]] = QM31::ONE;
        h1[inactive[1]] = QM31::ZERO.sub(QM31::ONE);
        assert_eq!(pool_v1_payment_copy_helper_sum_v1(&h1), Some(QM31::ZERO));

        for row in inactive {
            let point = boolean_point(row);
            let openings =
                pool_v1_payment_semantic_openings_at_point_v1(&trace.trace, &h1, &point).unwrap();
            let residuals = evaluate_pool_v1_private_transfer_semantic_oracle_v1(
                &public, &openings, &point, lambda, chi, &prepared,
            )
            .unwrap();
            assert_ne!(residuals.copy, QM31::ZERO, "inactive helper row {row}");
        }
    }

    #[test]
    fn permutation_and_auxiliary_padding_cells_are_constrained() {
        let (lambda, chi) = challenges();
        let (public, witness, context) = transfer_fixture();
        let honest = build_pool_v1_private_transfer_trace_v1(&public, &witness, context).unwrap();
        let prepared = prepare_pool_v1_payment_semantic_oracle_v1(
            PoolV1PaymentTraceVariantV1::PrivateTransfer,
        )
        .unwrap();
        let h1 =
            build_pool_v1_payment_copy_helper_v1(&prepared, &honest.trace, lambda, chi).unwrap();

        for (row, lane) in [
            (13usize, 7usize),
            (POOL_V1_PAYMENT_TRACE_ROWS - 1, POSEIDON2_WIDTH - 1),
        ] {
            assert!(
                row < POOL_V1_PAYMENT_TRACE_PERMUTATION_ROWS
                    || !pool_v1_payment_aux_cell_is_used_v1(row, lane)
            );
            let mut changed = honest.trace.clone();
            changed.c1[lane][row] = M31(1);
            let point = boolean_point(row);
            let openings =
                pool_v1_payment_semantic_openings_at_point_v1(&changed, &h1, &point).unwrap();
            let residuals = evaluate_pool_v1_private_transfer_semantic_oracle_v1(
                &public, &openings, &point, lambda, chi, &prepared,
            )
            .unwrap();
            assert!(!residuals.all_zero(), "padding cell ({row}, {lane})");
        }
    }
}
