//! Allocation-bounded SBF-safe terminal for the native Pool V1 Tag-73
//! payment relations.
//!
//! Runtime evaluation consumes only checked-in copy patterns, endpoints and
//! active-row masks. The allocation-heavy host registry and oracle remain an
//! independent compiler/reference boundary and are not linked on SBF.

use alloc::boxed::Box;

use aspis_core::{
    field::{qm31_pack_base4, PreparedQm31Multiplier, CM31, M31, QM31},
    state_only_hiding::{state_only_selected_mask_value, STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS},
};

use crate::{
    poseidon2::{Digest, DIGEST_ELEMS, POSEIDON2_WIDTH, RATE},
    spend::{DOMAIN_NOTE, DOMAIN_NULLIFIER, DOMAIN_OWNER_KEY},
    state_only_poseidon::{
        evaluate_state_only_poseidon_oracle_projected, StateOnlyPoseidonOpenings,
        StateOnlyPoseidonSelectors,
    },
};

use super::payment_relation::{PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1};

pub const POOL_V1_PAYMENT_TERMINAL_ROWS: usize = 1024;
pub const POOL_V1_PAYMENT_TERMINAL_C1_COLUMNS: usize = 16;
pub const POOL_V1_PAYMENT_TERMINAL_POINTS: usize = 3;
pub const POOL_V1_PAYMENT_SELECTED_TERMINAL_COLUMNS: usize =
    POOL_V1_PAYMENT_TERMINAL_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + 2;
pub const POOL_V1_PAYMENT_SELECTED_TERMINAL_CLAIMS: usize =
    POOL_V1_PAYMENT_TERMINAL_POINTS * POOL_V1_PAYMENT_SELECTED_TERMINAL_COLUMNS;
pub const POOL_V1_PAYMENT_SOURCE_SEMANTIC_LANES: usize = 94;
pub const POOL_V1_PAYMENT_PACKED_SEMANTIC_LANES: usize = 24;
pub const POOL_V1_PAYMENT_POSEIDON_LANES: usize = 4;
pub const POOL_V1_PAYMENT_COPY_LANES: usize = 1;
pub const POOL_V1_PAYMENT_THETA_LANES: usize = POOL_V1_PAYMENT_POSEIDON_LANES
    + POOL_V1_PAYMENT_PACKED_SEMANTIC_LANES
    + POOL_V1_PAYMENT_COPY_LANES;
pub const POOL_V1_PAYMENT_THETA_COLLISION_DEGREE: usize = POOL_V1_PAYMENT_THETA_LANES - 1;
pub const POOL_V1_PAYMENT_TAG73_MU_AGGREGATE_DEGREE: usize = 2;
pub const POOL_V1_PAYMENT_TAG73_MU_COLLISION_ROOT_BOUND: usize = 2;
pub const POOL_V1_PAYMENT_SEMANTIC_ORACLE_INDIVIDUAL_DEGREE: usize = 21;
pub const POOL_V1_PAYMENT_SEMANTIC_ZEROCHECK_INDIVIDUAL_DEGREE: usize = 22;
pub const POOL_V1_PAYMENT_MASKED_TERMINAL_DEGREE: usize = 27;
/// The runtime terminal performs one fixed-size selector allocation and no
/// registry-dependent or input-dependent allocation.
pub const POOL_V1_PAYMENT_TERMINAL_FIXED_HEAP_ALLOCATIONS: usize = 1;
pub const POOL_V1_PAYMENT_TERMINAL_SELECTOR_HEAP_BYTES: usize = 1_280;

pub const PINNED_POOL_V1_PRIVATE_TRANSFER_SEMANTIC_REGISTRY_FINGERPRINT_V1: u64 =
    constants::PRIVATE_TRANSFER_REGISTRY_FINGERPRINT;
pub const PINNED_POOL_V1_WITHDRAWAL_SEMANTIC_REGISTRY_FINGERPRINT_V1: u64 =
    constants::WITHDRAWAL_REGISTRY_FINGERPRINT;
pub const PINNED_POOL_V1_PAYMENT_AUXILIARY_LAYOUT_FINGERPRINT_V1: u64 =
    constants::AUXILIARY_USED_COLUMN_MASKS_FINGERPRINT;
pub const PINNED_POOL_V1_PRIVATE_TRANSFER_COPY_ACTIVE_ROWS_FINGERPRINT_V1: u64 =
    constants::PRIVATE_TRANSFER_ACTIVE_ROWS_FINGERPRINT;
pub const PINNED_POOL_V1_WITHDRAWAL_COPY_ACTIVE_ROWS_FINGERPRINT_V1: u64 =
    constants::WITHDRAWAL_ACTIVE_ROWS_FINGERPRINT;

const SELECTED_H1_COLUMN: usize =
    POOL_V1_PAYMENT_TERMINAL_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
const SELECTED_G_COLUMN: usize = SELECTED_H1_COLUMN + 1;
const AUXILIARY_ROW_START: usize = 784;
const COMPILED_AUXILIARY_ROW_END: usize = 880;
const VALUE_AUXILIARY_BLOCK: usize = 54;
const COPY_PATTERN_COUNT: usize = 13;

const _: () = assert!(DIGEST_ELEMS == 8);
const _: () = assert!(POSEIDON2_WIDTH == POOL_V1_PAYMENT_TERMINAL_C1_COLUMNS);
const _: () = assert!(POOL_V1_PAYMENT_SELECTED_TERMINAL_COLUMNS == 28);
const _: () = assert!(POOL_V1_PAYMENT_SELECTED_TERMINAL_CLAIMS == 84);
const _: () = assert!(POOL_V1_PAYMENT_THETA_LANES == 29);
const _: () = assert!(POOL_V1_PAYMENT_THETA_COLLISION_DEGREE == 28);
const _: () = assert!(constants::PRIVATE_TRANSFER_COPY_PATTERNS.len() == COPY_PATTERN_COUNT);
const _: () = assert!(constants::WITHDRAWAL_COPY_PATTERNS.len() == COPY_PATTERN_COUNT);
const _: () = assert!(constants::PRIVATE_TRANSFER_COPY_LINKS.len() == 78);
const _: () = assert!(constants::WITHDRAWAL_COPY_LINKS.len() == 75);
const _: () = assert!(constants::AUXILIARY_USED_COLUMN_MASKS.len() == 96);
const _: () =
    assert!(core::mem::size_of::<Selectors>() == POOL_V1_PAYMENT_TERMINAL_SELECTOR_HEAP_BYTES);

#[derive(Clone, Copy)]
struct CompiledPoolV1PaymentPattern {
    /// 0 = zero, 1 = constant, 2 = affine row-local C1 cell.
    kinds: [u8; POSEIDON2_WIDTH],
    columns: [u8; POSEIDON2_WIDTH],
    scales: [u32; POSEIDON2_WIDTH],
    offsets: [u32; POSEIDON2_WIDTH],
}

#[derive(Clone, Copy)]
struct CompiledPoolV1PaymentEndpoint {
    row: u16,
    slot: u8,
    pattern: u8,
}

#[derive(Clone, Copy)]
struct CompiledPoolV1PaymentLink {
    tag: u32,
    producer: CompiledPoolV1PaymentEndpoint,
    consumer: CompiledPoolV1PaymentEndpoint,
}

mod constants {
    use super::{
        CompiledPoolV1PaymentEndpoint, CompiledPoolV1PaymentLink, CompiledPoolV1PaymentPattern,
    };
    include!("payment_semantic_terminal_constants.rs");
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PaymentSemanticTerminalErrorV1 {
    InvalidPublicAmount,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CompiledVariant {
    PrivateTransfer,
    Withdrawal,
}

#[derive(Clone, Copy)]
struct SemanticPublic {
    variant: CompiledVariant,
    anchor: Digest,
    nullifier: Digest,
    asset_id: M31,
    recipient: Option<Digest>,
    change: Digest,
    withdrawal_amount: Option<u32>,
}

#[derive(Clone, Copy)]
struct CompiledRegistry {
    patterns: &'static [CompiledPoolV1PaymentPattern],
    links: &'static [CompiledPoolV1PaymentLink],
    active_row_masks: &'static [u16; 64],
}

fn compiled_registry(variant: CompiledVariant) -> CompiledRegistry {
    match variant {
        CompiledVariant::PrivateTransfer => CompiledRegistry {
            patterns: &constants::PRIVATE_TRANSFER_COPY_PATTERNS,
            links: &constants::PRIVATE_TRANSFER_COPY_LINKS,
            active_row_masks: &constants::PRIVATE_TRANSFER_ACTIVE_ROW_MASKS,
        },
        CompiledVariant::Withdrawal => CompiledRegistry {
            patterns: &constants::WITHDRAWAL_COPY_PATTERNS,
            links: &constants::WITHDRAWAL_COPY_LINKS,
            active_row_masks: &constants::WITHDRAWAL_ACTIVE_ROW_MASKS,
        },
    }
}

pub fn pool_v1_private_transfer_copy_active_row_masks_compiled_v1() -> &'static [u16; 64] {
    &constants::PRIVATE_TRANSFER_ACTIVE_ROW_MASKS
}

pub fn pool_v1_withdrawal_copy_active_row_masks_compiled_v1() -> &'static [u16; 64] {
    &constants::WITHDRAWAL_ACTIVE_ROW_MASKS
}

#[inline(always)]
fn lift(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}

#[inline(always)]
fn selector_mask_sum_16(values: &[QM31; 16], mut mask: u16) -> QM31 {
    let complement = mask.count_ones() > 8;
    if complement {
        mask = !mask;
    }
    let mut sum = if complement { QM31::ONE } else { QM31::ZERO };
    while mask != 0 {
        let index = mask.trailing_zeros() as usize;
        sum = if complement {
            sum.sub(values[index])
        } else {
            sum.add(values[index])
        };
        mask &= mask - 1;
    }
    sum
}

#[derive(Clone, Copy)]
struct Selectors {
    high: [QM31; 64],
    low: [QM31; 16],
}

impl Selectors {
    fn expand<const N: usize>(coordinates: &[QM31]) -> [QM31; N] {
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

    fn at_point(point: &[QM31; 10]) -> Self {
        Self {
            high: Self::expand(&point[..6]),
            low: Self::expand(&point[6..]),
        }
    }

    #[inline(never)]
    fn boxed_at_point(point: &[QM31; 10]) -> Box<Self> {
        Box::new(Self::at_point(point))
    }

    #[inline(always)]
    fn row(&self, row: usize) -> QM31 {
        debug_assert!(row < POOL_V1_PAYMENT_TERMINAL_ROWS);
        self.high[row >> 4].mul(self.low[row & 15])
    }

    fn poseidon(&self) -> StateOnlyPoseidonSelectors {
        StateOnlyPoseidonSelectors {
            block: self.high[..49].iter().copied().fold(QM31::ZERO, QM31::add),
            local: self.low,
        }
    }

    fn copy_active(&self, masks: &[u16; 64]) -> QM31 {
        masks
            .iter()
            .enumerate()
            .filter(|(_, mask)| **mask != 0)
            .fold(QM31::ZERO, |sum, (block, &mask)| {
                sum.add(self.high[block].mul(selector_mask_sum_16(&self.low, mask)))
            })
    }
}

pub fn pool_v1_private_transfer_copy_active_at_point_compiled_v1(point: &[QM31; 10]) -> QM31 {
    Selectors::at_point(point).copy_active(&constants::PRIVATE_TRANSFER_ACTIVE_ROW_MASKS)
}

pub fn pool_v1_withdrawal_copy_active_at_point_compiled_v1(point: &[QM31; 10]) -> QM31 {
    Selectors::at_point(point).copy_active(&constants::WITHDRAWAL_ACTIVE_ROW_MASKS)
}

fn pattern_values(
    openings: &[QM31; POSEIDON2_WIDTH],
    lambda: QM31,
    patterns: &[CompiledPoolV1PaymentPattern],
) -> [QM31; COPY_PATTERN_COUNT] {
    let mut powers = [QM31::ZERO; POSEIDON2_WIDTH];
    let mut power = lambda;
    for output in &mut powers {
        *output = power;
        power = power.mul(lambda);
    }
    core::array::from_fn(|pattern_index| {
        let pattern = patterns[pattern_index];
        let mut value = QM31::ZERO;
        for limb in 0..POSEIDON2_WIDTH {
            let source = match pattern.kinds[limb] {
                0 => continue,
                1 => lift(M31(pattern.offsets[limb])),
                2 => openings[usize::from(pattern.columns[limb])]
                    .mul_m31(M31(pattern.scales[limb]))
                    .add(lift(M31(pattern.offsets[limb]))),
                _ => unreachable!("generated Pool V1 tuple kind"),
            };
            value = value.add(powers[limb].mul(source));
        }
        value
    })
}

#[derive(Clone, Copy)]
struct CopyRowExtension {
    producer_values: [QM31; 2],
    producer_weights: [QM31; 2],
    consumer_values: [QM31; 2],
    consumer_weights: [QM31; 2],
}

fn copy_residual(row: CopyRowExtension, helper: QM31, chi: QM31) -> QM31 {
    let denominators = [
        chi.sub(row.producer_values[0]),
        chi.sub(row.producer_values[1]),
        chi.sub(row.consumer_values[0]),
        chi.sub(row.consumer_values[1]),
    ];
    let producer_denominator = denominators[0].mul(denominators[1]);
    let consumer_denominator = denominators[2].mul(denominators[3]);
    let producer_numerator = row.producer_weights[0]
        .mul(denominators[1])
        .add(row.producer_weights[1].mul(denominators[0]));
    let consumer_numerator = row.consumer_weights[0]
        .mul(denominators[3])
        .add(row.consumer_weights[1].mul(denominators[2]));
    producer_denominator
        .mul(helper.mul(consumer_denominator).add(consumer_numerator))
        .sub(consumer_denominator.mul(producer_numerator))
}

fn copy_lane(
    openings: &[QM31; POSEIDON2_WIDTH],
    h1_z: QM31,
    selectors: &Selectors,
    lambda: QM31,
    chi: QM31,
    registry: CompiledRegistry,
) -> (QM31, QM31) {
    let patterns = pattern_values(openings, lambda, registry.patterns);
    let mut row = CopyRowExtension {
        producer_values: [QM31::ZERO; 2],
        producer_weights: [QM31::ZERO; 2],
        consumer_values: [QM31::ZERO; 2],
        consumer_weights: [QM31::ZERO; 2],
    };
    for link in registry.links {
        for (endpoint, values, weights) in [
            (
                link.producer,
                &mut row.producer_values,
                &mut row.producer_weights,
            ),
            (
                link.consumer,
                &mut row.consumer_values,
                &mut row.consumer_weights,
            ),
        ] {
            let selector = selectors.row(usize::from(endpoint.row));
            let slot = usize::from(endpoint.slot);
            weights[slot] = weights[slot].add(selector);
            let compressed = lift(M31(link.tag)).add(patterns[usize::from(endpoint.pattern)]);
            values[slot] = values[slot].add(selector.mul(compressed));
        }
    }
    let active = selectors.copy_active(registry.active_row_masks);
    (active.mul(copy_residual(row, h1_z, chi)), active)
}

#[inline(always)]
fn add_preweighted<const N: usize>(
    packed: &mut [QM31; POOL_V1_PAYMENT_PACKED_SEMANTIC_LANES],
    start: usize,
    values: &[QM31; N],
) {
    let first = start / 4;
    let last = (start + N - 1) / 4;
    for group in first..=last {
        let lanes: [QM31; 4] = core::array::from_fn(|slot| {
            let source = 4 * group + slot;
            if source >= start && source < start + N {
                values[source - start]
            } else {
                QM31::ZERO
            }
        });
        packed[group] = packed[group].add(qm31_pack_base4(&lanes));
    }
}

fn first_sponge(block: usize, variant: CompiledVariant) -> Option<(M31, usize)> {
    match block {
        0 => Some((DOMAIN_OWNER_KEY, 8)),
        1 => Some((DOMAIN_NOTE, 18)),
        24 => Some((DOMAIN_NULLIFIER, 16)),
        26 if variant == CompiledVariant::PrivateTransfer => Some((DOMAIN_NOTE, 18)),
        29 => Some((DOMAIN_NOTE, 18)),
        _ => None,
    }
}

fn fixed_zero_block(block: usize, variant: CompiledVariant) -> bool {
    (32..49).contains(&block)
        || (variant == CompiledVariant::Withdrawal && (26..=28).contains(&block))
}

fn expected_initial_limb(block: usize, lane: usize, variant: CompiledVariant) -> Option<M31> {
    if let Some((domain, length)) = first_sponge(block, variant) {
        return Some(match lane {
            RATE => domain,
            lane if lane == RATE + 1 => M31(length as u32),
            _ => M31::ZERO,
        });
    }
    if (4..24).contains(&block) {
        return (lane < RATE).then_some(M31::ZERO);
    }
    fixed_zero_block(block, variant).then_some(M31::ZERO)
}

fn absorption_length(block: usize, variant: CompiledVariant) -> usize {
    match block {
        0 | 1 | 2 | 4..=25 | 26 | 27 | 29 | 30 => {
            if variant == CompiledVariant::Withdrawal && (26..=27).contains(&block) {
                0
            } else {
                8
            }
        }
        3 | 28 | 31 => {
            if variant == CompiledVariant::Withdrawal && block == 28 {
                0
            } else {
                2
            }
        }
        _ => 0,
    }
}

fn semantic_packed(
    public: SemanticPublic,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) -> [QM31; POOL_V1_PAYMENT_PACKED_SEMANTIC_LANES] {
    let mut packed = [QM31::ZERO; POOL_V1_PAYMENT_PACKED_SEMANTIC_LANES];

    let mut initial = [QM31::ZERO; 16];
    for block in 0..49 {
        let selector = selectors.row(block * 16);
        for lane in 0..POSEIDON2_WIDTH {
            if let Some(expected) = expected_initial_limb(block, lane, public.variant) {
                initial[lane] =
                    initial[lane].add(selector.mul(openings.z[lane].sub(lift(expected))));
            }
        }
    }
    let mut auxiliary_unused = [QM31::ZERO; 16];
    for (offset, &used_mask) in constants::AUXILIARY_USED_COLUMN_MASKS.iter().enumerate() {
        let selector = selectors.row(AUXILIARY_ROW_START + offset);
        for (lane, sum) in auxiliary_unused.iter_mut().enumerate() {
            if used_mask & (1 << lane) == 0 {
                *sum = sum.add(selector);
            }
        }
    }
    let completely_unused_tail = selectors.high[COMPILED_AUXILIARY_ROW_END >> 4..]
        .iter()
        .copied()
        .fold(QM31::ZERO, QM31::add);
    for lane in 0..16 {
        initial[lane] = initial[lane].add(
            auxiliary_unused[lane]
                .add(completely_unused_tail)
                .mul(openings.z[lane]),
        );
    }
    add_preweighted(&mut packed, 0, &initial);

    let mut absorption_zero = [QM31::ZERO; 16];
    for block in 0..49 {
        let selector = selectors.row(block * 16 + 12);
        for lane in absorption_length(block, public.variant)..16 {
            absorption_zero[lane] = absorption_zero[lane].add(selector.mul(openings.z[lane]));
        }
    }
    let permutation_blocks = selectors.high[..49]
        .iter()
        .copied()
        .fold(QM31::ZERO, QM31::add);
    let padding_selector = permutation_blocks.mul(
        selectors.low[13]
            .add(selectors.low[14])
            .add(selectors.low[15]),
    );
    for lane in 0..16 {
        absorption_zero[lane] = absorption_zero[lane].add(padding_selector.mul(openings.z[lane]));
    }
    add_preweighted(&mut packed, 16, &absorption_zero);

    let path_blocks = selectors.high[49..54]
        .iter()
        .copied()
        .fold(QM31::ZERO, QM31::add);
    let path_locals = selectors.low[0]
        .add(selectors.low[2])
        .add(selectors.low[4])
        .add(selectors.low[6]);
    let merkle_selector = path_blocks.mul(path_locals);
    let bit = openings.z[0];
    let mut merkle = [QM31::ZERO; 17];
    merkle[0] = merkle_selector.mul(bit.mul(bit.sub(QM31::ONE)));
    for lane in 0..DIGEST_ELEMS {
        let current = openings.z[1 + lane];
        let sibling = openings.xor12_z[lane];
        let delta = sibling.sub(current);
        merkle[1 + lane] =
            merkle_selector.mul(openings.succ_z[lane].sub(current.add(bit.mul(delta))));
        merkle[1 + DIGEST_ELEMS + lane] =
            merkle_selector.mul(openings.succ_z[RATE + lane].sub(sibling.sub(bit.mul(delta))));
    }
    add_preweighted(&mut packed, 32, &merkle);

    let value_selectors = [0usize, 2, 4].map(|local| selectors.row(54 * 16 + local));
    let range_selector = value_selectors.iter().copied().fold(QM31::ZERO, QM31::add);
    let views = [&openings.z, &openings.succ_z, &openings.xor12_z];
    let mut direct_range = [QM31::ZERO; 33];
    for (view, values) in views.into_iter().zip(direct_range[..30].chunks_mut(10)) {
        for bit_index in 0..10 {
            values[bit_index] =
                range_selector.mul(view[bit_index].mul(view[bit_index].sub(QM31::ONE)));
        }
    }
    let reconstructed_value = (0..10).fold(QM31::ZERO, |sum, bit_index| {
        sum.add(openings.z[bit_index].mul_m31(M31(1 << bit_index)))
            .add(openings.succ_z[bit_index].mul_m31(M31(1 << (10 + bit_index))))
            .add(openings.xor12_z[bit_index].mul_m31(M31(1 << (20 + bit_index))))
    });
    direct_range[30] = value_selectors
        .iter()
        .copied()
        .fold(QM31::ZERO, |sum, selector| {
            sum.add(selector.mul(openings.z[10].sub(reconstructed_value)))
        });
    direct_range[31] = range_selector.mul(openings.succ_z[10]);
    direct_range[32] = range_selector.mul(openings.xor12_z[10]);
    add_preweighted(&mut packed, 49, &direct_range);

    let conservation_selector = selectors.row(VALUE_AUXILIARY_BLOCK * 16 + 6);
    let value = [
        conservation_selector.mul(openings.z[0].sub(openings.z[1]).sub(openings.z[2])),
        conservation_selector.mul(openings.succ_z[0].sub(openings.succ_z[1])),
    ];
    add_preweighted(&mut packed, 82, &value);

    let mut public_digest = [QM31::ZERO; DIGEST_ELEMS];
    for (block, digest) in [
        (23usize, Some(public.anchor)),
        (25, Some(public.nullifier)),
        (28, public.recipient),
        (31, Some(public.change)),
    ] {
        let Some(digest) = digest else { continue };
        let selector = selectors.row(block * 16 + 11);
        for lane in 0..DIGEST_ELEMS {
            public_digest[lane] =
                public_digest[lane].add(selector.mul(openings.z[lane].sub(lift(digest[lane]))));
        }
    }
    add_preweighted(&mut packed, 84, &public_digest);

    let input_asset_selector = selectors.row(2 * 16 + 12);
    let mut output_scalar = selectors
        .row(30 * 16 + 12)
        .mul(openings.z[1].sub(lift(public.asset_id)));
    if public.variant == CompiledVariant::PrivateTransfer {
        output_scalar = output_scalar.add(
            selectors
                .row(27 * 16 + 12)
                .mul(openings.z[1].sub(lift(public.asset_id))),
        );
    } else if let Some(amount) = public.withdrawal_amount {
        output_scalar =
            output_scalar.add(value_selectors[1].mul(openings.z[10].sub(lift(M31(amount)))));
    }
    let public_scalar = [
        input_asset_selector.mul(openings.z[1].sub(lift(public.asset_id))),
        output_scalar,
    ];
    add_preweighted(&mut packed, 92, &public_scalar);

    packed
}

fn selected_claim(
    claims: &[QM31; POOL_V1_PAYMENT_SELECTED_TERMINAL_CLAIMS],
    point: usize,
    column: usize,
) -> QM31 {
    claims[point * POOL_V1_PAYMENT_SELECTED_TERMINAL_COLUMNS + column]
}

fn equality_value(left: &[QM31; 10], right: &[QM31; 10]) -> QM31 {
    let factor = |a: QM31, b: QM31| {
        let ab = a.mul(b);
        QM31::ONE.sub(a).sub(b).add(ab).add(ab)
    };
    left[1..]
        .iter()
        .zip(&right[1..])
        .fold(factor(left[0], right[0]), |product, (&a, &b)| {
            product.mul(factor(a, b))
        })
}

#[allow(clippy::type_complexity)]
fn composition_parts(
    public: SemanticPublic,
    claims: &[QM31; POOL_V1_PAYMENT_SELECTED_TERMINAL_CLAIMS],
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
) -> Result<
    (
        QM31,
        [QM31; 16],
        [QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
        QM31,
        QM31,
        QM31,
    ),
    PoolV1PaymentSemanticTerminalErrorV1,
> {
    if public
        .withdrawal_amount
        .is_some_and(|amount| amount == 0 || amount >= (1 << 30))
    {
        return Err(PoolV1PaymentSemanticTerminalErrorV1::InvalidPublicAmount);
    }
    let openings = StateOnlyPoseidonOpenings {
        z: core::array::from_fn(|column| selected_claim(claims, 0, column)),
        succ_z: core::array::from_fn(|column| selected_claim(claims, 1, column)),
        xor12_z: core::array::from_fn(|column| selected_claim(claims, 2, column)),
    };
    let mask_only = core::array::from_fn(|column| {
        selected_claim(claims, 0, POOL_V1_PAYMENT_TERMINAL_C1_COLUMNS + column)
    });
    let selectors = Selectors::boxed_at_point(point);
    let poseidon = evaluate_state_only_poseidon_oracle_projected(&openings, &selectors.poseidon());
    let semantic = semantic_packed(public, &openings, selectors.as_ref());
    let h1_z = selected_claim(claims, 0, SELECTED_H1_COLUMN);
    let (copy, copy_active) = copy_lane(
        &openings.z,
        h1_z,
        selectors.as_ref(),
        lambda,
        chi,
        compiled_registry(public.variant),
    );
    let prepared_theta = PreparedQm31Multiplier::new(theta);
    let mut composition = copy;
    for lane in semantic.into_iter().rev() {
        composition = prepared_theta.mul(composition).add(lane);
    }
    for lane in poseidon.into_iter().rev() {
        composition = prepared_theta.mul(composition).add(lane);
    }
    Ok((
        composition,
        openings.z,
        mask_only,
        selected_claim(claims, 0, SELECTED_G_COLUMN),
        h1_z,
        copy_active,
    ))
}

fn terminal_parts(
    public: SemanticPublic,
    claims: &[QM31; POOL_V1_PAYMENT_SELECTED_TERMINAL_CLAIMS],
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
    zerocheck_point: &[QM31; 10],
    mu: QM31,
) -> Result<
    (
        QM31,
        [QM31; 16],
        [QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
        QM31,
    ),
    PoolV1PaymentSemanticTerminalErrorV1,
> {
    let (composition, c1, mask_only, g, h1_z, copy_active) =
        composition_parts(public, claims, point, lambda, chi, theta)?;
    let original = equality_value(zerocheck_point, point)
        .mul(composition)
        .add(mu.mul(h1_z))
        .add(mu.mul(mu).mul(QM31::ONE.sub(copy_active).mul(h1_z)));
    Ok((original, c1, mask_only, g))
}

fn private_public(public: &PoolV1PrivateTransferPublicV1) -> SemanticPublic {
    SemanticPublic {
        variant: CompiledVariant::PrivateTransfer,
        anchor: public.anchor_root,
        nullifier: public.nullifier,
        asset_id: public.asset_id,
        recipient: Some(public.recipient_commitment),
        change: public.change_commitment,
        withdrawal_amount: None,
    }
}

fn withdrawal_public(public: &PoolV1WithdrawalPublicV1) -> SemanticPublic {
    SemanticPublic {
        variant: CompiledVariant::Withdrawal,
        anchor: public.anchor_root,
        nullifier: public.nullifier,
        asset_id: public.asset_id,
        recipient: None,
        change: public.change_commitment,
        withdrawal_amount: Some(public.amount),
    }
}

macro_rules! define_variant_terminal {
    ($composition:ident, $unmasked:ident, $masked:ident, $public_ty:ty, $convert:ident) => {
        #[allow(clippy::too_many_arguments)]
        pub fn $composition(
            public: &$public_ty,
            claims: &[QM31; POOL_V1_PAYMENT_SELECTED_TERMINAL_CLAIMS],
            point: &[QM31; 10],
            lambda: QM31,
            chi: QM31,
            theta: QM31,
        ) -> Result<QM31, PoolV1PaymentSemanticTerminalErrorV1> {
            Ok(composition_parts($convert(public), claims, point, lambda, chi, theta)?.0)
        }

        #[allow(clippy::too_many_arguments)]
        pub fn $unmasked(
            public: &$public_ty,
            claims: &[QM31; POOL_V1_PAYMENT_SELECTED_TERMINAL_CLAIMS],
            point: &[QM31; 10],
            lambda: QM31,
            chi: QM31,
            theta: QM31,
            zerocheck_point: &[QM31; 10],
            mu: QM31,
        ) -> Result<QM31, PoolV1PaymentSemanticTerminalErrorV1> {
            Ok(terminal_parts(
                $convert(public),
                claims,
                point,
                lambda,
                chi,
                theta,
                zerocheck_point,
                mu,
            )?
            .0)
        }

        #[allow(clippy::too_many_arguments)]
        #[inline(never)]
        pub fn $masked(
            public: &$public_ty,
            claims: &[QM31; POOL_V1_PAYMENT_SELECTED_TERMINAL_CLAIMS],
            point: &[QM31; 10],
            lambda: QM31,
            chi: QM31,
            theta: QM31,
            zerocheck_point: &[QM31; 10],
            mu: QM31,
            eta: QM31,
        ) -> Result<QM31, PoolV1PaymentSemanticTerminalErrorV1> {
            let (original, c1, mask_only, g) = terminal_parts(
                $convert(public),
                claims,
                point,
                lambda,
                chi,
                theta,
                zerocheck_point,
                mu,
            )?;
            Ok(state_only_selected_mask_value(&c1, &mask_only, g, point).add(eta.mul(original)))
        }
    };
}

define_variant_terminal!(
    evaluate_pool_v1_private_transfer_selected_constraint_composition_compiled_v1,
    evaluate_pool_v1_private_transfer_selected_unmasked_terminal_compiled_tag73_v1,
    evaluate_pool_v1_private_transfer_selected_masked_terminal_compiled_tag73_v1,
    PoolV1PrivateTransferPublicV1,
    private_public
);

define_variant_terminal!(
    evaluate_pool_v1_withdrawal_selected_constraint_composition_compiled_v1,
    evaluate_pool_v1_withdrawal_selected_unmasked_terminal_compiled_tag73_v1,
    evaluate_pool_v1_withdrawal_selected_masked_terminal_compiled_tag73_v1,
    PoolV1WithdrawalPublicV1,
    withdrawal_public
);

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;
    use aspis_core::field::P;
    use aspis_core::state_only_hiding::state_only_selected_mask_value;

    use crate::{
        derive_owner_key,
        pool_v1::{
            build_pool_v1_private_transfer_trace_v1, build_pool_v1_withdrawal_trace_v1,
            payment_semantic_oracle::{
                build_pool_v1_payment_copy_helper_v1,
                evaluate_pool_v1_private_transfer_semantic_oracle_v1,
                evaluate_pool_v1_withdrawal_semantic_oracle_v1,
                pool_v1_payment_copy_active_at_point_v1,
                pool_v1_payment_semantic_openings_at_point_v1,
                prepare_pool_v1_payment_semantic_oracle_v1, PoolV1PaymentSemanticOpeningsV1,
                PoolV1PaymentSemanticPreparedV1, PoolV1PaymentSemanticResidualsV1,
            },
            payment_semantic_registry::{
                build_pool_v1_payment_semantic_registry_v1, pool_v1_payment_aux_cell_is_used_v1,
                pool_v1_payment_semantic_registry_fingerprint_v1, PoolV1PaymentCopyTupleV1,
                PoolV1PaymentTupleLimbV1,
            },
            pool_v1_membership_root_v1, pool_v1_note_commitment, pool_v1_nullifier,
            PoolV1InputNoteWitnessV1, PoolV1MembershipWitnessV1, PoolV1OutputNoteWitnessV1,
            PoolV1PaymentRelationContextV1, PoolV1PaymentRuntimeBindingV1,
            PoolV1PaymentTraceVariantV1, PoolV1PrivateTransferWitnessV1, PoolV1WithdrawalWitnessV1,
        },
        state_only_poseidon::{
            evaluate_state_only_poseidon_oracle_projected, StateOnlyPoseidonSelectors,
        },
    };

    #[derive(Clone, Copy)]
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0 = self.0.wrapping_mul(0x2545_f491_4f6c_dd1d);
            self.0
        }

        fn m31(&mut self) -> M31 {
            M31((self.next() % u64::from(P)) as u32)
        }

        fn qm31(&mut self) -> QM31 {
            QM31 {
                c0: CM31::new(self.m31(), self.m31()),
                c1: CM31::new(self.m31(), self.m31()),
            }
        }
    }

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

    fn challenges() -> (QM31, QM31, QM31, QM31, QM31) {
        let mut rng = Rng(0x5441_4737_335f_504f);
        (rng.qm31(), rng.qm31(), rng.qm31(), rng.qm31(), rng.qm31())
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

    fn claims_from_openings(
        openings: &PoolV1PaymentSemanticOpeningsV1,
    ) -> [QM31; POOL_V1_PAYMENT_SELECTED_TERMINAL_CLAIMS] {
        let mut claims = [QM31::ZERO; POOL_V1_PAYMENT_SELECTED_TERMINAL_CLAIMS];
        for (point, view) in [&openings.c1.z, &openings.c1.succ_z, &openings.c1.xor12_z]
            .into_iter()
            .enumerate()
        {
            for (column, value) in view.iter().copied().enumerate() {
                claims[point * POOL_V1_PAYMENT_SELECTED_TERMINAL_COLUMNS + column] = value;
            }
        }
        claims[SELECTED_H1_COLUMN] = openings.h1_z;
        claims
    }

    fn host_pattern(tuple: PoolV1PaymentCopyTupleV1) -> CompiledPoolV1PaymentPattern {
        let mut pattern = CompiledPoolV1PaymentPattern {
            kinds: [0; 16],
            columns: [0; 16],
            scales: [0; 16],
            offsets: [0; 16],
        };
        for (index, limb) in tuple.limbs.into_iter().enumerate() {
            match limb {
                PoolV1PaymentTupleLimbV1::Zero => {}
                PoolV1PaymentTupleLimbV1::Constant(value) => {
                    pattern.kinds[index] = 1;
                    pattern.offsets[index] = value.0;
                }
                PoolV1PaymentTupleLimbV1::AffineCell {
                    cell,
                    scale,
                    offset,
                } => {
                    assert_eq!(cell.row, tuple.row);
                    pattern.kinds[index] = 2;
                    pattern.columns[index] = cell.column;
                    pattern.scales[index] = scale.0;
                    pattern.offsets[index] = offset.0;
                }
            }
        }
        pattern
    }

    fn assert_registry_identity(variant: PoolV1PaymentTraceVariantV1) {
        let registry = build_pool_v1_payment_semantic_registry_v1(variant).unwrap();
        let compiled_variant = match variant {
            PoolV1PaymentTraceVariantV1::PrivateTransfer => CompiledVariant::PrivateTransfer,
            PoolV1PaymentTraceVariantV1::Withdrawal => CompiledVariant::Withdrawal,
        };
        let compiled = compiled_registry(compiled_variant);
        let expected_fingerprint = match compiled_variant {
            CompiledVariant::PrivateTransfer => {
                PINNED_POOL_V1_PRIVATE_TRANSFER_SEMANTIC_REGISTRY_FINGERPRINT_V1
            }
            CompiledVariant::Withdrawal => {
                PINNED_POOL_V1_WITHDRAWAL_SEMANTIC_REGISTRY_FINGERPRINT_V1
            }
        };
        assert_eq!(
            pool_v1_payment_semantic_registry_fingerprint_v1(&registry).unwrap(),
            expected_fingerprint
        );

        let mut host_patterns = Vec::<CompiledPoolV1PaymentPattern>::new();
        for link in &registry.links {
            for tuple in [link.producer, link.consumer] {
                let candidate = host_pattern(tuple);
                if !host_patterns.iter().any(|pattern| {
                    pattern.kinds == candidate.kinds
                        && pattern.columns == candidate.columns
                        && pattern.scales == candidate.scales
                        && pattern.offsets == candidate.offsets
                }) {
                    host_patterns.push(candidate);
                }
            }
        }
        assert_eq!(host_patterns.len(), compiled.patterns.len());
        for (host, compiled) in host_patterns.iter().zip(compiled.patterns) {
            assert_eq!(host.kinds, compiled.kinds);
            assert_eq!(host.columns, compiled.columns);
            assert_eq!(host.scales, compiled.scales);
            assert_eq!(host.offsets, compiled.offsets);
        }

        let mut producer_arity = [0u8; 1024];
        let mut consumer_arity = [0u8; 1024];
        let mut active_masks = [0u16; 64];
        assert_eq!(registry.links.len(), compiled.links.len());
        for (host, compiled_link) in registry.links.iter().zip(compiled.links) {
            assert_eq!(host.tag.0, compiled_link.tag);
            for (tuple, arity, endpoint) in [
                (host.producer, &mut producer_arity, compiled_link.producer),
                (host.consumer, &mut consumer_arity, compiled_link.consumer),
            ] {
                let row = usize::from(tuple.row);
                active_masks[row >> 4] |= 1 << (row & 15);
                assert_eq!(endpoint.row, tuple.row);
                assert_eq!(endpoint.slot, arity[row]);
                arity[row] += 1;
                let expected_pattern = host_pattern(tuple);
                let expected_pattern = host_patterns
                    .iter()
                    .position(|candidate| {
                        candidate.kinds == expected_pattern.kinds
                            && candidate.columns == expected_pattern.columns
                            && candidate.scales == expected_pattern.scales
                            && candidate.offsets == expected_pattern.offsets
                    })
                    .unwrap();
                assert_eq!(usize::from(endpoint.pattern), expected_pattern);
            }
        }
        assert_eq!(&active_masks, compiled.active_row_masks);
        let mut active_fingerprint = 0xcbf2_9ce4_8422_2325u64;
        for row in 0..1024u16 {
            if active_masks[usize::from(row) >> 4] & (1 << (usize::from(row) & 15)) != 0 {
                for byte in row.to_le_bytes() {
                    active_fingerprint ^= u64::from(byte);
                    active_fingerprint = active_fingerprint.wrapping_mul(0x0000_0100_0000_01b3);
                }
            }
        }
        assert_eq!(
            active_fingerprint,
            match compiled_variant {
                CompiledVariant::PrivateTransfer => {
                    PINNED_POOL_V1_PRIVATE_TRANSFER_COPY_ACTIVE_ROWS_FINGERPRINT_V1
                }
                CompiledVariant::Withdrawal => {
                    PINNED_POOL_V1_WITHDRAWAL_COPY_ACTIVE_ROWS_FINGERPRINT_V1
                }
            }
        );
    }

    #[test]
    fn compiled_constants_equal_host_registries_endpoints_and_auxiliary_layout() {
        assert_registry_identity(PoolV1PaymentTraceVariantV1::PrivateTransfer);
        assert_registry_identity(PoolV1PaymentTraceVariantV1::Withdrawal);
        let mut fingerprint = 0xcbf2_9ce4_8422_2325u64;
        for offset in 0..96 {
            let row = AUXILIARY_ROW_START + offset;
            let host_mask = (0..16).fold(0u16, |mask, column| {
                if pool_v1_payment_aux_cell_is_used_v1(row, column) {
                    mask | (1 << column)
                } else {
                    mask
                }
            });
            assert_eq!(constants::AUXILIARY_USED_COLUMN_MASKS[offset], host_mask);
            for byte in host_mask.to_le_bytes() {
                fingerprint ^= u64::from(byte);
                fingerprint = fingerprint.wrapping_mul(0x0000_0100_0000_01b3);
            }
        }
        assert_eq!(
            fingerprint,
            PINNED_POOL_V1_PAYMENT_AUXILIARY_LAYOUT_FINGERPRINT_V1
        );
        for row in COMPILED_AUXILIARY_ROW_END..POOL_V1_PAYMENT_TERMINAL_ROWS {
            for column in 0..16 {
                assert!(!pool_v1_payment_aux_cell_is_used_v1(row, column));
            }
        }
    }

    fn add_zero_sum_inactive_padding(h1: &mut [QM31], masks: &[u16; 64], value: QM31) {
        let inactive = (0..1024)
            .filter(|row| masks[row >> 4] & (1 << (row & 15)) == 0)
            .take(2)
            .collect::<Vec<_>>();
        assert_eq!(inactive.len(), 2);
        h1[inactive[0]] = h1[inactive[0]].add(value);
        h1[inactive[1]] = h1[inactive[1]].sub(value);
    }

    #[test]
    fn honest_boolean_tag73_terminal_sums_zero_with_random_inactive_h1_for_both_variants() {
        let (lambda, chi, theta, mu, _) = challenges();
        let zerocheck_point = core::array::from_fn(|index| lift(M31(20_000 + index as u32)));
        let random_padding = lift(M31(987_654));

        let (public, witness, context) = transfer_fixture();
        let trace = build_pool_v1_private_transfer_trace_v1(&public, &witness, context).unwrap();
        let prepared = prepare_pool_v1_payment_semantic_oracle_v1(
            PoolV1PaymentTraceVariantV1::PrivateTransfer,
        )
        .unwrap();
        let mut h1 =
            build_pool_v1_payment_copy_helper_v1(&prepared, &trace.trace, lambda, chi).unwrap();
        add_zero_sum_inactive_padding(
            &mut h1,
            &constants::PRIVATE_TRANSFER_ACTIVE_ROW_MASKS,
            random_padding,
        );
        let mut terminal_sum = QM31::ZERO;
        for row in 0..1024 {
            let point = boolean_point(row);
            let openings =
                pool_v1_payment_semantic_openings_at_point_v1(&trace.trace, &h1, &point).unwrap();
            let claims = claims_from_openings(&openings);
            terminal_sum = terminal_sum.add(
                evaluate_pool_v1_private_transfer_selected_unmasked_terminal_compiled_tag73_v1(
                    &public,
                    &claims,
                    &point,
                    lambda,
                    chi,
                    theta,
                    &zerocheck_point,
                    mu,
                )
                .unwrap(),
            );
        }
        assert_eq!(terminal_sum, QM31::ZERO);

        let (public, witness, context) = withdrawal_fixture();
        let trace = build_pool_v1_withdrawal_trace_v1(&public, &witness, context).unwrap();
        let prepared =
            prepare_pool_v1_payment_semantic_oracle_v1(PoolV1PaymentTraceVariantV1::Withdrawal)
                .unwrap();
        let mut h1 =
            build_pool_v1_payment_copy_helper_v1(&prepared, &trace.trace, lambda, chi).unwrap();
        add_zero_sum_inactive_padding(
            &mut h1,
            &constants::WITHDRAWAL_ACTIVE_ROW_MASKS,
            random_padding,
        );
        let mut terminal_sum = QM31::ZERO;
        for row in 0..1024 {
            let point = boolean_point(row);
            let openings =
                pool_v1_payment_semantic_openings_at_point_v1(&trace.trace, &h1, &point).unwrap();
            let claims = claims_from_openings(&openings);
            terminal_sum = terminal_sum.add(
                evaluate_pool_v1_withdrawal_selected_unmasked_terminal_compiled_tag73_v1(
                    &public,
                    &claims,
                    &point,
                    lambda,
                    chi,
                    theta,
                    &zerocheck_point,
                    mu,
                )
                .unwrap(),
            );
        }
        assert_eq!(terminal_sum, QM31::ZERO);
    }

    fn openings_from_claims(
        claims: &[QM31; POOL_V1_PAYMENT_SELECTED_TERMINAL_CLAIMS],
    ) -> PoolV1PaymentSemanticOpeningsV1 {
        PoolV1PaymentSemanticOpeningsV1 {
            c1: StateOnlyPoseidonOpenings {
                z: core::array::from_fn(|column| selected_claim(claims, 0, column)),
                succ_z: core::array::from_fn(|column| selected_claim(claims, 1, column)),
                xor12_z: core::array::from_fn(|column| selected_claim(claims, 2, column)),
            },
            h1_z: selected_claim(claims, 0, SELECTED_H1_COLUMN),
        }
    }

    fn reference_composition(
        residuals: &PoolV1PaymentSemanticResidualsV1,
        openings: &PoolV1PaymentSemanticOpeningsV1,
        point: &[QM31; 10],
        theta: QM31,
    ) -> QM31 {
        let poseidon = evaluate_state_only_poseidon_oracle_projected(
            &openings.c1,
            &StateOnlyPoseidonSelectors::at_point(point),
        );
        let semantic = residuals.packed_base_lanes();
        let mut composition = residuals.copy;
        for lane in semantic.into_iter().rev() {
            composition = theta.mul(composition).add(lane);
        }
        for lane in poseidon.into_iter().rev() {
            composition = theta.mul(composition).add(lane);
        }
        composition
    }

    #[allow(clippy::too_many_arguments)]
    fn assert_random_identity_private(
        public: &PoolV1PrivateTransferPublicV1,
        prepared: &PoolV1PaymentSemanticPreparedV1,
        claims: &[QM31; POOL_V1_PAYMENT_SELECTED_TERMINAL_CLAIMS],
        point: &[QM31; 10],
        lambda: QM31,
        chi: QM31,
        theta: QM31,
        zerocheck_point: &[QM31; 10],
        mu: QM31,
        eta: QM31,
    ) {
        let openings = openings_from_claims(claims);
        let residuals = evaluate_pool_v1_private_transfer_semantic_oracle_v1(
            public, &openings, point, lambda, chi, prepared,
        )
        .unwrap();
        let selectors = Selectors::at_point(point);
        assert_eq!(
            semantic_packed(private_public(public), &openings.c1, &selectors),
            residuals.packed_base_lanes(),
            "private semantic packing"
        );
        assert_eq!(
            copy_lane(
                &openings.c1.z,
                openings.h1_z,
                &selectors,
                lambda,
                chi,
                compiled_registry(CompiledVariant::PrivateTransfer),
            )
            .0,
            residuals.copy,
            "private compiled copy"
        );
        let composition = reference_composition(&residuals, &openings, point, theta);
        assert_eq!(
            evaluate_pool_v1_private_transfer_selected_constraint_composition_compiled_v1(
                public, claims, point, lambda, chi, theta,
            )
            .unwrap(),
            composition
        );
        let reference_unmasked = equality_value(zerocheck_point, point)
            .mul(composition)
            .add(mu.mul(openings.h1_z))
            .add(
                mu.mul(mu).mul(
                    QM31::ONE
                        .sub(pool_v1_payment_copy_active_at_point_v1(prepared, point))
                        .mul(openings.h1_z),
                ),
            );
        let compiled_unmasked =
            evaluate_pool_v1_private_transfer_selected_unmasked_terminal_compiled_tag73_v1(
                public,
                claims,
                point,
                lambda,
                chi,
                theta,
                zerocheck_point,
                mu,
            )
            .unwrap();
        assert_eq!(compiled_unmasked, reference_unmasked);
        let c1 = core::array::from_fn(|column| selected_claim(claims, 0, column));
        let mask_only = core::array::from_fn(|column| selected_claim(claims, 0, 16 + column));
        let mask = state_only_selected_mask_value(
            &c1,
            &mask_only,
            selected_claim(claims, 0, SELECTED_G_COLUMN),
            point,
        );
        assert_eq!(
            evaluate_pool_v1_private_transfer_selected_masked_terminal_compiled_tag73_v1(
                public,
                claims,
                point,
                lambda,
                chi,
                theta,
                zerocheck_point,
                mu,
                eta,
            )
            .unwrap(),
            mask.add(eta.mul(compiled_unmasked))
        );
    }

    #[allow(clippy::too_many_arguments)]
    fn assert_random_identity_withdrawal(
        public: &PoolV1WithdrawalPublicV1,
        prepared: &PoolV1PaymentSemanticPreparedV1,
        claims: &[QM31; POOL_V1_PAYMENT_SELECTED_TERMINAL_CLAIMS],
        point: &[QM31; 10],
        lambda: QM31,
        chi: QM31,
        theta: QM31,
        zerocheck_point: &[QM31; 10],
        mu: QM31,
        eta: QM31,
    ) {
        let openings = openings_from_claims(claims);
        let residuals = evaluate_pool_v1_withdrawal_semantic_oracle_v1(
            public, &openings, point, lambda, chi, prepared,
        )
        .unwrap();
        let selectors = Selectors::at_point(point);
        assert_eq!(
            semantic_packed(withdrawal_public(public), &openings.c1, &selectors),
            residuals.packed_base_lanes(),
            "withdrawal semantic packing"
        );
        assert_eq!(
            copy_lane(
                &openings.c1.z,
                openings.h1_z,
                &selectors,
                lambda,
                chi,
                compiled_registry(CompiledVariant::Withdrawal),
            )
            .0,
            residuals.copy,
            "withdrawal compiled copy"
        );
        let composition = reference_composition(&residuals, &openings, point, theta);
        assert_eq!(
            evaluate_pool_v1_withdrawal_selected_constraint_composition_compiled_v1(
                public, claims, point, lambda, chi, theta,
            )
            .unwrap(),
            composition
        );
        let reference_unmasked = equality_value(zerocheck_point, point)
            .mul(composition)
            .add(mu.mul(openings.h1_z))
            .add(
                mu.mul(mu).mul(
                    QM31::ONE
                        .sub(pool_v1_payment_copy_active_at_point_v1(prepared, point))
                        .mul(openings.h1_z),
                ),
            );
        let compiled_unmasked =
            evaluate_pool_v1_withdrawal_selected_unmasked_terminal_compiled_tag73_v1(
                public,
                claims,
                point,
                lambda,
                chi,
                theta,
                zerocheck_point,
                mu,
            )
            .unwrap();
        assert_eq!(compiled_unmasked, reference_unmasked);
        let c1 = core::array::from_fn(|column| selected_claim(claims, 0, column));
        let mask_only = core::array::from_fn(|column| selected_claim(claims, 0, 16 + column));
        let mask = state_only_selected_mask_value(
            &c1,
            &mask_only,
            selected_claim(claims, 0, SELECTED_G_COLUMN),
            point,
        );
        assert_eq!(
            evaluate_pool_v1_withdrawal_selected_masked_terminal_compiled_tag73_v1(
                public,
                claims,
                point,
                lambda,
                chi,
                theta,
                zerocheck_point,
                mu,
                eta,
            )
            .unwrap(),
            mask.add(eta.mul(compiled_unmasked))
        );
    }

    #[test]
    fn randomized_off_domain_compiled_terminal_matches_host_reference_and_mask_identity() {
        let (transfer, _, _) = transfer_fixture();
        let transfer_prepared = prepare_pool_v1_payment_semantic_oracle_v1(
            PoolV1PaymentTraceVariantV1::PrivateTransfer,
        )
        .unwrap();
        let (withdrawal, _, _) = withdrawal_fixture();
        let withdrawal_prepared =
            prepare_pool_v1_payment_semantic_oracle_v1(PoolV1PaymentTraceVariantV1::Withdrawal)
                .unwrap();
        let mut rng = Rng(0x4f46_4644_4f4d_4149);
        for _ in 0..12 {
            let claims = core::array::from_fn(|_| rng.qm31());
            let point = core::array::from_fn(|_| rng.qm31());
            let zerocheck_point = core::array::from_fn(|_| rng.qm31());
            let (lambda, chi, theta, mu, eta) =
                (rng.qm31(), rng.qm31(), rng.qm31(), rng.qm31(), rng.qm31());
            assert_random_identity_private(
                &transfer,
                &transfer_prepared,
                &claims,
                &point,
                lambda,
                chi,
                theta,
                &zerocheck_point,
                mu,
                eta,
            );
            assert_random_identity_withdrawal(
                &withdrawal,
                &withdrawal_prepared,
                &claims,
                &point,
                lambda,
                chi,
                theta,
                &zerocheck_point,
                mu,
                eta,
            );
        }
    }

    #[test]
    fn active_mismatch_and_inactive_helper_cancel_only_at_two_mu_roots() {
        assert_eq!(POOL_V1_PAYMENT_TAG73_MU_AGGREGATE_DEGREE, 2);
        assert_eq!(POOL_V1_PAYMENT_TAG73_MU_COLLISION_ROOT_BOUND, 2);
        let (lambda, chi, theta, _, _) = challenges();
        let (public, witness, context) = transfer_fixture();
        let trace = build_pool_v1_private_transfer_trace_v1(&public, &witness, context).unwrap();
        let prepared = prepare_pool_v1_payment_semantic_oracle_v1(
            PoolV1PaymentTraceVariantV1::PrivateTransfer,
        )
        .unwrap();
        let mut h1 =
            build_pool_v1_payment_copy_helper_v1(&prepared, &trace.trace, lambda, chi).unwrap();
        let active_row = (0..1024)
            .find(|row| {
                constants::PRIVATE_TRANSFER_ACTIVE_ROW_MASKS[row >> 4] & (1 << (row & 15)) != 0
            })
            .unwrap();
        h1[active_row] = h1[active_row].add(QM31::ONE);
        let point = boolean_point(active_row);
        let openings =
            pool_v1_payment_semantic_openings_at_point_v1(&trace.trace, &h1, &point).unwrap();
        let claims = claims_from_openings(&openings);
        let active_mismatch =
            evaluate_pool_v1_private_transfer_selected_constraint_composition_compiled_v1(
                &public, &claims, &point, lambda, chi, theta,
            )
            .unwrap();
        assert_ne!(active_mismatch, QM31::ZERO);

        let total_helper = QM31::ZERO;
        let inactive_helper = QM31::ZERO.sub(active_mismatch);
        let aggregate = |mu: QM31| {
            active_mismatch
                .add(mu.mul(total_helper))
                .add(mu.mul(mu).mul(inactive_helper))
        };
        assert_eq!(aggregate(QM31::ONE), QM31::ZERO);
        assert_eq!(aggregate(QM31::ZERO.sub(QM31::ONE)), QM31::ZERO);
        let roots = (0..4096u32)
            .filter(|&candidate| aggregate(lift(M31(candidate))) == QM31::ZERO)
            .count();
        assert_eq!(roots, 1, "the sampled subfield contains +1 but not P-1");
        for candidate in [M31(0), M31(2), M31(17), M31(P - 2)] {
            assert_ne!(aggregate(lift(candidate)), QM31::ZERO);
        }
    }

    #[test]
    fn withdrawal_amount_errors_are_identical_across_terminal_apis() {
        let (mut public, _, _) = withdrawal_fixture();
        let claims = [QM31::ZERO; POOL_V1_PAYMENT_SELECTED_TERMINAL_CLAIMS];
        let point = [QM31::ZERO; 10];
        let error = PoolV1PaymentSemanticTerminalErrorV1::InvalidPublicAmount;
        for invalid in [0, 1 << 30, u32::MAX] {
            public.amount = invalid;
            assert_eq!(
                evaluate_pool_v1_withdrawal_selected_constraint_composition_compiled_v1(
                    &public,
                    &claims,
                    &point,
                    QM31::ONE,
                    QM31::ONE,
                    QM31::ONE,
                ),
                Err(error)
            );
            assert_eq!(
                evaluate_pool_v1_withdrawal_selected_unmasked_terminal_compiled_tag73_v1(
                    &public,
                    &claims,
                    &point,
                    QM31::ONE,
                    QM31::ONE,
                    QM31::ONE,
                    &point,
                    QM31::ONE,
                ),
                Err(error)
            );
            assert_eq!(
                evaluate_pool_v1_withdrawal_selected_masked_terminal_compiled_tag73_v1(
                    &public,
                    &claims,
                    &point,
                    QM31::ONE,
                    QM31::ONE,
                    QM31::ONE,
                    &point,
                    QM31::ONE,
                    QM31::ONE,
                ),
                Err(error)
            );
        }
    }
}
