//! Generated terminal/routing evaluator for the atomic state-only v3 copy lane.
//!
//! This module is deliberately separate from the live state-only verifier.
//! It consumes only checked-in constants at runtime; host registry builders
//! are used exclusively by the identity tests.

use alloc::{boxed::Box, vec, vec::Vec};

use aspis_core::field::{
    qm31_dot, qm31_m31_dot, qm31_pack_base4, PreparedQm31Multiplier, CM31, M31, P, QM31,
};
use aspis_core::state_only_hiding::{
    state_only_selected_mask_value, STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS,
};

use crate::atomic_statement::AtomicPaymentStatementV4;
use crate::poseidon2::DIGEST_ELEMS;
use crate::spend::VALUE_LIMIT;
use crate::state_only_poseidon::{
    evaluate_state_only_poseidon_oracle_projected, StateOnlyPoseidonOpenings,
    StateOnlyPoseidonSelectors,
};
use crate::state_only_terminal::{
    constants as state_constants, StateOnlyTerminalDiagnosticPhase, StateOnlyTerminalError,
};

const TRACE_ROWS: usize = 1024;
const C1_COLUMNS: usize = 16;
const PINNED_ATOMIC_STATE_ONLY_REGISTRY_FINGERPRINT_V3: u64 = 0xa524_9dda_67f7_5888;
const ATOMIC_PACKED_SEMANTIC_LANES: usize = 20;
const ATOMIC_SOURCE_SEMANTIC_LANES: usize = 77;
const ATOMIC_SELECTED_TERMINAL_COLUMNS: usize =
    C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + 2;
const ATOMIC_SELECTED_TERMINAL_CLAIMS: usize = 3 * ATOMIC_SELECTED_TERMINAL_COLUMNS;
const ATOMIC_SELECTED_H1_COLUMN: usize = C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
const ATOMIC_SELECTED_G_COLUMN: usize = ATOMIC_SELECTED_H1_COLUMN + 1;
const ATOMIC_RETAINED_INITIAL_BLOCK_INDICES: [usize; 4] = [0, 1, 22, 23];

#[derive(Clone, Copy)]
struct CompiledAtomicPattern {
    /// 0 = zero, 1 = constant, 2 = affine local cell.
    kinds: [u8; 16],
    columns: [u8; 16],
    scales: [u32; 16],
    offsets: [u32; 16],
}

#[derive(Clone, Copy)]
struct CompiledAtomicCopyEndpoint {
    row: u16,
    slot: u8,
    pattern: u8,
}

#[derive(Clone, Copy)]
struct CompiledAtomicCopyLink {
    tag: u32,
    producer: CompiledAtomicCopyEndpoint,
    consumer: CompiledAtomicCopyEndpoint,
}

mod constants {
    use super::{CompiledAtomicCopyEndpoint, CompiledAtomicCopyLink, CompiledAtomicPattern};
    include!("atomic_state_only_terminal_constants.rs");
}

mod legacy_partition_constants {
    use super::{CompiledAtomicCopyEndpoint, CompiledAtomicCopyLink, CompiledAtomicPattern};
    include!("atomic_state_only_terminal_constants_legacy_partition.rs");
}

pub const ATOMIC_STATE_ONLY_COMPILED_COPY_LINKS: usize =
    constants::COMPILED_ATOMIC_COPY_LINKS.len();
pub const ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS: usize = constants::ATOMIC_COPY_PATTERNS.len();
pub const ATOMIC_STATE_ONLY_COMPILED_ROUTING_RANK: usize = constants::ATOMIC_COPY_ROUTING_RANK;
pub const ATOMIC_STATE_ONLY_COMPILED_ROUTING_SHARED_PAIRS: usize =
    constants::ATOMIC_COPY_ROUTING_PAIR_TERMS.len();
pub const ATOMIC_STATE_ONLY_COMPILED_ACTIVE_ROWS: usize =
    constants::COMPILED_ATOMIC_COPY_ACTIVE_ROWS.len();
pub const ATOMIC_STATE_ONLY_COMPILED_INACTIVE_ROWS: usize =
    TRACE_ROWS - ATOMIC_STATE_ONLY_COMPILED_ACTIVE_ROWS;
pub const PINNED_ATOMIC_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT_V3: u64 =
    constants::COMPILED_ATOMIC_COPY_ACTIVE_ROWS_FINGERPRINT;

const _: () = assert!(
    constants::COMPILED_ATOMIC_REGISTRY_FINGERPRINT
        == PINNED_ATOMIC_STATE_ONLY_REGISTRY_FINGERPRINT_V3
);
const _: () = assert!(ATOMIC_STATE_ONLY_COMPILED_COPY_LINKS == 183);
const _: () = assert!(ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS == 15);
const _: () = assert!(ATOMIC_STATE_ONLY_COMPILED_ROUTING_RANK == 74);
const _: () = assert!(ATOMIC_STATE_ONLY_COMPILED_ROUTING_SHARED_PAIRS == 61);
const _: () = assert!(ATOMIC_STATE_ONLY_COMPILED_ACTIVE_ROWS == 210);
const _: () = assert!(constants::ATOMIC_COPY_ROUTING_LOW_ROW_BITS == 0x03c0);
const _: () = assert!(legacy_partition_constants::ATOMIC_COPY_ROUTING_LOW_ROW_BITS == 0x000f);
const _: () = assert!(legacy_partition_constants::ATOMIC_COPY_ROUTING_RANK == 103);
const _: () = assert!(legacy_partition_constants::ATOMIC_COPY_ROUTING_PAIR_TERMS.len() == 84);
const _: () = assert!(state_constants::INITIAL_BLOCKS.len() == 24);
const _: () = assert!(state_constants::INITIAL_BLOCKS[0].0 == 0);
const _: () = assert!(state_constants::INITIAL_BLOCKS[1].0 == 16);
const _: () = assert!(state_constants::INITIAL_BLOCKS[2].0 == 64);
const _: () = assert!(state_constants::INITIAL_BLOCKS[21].0 == 672);
const _: () = assert!(state_constants::INITIAL_BLOCKS[22].0 == 704);
const _: () = assert!(state_constants::INITIAL_BLOCKS[23].0 == 736);
const _: () = assert!(
    legacy_partition_constants::COMPILED_ATOMIC_REGISTRY_FINGERPRINT
        == PINNED_ATOMIC_STATE_ONLY_REGISTRY_FINGERPRINT_V3
);

pub fn atomic_state_only_copy_active_rows_v3(
) -> &'static [u16; ATOMIC_STATE_ONLY_COMPILED_ACTIVE_ROWS] {
    &constants::COMPILED_ATOMIC_COPY_ACTIVE_ROWS
}

pub fn atomic_state_only_copy_inactive_row_masks_v3() -> [u16; 64] {
    let mut masks = [u16::MAX; 64];
    for &row in &constants::COMPILED_ATOMIC_COPY_ACTIVE_ROWS {
        let row = usize::from(row);
        masks[row >> 4] &= !(1u16 << (row & 15));
    }
    masks
}

pub fn atomic_state_only_copy_inactive_indicator_v3() -> Vec<QM31> {
    atomic_state_only_copy_inactive_row_masks_v3()
        .into_iter()
        .flat_map(|mask| {
            (0..16).map(move |low| {
                if mask & (1 << low) == 0 {
                    QM31::ZERO
                } else {
                    QM31::ONE
                }
            })
        })
        .collect()
}

#[derive(Clone, Copy)]
struct AtomicSelectors {
    high: [QM31; 64],
    low: [QM31; 16],
}

#[inline(always)]
fn projected_row_index(row: usize, bit_mask: u16) -> usize {
    let mut output = 0usize;
    for bit in (0..10).rev() {
        if bit_mask & (1 << bit) != 0 {
            output = (output << 1) | ((row >> bit) & 1);
        }
    }
    output
}

impl AtomicSelectors {
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
            // high indexes row bits 5..0, hence point coordinates 4..9;
            // low indexes row bits 9..6, hence point coordinates 0..3.
            high: Self::expand(&point[4..]),
            low: Self::expand(&point[..4]),
        }
    }

    #[inline(always)]
    fn row(&self, row: usize) -> QM31 {
        debug_assert!(row < TRACE_ROWS);
        let low_bits = constants::ATOMIC_COPY_ROUTING_LOW_ROW_BITS;
        let high_bits = (!low_bits) & 0x03ff;
        self.high[projected_row_index(row, high_bits)]
            .mul(self.low[projected_row_index(row, low_bits)])
    }

    fn copy_active(&self) -> QM31 {
        constants::COMPILED_ATOMIC_COPY_ACTIVE_FACTORS
            .iter()
            .copied()
            .fold(QM31::ZERO, |sum, (high_mask, low_mask)| {
                let high = self
                    .high
                    .iter()
                    .copied()
                    .enumerate()
                    .filter(|(index, _)| high_mask & (1u64 << index) != 0)
                    .fold(QM31::ZERO, |sum, (_, value)| sum.add(value));
                let low = self
                    .low
                    .iter()
                    .copied()
                    .enumerate()
                    .filter(|(index, _)| low_mask & (1u16 << index) != 0)
                    .fold(QM31::ZERO, |sum, (_, value)| sum.add(value));
                sum.add(high.mul(low))
            })
    }
}

#[derive(Clone, Copy)]
struct LegacyAtomicSelectors {
    high: [QM31; 64],
    low: [QM31; 16],
}

impl LegacyAtomicSelectors {
    fn at_point(point: &[QM31; 10]) -> Self {
        Self {
            high: AtomicSelectors::expand(&point[..6]),
            low: AtomicSelectors::expand(&point[6..]),
        }
    }

    fn copy_active(&self) -> QM31 {
        legacy_partition_constants::COMPILED_ATOMIC_COPY_ACTIVE_FACTORS
            .iter()
            .copied()
            .fold(QM31::ZERO, |sum, (mut high_mask, mut low_mask)| {
                // Both arrays are complete multilinear equality bases, so
                // each sums to one at every (including off-domain) point.
                // Evaluate a dense mask through its smaller complement.  In
                // the deployed six-factor partition this turns the 42-entry
                // high mask into 22 subtractions.
                let high = if high_mask.count_ones() > 32 {
                    high_mask = !high_mask;
                    let mut high = QM31::ONE;
                    while high_mask != 0 {
                        let index = high_mask.trailing_zeros() as usize;
                        high = high.sub(self.high[index]);
                        high_mask &= high_mask - 1;
                    }
                    high
                } else {
                    let mut high = QM31::ZERO;
                    while high_mask != 0 {
                        let index = high_mask.trailing_zeros() as usize;
                        high = high.add(self.high[index]);
                        high_mask &= high_mask - 1;
                    }
                    high
                };
                // The final deployed low mask selects all sixteen basis
                // values, hence is exactly one without a scan.
                let low = if low_mask == u16::MAX {
                    QM31::ONE
                } else {
                    let mut low = QM31::ZERO;
                    while low_mask != 0 {
                        let index = low_mask.trailing_zeros() as usize;
                        low = low.add(self.low[index]);
                        low_mask &= low_mask - 1;
                    }
                    low
                };
                sum.add(high.mul(low))
            })
    }
}

#[derive(Clone, Copy)]
struct AtomicSemanticSelectors {
    high: [QM31; 64],
    low: [QM31; 16],
}

impl AtomicSemanticSelectors {
    fn at_point(point: &[QM31; 10]) -> Self {
        Self {
            high: AtomicSelectors::expand(&point[..6]),
            low: AtomicSelectors::expand(&point[6..]),
        }
    }

    #[inline(always)]
    fn row(&self, row: usize) -> QM31 {
        self.high[row >> 4].mul(self.low[row & 15])
    }

    fn poseidon(&self) -> StateOnlyPoseidonSelectors {
        StateOnlyPoseidonSelectors {
            block: self.high[..crate::state_only_poseidon::STATE_ONLY_POSEIDON_BLOCKS]
                .iter()
                .copied()
                .fold(QM31::ZERO, QM31::add),
            local: self.low,
        }
    }
}

#[inline(always)]
fn lift(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}

fn atomic_copy_pattern_values(
    openings: &[QM31; C1_COLUMNS],
    powers: &[QM31; 16],
) -> [QM31; ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS] {
    // The generated inventory has fifteen affine tuple shapes but only five
    // distinct length-eight opening windows. Since
    // powers[j + 8] = powers[j] * lambda^8, compute those windows once and
    // reconstruct every shape by an exact field identity. The generated
    // constants remain the provenance for both affine offsets.
    let a = qm31_dot(&powers[..8], &openings[..8]);
    let b = qm31_dot(&powers[..8], &openings[8..16]);
    let c = qm31_dot(&powers[..8], &openings[1..9]);
    let d_values = [
        openings[8],
        openings[9],
        openings[10],
        openings[11],
        openings[12],
        openings[13],
        openings[0],
        openings[1],
    ];
    let d = qm31_dot(&powers[..8], &d_values);
    let e = qm31_dot(&powers[..8], &openings[2..10]);
    let lambda = powers[0];
    let lambda8 = powers[7];
    let x0 = powers[0].mul(openings[0]);
    let x11 = powers[0].mul(openings[11]);
    let x12 = powers[0].mul(openings[12]);
    let path_tweak = M31(constants::ATOMIC_COPY_PATTERNS[14].offsets[8]);
    [
        a.add(lambda8.mul(b)),
        a,
        c,
        b,
        d,
        b.add(lambda8.mul(b)),
        a.add(lambda8.mul(e)),
        a.add(lambda8.mul(d)),
        x11,
        x0,
        x12,
        a.add(powers[8].mul(openings[8])),
        lambda.mul(a),
        powers[0].add(lambda.mul(c)).sub(x0),
        powers[0]
            .add(lambda.mul(b))
            .add(powers[8].mul_m31(path_tweak)),
    ]
}

#[cfg(test)]
fn atomic_copy_pattern_values_generated_reference(
    openings: &[QM31; C1_COLUMNS],
    powers: &[QM31; 16],
) -> [QM31; ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS] {
    constants::ATOMIC_COPY_PATTERNS.map(|pattern| {
        let mut value = QM31::ZERO;
        for limb in 0..16 {
            let source = match pattern.kinds[limb] {
                0 => continue,
                1 => lift(M31(pattern.offsets[limb])),
                2 => openings[usize::from(pattern.columns[limb])]
                    .mul_m31(M31(pattern.scales[limb]))
                    .add(lift(M31(pattern.offsets[limb]))),
                _ => unreachable!("generated atomic tuple kind"),
            };
            value = value.add(powers[limb].mul(source));
        }
        value
    })
}

#[inline(always)]
fn routing_linear_form(entries: &[(u8, u32)], selectors: &[QM31]) -> QM31 {
    // Keep exact ±1 terms in their own small accumulator. The generated
    // factors contain at most 52 entries, so even the noncanonical `P - 0`
    // representative is bounded by `52 * P < 2^64`. Genuine products retain
    // the audited four-product groups: `4 * (P - 1)^2 < 2^64`.
    let mut signed = [0u64; 4];
    let mut products = [0u64; 4];
    let mut reduced_products = [0u64; 4];
    let mut product_count = 0usize;
    for &(index, coefficient) in entries {
        let selector = selectors[usize::from(index)];
        let limbs = [
            selector.c0.a.0,
            selector.c0.b.0,
            selector.c1.a.0,
            selector.c1.b.0,
        ];
        match coefficient {
            1 => {
                for limb in 0..4 {
                    signed[limb] += u64::from(limbs[limb]);
                }
            }
            value if value == P - 1 => {
                for limb in 0..4 {
                    signed[limb] += u64::from(P) - u64::from(limbs[limb]);
                }
            }
            _ => {
                for limb in 0..4 {
                    products[limb] += u64::from(limbs[limb]) * u64::from(coefficient);
                }
                product_count += 1;
                if product_count == 4 {
                    for limb in 0..4 {
                        reduced_products[limb] += u64::from(M31::reduce_u64(products[limb]).0);
                    }
                    products = [0u64; 4];
                    product_count = 0;
                }
            }
        }
    }
    if product_count != 0 {
        for limb in 0..4 {
            reduced_products[limb] += u64::from(M31::reduce_u64(products[limb]).0);
        }
    }
    QM31 {
        c0: CM31::new(
            M31::reduce_u64(signed[0] + reduced_products[0]),
            M31::reduce_u64(signed[1] + reduced_products[1]),
        ),
        c1: CM31::new(
            M31::reduce_u64(signed[2] + reduced_products[2]),
            M31::reduce_u64(signed[3] + reduced_products[3]),
        ),
    }
}

#[cfg(test)]
fn routing_linear_form_four_entry_reference(entries: &[(u8, u32)], selectors: &[QM31]) -> QM31 {
    let mut sums = [0u64; 4];
    for block in entries.chunks(4) {
        let mut raw = [0u64; 4];
        for &(index, coefficient) in block {
            let selector = selectors[usize::from(index)];
            let limbs = [
                selector.c0.a.0,
                selector.c0.b.0,
                selector.c1.a.0,
                selector.c1.b.0,
            ];
            match coefficient {
                1 => {
                    for limb in 0..4 {
                        raw[limb] += u64::from(limbs[limb]);
                    }
                }
                value if value == P - 1 => {
                    for limb in 0..4 {
                        raw[limb] += u64::from(P) - u64::from(limbs[limb]);
                    }
                }
                _ => {
                    for limb in 0..4 {
                        raw[limb] += u64::from(limbs[limb]) * u64::from(coefficient);
                    }
                }
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

#[cfg(test)]
fn routing_linear_form_reference(entries: &[(u8, u32)], selectors: &[QM31]) -> QM31 {
    entries
        .iter()
        .copied()
        .fold(QM31::ZERO, |sum, (index, coefficient)| {
            sum.add(selectors[usize::from(index)].mul_m31(M31(coefficient)))
        })
}

#[cfg(test)]
fn legacy_copy_active_scanning_reference(selectors: &LegacyAtomicSelectors) -> QM31 {
    legacy_partition_constants::COMPILED_ATOMIC_COPY_ACTIVE_FACTORS
        .iter()
        .copied()
        .fold(QM31::ZERO, |sum, (high_mask, low_mask)| {
            let high = selectors
                .high
                .iter()
                .copied()
                .enumerate()
                .filter(|(index, _)| high_mask & (1u64 << index) != 0)
                .fold(QM31::ZERO, |sum, (_, value)| sum.add(value));
            let low = selectors
                .low
                .iter()
                .copied()
                .enumerate()
                .filter(|(index, _)| low_mask & (1u16 << index) != 0)
                .fold(QM31::ZERO, |sum, (_, value)| sum.add(value));
            sum.add(high.mul(low))
        })
}

fn evaluate_atomic_copy_routing(selectors: &AtomicSelectors) -> Vec<QM31> {
    let left_values = (0..constants::ATOMIC_COPY_ROUTING_LEFT_FACTORS.len())
        .map(|index| {
            let (start, len) = constants::ATOMIC_COPY_ROUTING_LEFT_FACTORS[index];
            let start = usize::from(start);
            routing_linear_form(
                &constants::ATOMIC_COPY_ROUTING_ENTRIES[start..start + usize::from(len)],
                &selectors.high,
            )
        })
        .collect::<Vec<_>>();
    let right_values = (0..constants::ATOMIC_COPY_ROUTING_RIGHT_FACTORS.len())
        .map(|index| {
            let (start, len) = constants::ATOMIC_COPY_ROUTING_RIGHT_FACTORS[index];
            let start = usize::from(start);
            routing_linear_form(
                &constants::ATOMIC_COPY_ROUTING_ENTRIES[start..start + usize::from(len)],
                &selectors.low,
            )
        })
        .collect::<Vec<_>>();
    let mut matrices = vec![QM31::ZERO; 4 * (2 + ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS)];
    for &(left, right, matrix_start, matrix_len) in &constants::ATOMIC_COPY_ROUTING_PAIR_TERMS {
        let product = left_values[usize::from(left)].mul(right_values[usize::from(right)]);
        let start = usize::from(matrix_start);
        for &matrix in
            &constants::ATOMIC_COPY_ROUTING_DESTINATIONS[start..start + usize::from(matrix_len)]
        {
            matrices[usize::from(matrix)] = matrices[usize::from(matrix)].add(product);
        }
    }
    matrices
}

fn evaluate_atomic_copy_routing_legacy(selectors: &LegacyAtomicSelectors) -> Vec<QM31> {
    let left_values = (0..legacy_partition_constants::ATOMIC_COPY_ROUTING_LEFT_FACTORS.len())
        .map(|index| {
            let (start, len) = legacy_partition_constants::ATOMIC_COPY_ROUTING_LEFT_FACTORS[index];
            let start = usize::from(start);
            routing_linear_form(
                &legacy_partition_constants::ATOMIC_COPY_ROUTING_ENTRIES
                    [start..start + usize::from(len)],
                &selectors.high,
            )
        })
        .collect::<Vec<_>>();
    let right_values = (0..legacy_partition_constants::ATOMIC_COPY_ROUTING_RIGHT_FACTORS.len())
        .map(|index| {
            let (start, len) = legacy_partition_constants::ATOMIC_COPY_ROUTING_RIGHT_FACTORS[index];
            let start = usize::from(start);
            routing_linear_form(
                &legacy_partition_constants::ATOMIC_COPY_ROUTING_ENTRIES
                    [start..start + usize::from(len)],
                &selectors.low,
            )
        })
        .collect::<Vec<_>>();
    let mut matrices = vec![QM31::ZERO; 4 * (2 + ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS)];
    for &(left, right, matrix_start, matrix_len) in
        &legacy_partition_constants::ATOMIC_COPY_ROUTING_PAIR_TERMS
    {
        let product = left_values[usize::from(left)].mul(right_values[usize::from(right)]);
        let start = usize::from(matrix_start);
        for &matrix in &legacy_partition_constants::ATOMIC_COPY_ROUTING_DESTINATIONS
            [start..start + usize::from(matrix_len)]
        {
            matrices[usize::from(matrix)] = matrices[usize::from(matrix)].add(product);
        }
    }
    matrices
}

fn atomic_copy_lane_from_routing_impl<F>(
    openings: &[QM31; C1_COLUMNS],
    h1_z: QM31,
    selectors: &AtomicSelectors,
    lambda: QM31,
    chi: QM31,
    mut trace: F,
) -> QM31
where
    F: FnMut(StateOnlyTerminalDiagnosticPhase),
{
    let mut powers = [QM31::ZERO; 16];
    powers[0] = lambda;
    for index in 1..powers.len() {
        powers[index] = powers[index - 1].mul(lambda);
    }
    let pattern_values = atomic_copy_pattern_values(openings, &powers);
    trace(StateOnlyTerminalDiagnosticPhase::CopyPatterns);
    let routing = evaluate_atomic_copy_routing(selectors);
    trace(StateOnlyTerminalDiagnosticPhase::CopyRouting);
    let mut values = [QM31::ZERO; 4];
    let mut weights = [QM31::ZERO; 4];
    for slot in 0..4 {
        let base = slot * (2 + ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS);
        weights[slot] = routing[base];
        values[slot] = routing[base + 1];
        let mut support = constants::ATOMIC_COPY_ROUTING_PATTERN_MASKS[slot];
        while support != 0 {
            let pattern = support.trailing_zeros() as usize;
            values[slot] =
                values[slot].add(routing[base + 2 + pattern].mul(pattern_values[pattern]));
            support &= support - 1;
        }
    }
    let d = [
        chi.sub(values[0]),
        chi.sub(values[1]),
        chi.sub(values[2]),
        chi.sub(values[3]),
    ];
    let producer_denominator = d[0].mul(d[1]);
    let consumer_denominator = d[2].mul(d[3]);
    let producer = weights[0].mul(d[1]).add(weights[1].mul(d[0]));
    let consumer = weights[2].mul(d[3]).add(weights[3].mul(d[2]));
    let output = selectors.copy_active().mul(
        producer_denominator
            .mul(h1_z.mul(consumer_denominator).add(consumer))
            .sub(consumer_denominator.mul(producer)),
    );
    trace(StateOnlyTerminalDiagnosticPhase::Copy);
    output
}

#[inline(never)]
fn atomic_copy_lane_from_routing(
    openings: &[QM31; C1_COLUMNS],
    h1_z: QM31,
    selectors: &AtomicSelectors,
    lambda: QM31,
    chi: QM31,
) -> QM31 {
    atomic_copy_lane_from_routing_impl(openings, h1_z, selectors, lambda, chi, |_| {})
}

/// Evaluate the exact atomic-v3 copy/LogUp terminal lane from the z opening.
pub fn atomic_state_only_copy_terminal_lane_compiled_v3(
    openings_z: &[QM31; C1_COLUMNS],
    h1_z: QM31,
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
) -> QM31 {
    let selectors = Box::new(AtomicSelectors::at_point(point));
    atomic_copy_lane_from_routing(openings_z, h1_z, &selectors, lambda, chi)
}

#[inline(never)]
fn atomic_copy_lane_from_shared_semantic_routing_impl<F>(
    openings: &[QM31; C1_COLUMNS],
    h1_z: QM31,
    selectors: &AtomicSemanticSelectors,
    lambda: QM31,
    chi: QM31,
    mut trace: F,
) -> QM31
where
    F: FnMut(StateOnlyTerminalDiagnosticPhase),
{
    let legacy = LegacyAtomicSelectors {
        high: selectors.high,
        low: selectors.low,
    };
    let mut powers = [QM31::ZERO; 16];
    powers[0] = lambda;
    let prepared_lambda = PreparedQm31Multiplier::new(lambda);
    for index in 1..powers.len() {
        powers[index] = prepared_lambda.mul(powers[index - 1]);
    }
    let pattern_values = atomic_copy_pattern_values(openings, &powers);
    trace(StateOnlyTerminalDiagnosticPhase::CopyPatterns);
    let routing = evaluate_atomic_copy_routing_legacy(&legacy);
    trace(StateOnlyTerminalDiagnosticPhase::CopyRouting);
    let mut values = [QM31::ZERO; 4];
    let mut weights = [QM31::ZERO; 4];
    for slot in 0..4 {
        let base = slot * (2 + ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS);
        weights[slot] = routing[base];
        values[slot] = routing[base + 1];
        let mut support = legacy_partition_constants::ATOMIC_COPY_ROUTING_PATTERN_MASKS[slot];
        while support != 0 {
            let pattern = support.trailing_zeros() as usize;
            values[slot] =
                values[slot].add(routing[base + 2 + pattern].mul(pattern_values[pattern]));
            support &= support - 1;
        }
    }
    let d = [
        chi.sub(values[0]),
        chi.sub(values[1]),
        chi.sub(values[2]),
        chi.sub(values[3]),
    ];
    let producer_denominator = d[0].mul(d[1]);
    let consumer_denominator = d[2].mul(d[3]);
    let producer = weights[0].mul(d[1]).add(weights[1].mul(d[0]));
    let consumer = weights[2].mul(d[3]).add(weights[3].mul(d[2]));
    let output = legacy.copy_active().mul(
        producer_denominator
            .mul(h1_z.mul(consumer_denominator).add(consumer))
            .sub(consumer_denominator.mul(producer)),
    );
    trace(StateOnlyTerminalDiagnosticPhase::Copy);
    output
}

/// Exact rank-103 partition retained as both the append-only SBF A/B reference
/// and the selected integrated routing basis.  In the full terminal its
/// `(bits 9..4, bits 3..0)` factors reuse the already-built semantic selector
/// tensor, which is cheaper end-to-end than expanding a second rank-74 tensor.
/// It computes exactly the same atomic-v3 copy polynomial as the generated
/// minimum-rank path.
pub fn atomic_state_only_copy_terminal_lane_legacy_partition_v3(
    openings_z: &[QM31; C1_COLUMNS],
    h1_z: QM31,
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
) -> QM31 {
    let selectors = Box::new(AtomicSemanticSelectors::at_point(point));
    atomic_copy_lane_from_shared_semantic_routing_impl(
        openings_z,
        h1_z,
        &selectors,
        lambda,
        chi,
        |_| {},
    )
}

#[inline(always)]
fn atomic_selected_claim(
    claims: &[QM31; ATOMIC_SELECTED_TERMINAL_CLAIMS],
    point: usize,
    column: usize,
) -> QM31 {
    claims[point * ATOMIC_SELECTED_TERMINAL_COLUMNS + column]
}

#[inline(always)]
fn atomic_add_preweighted<const N: usize>(
    packed: &mut [QM31; ATOMIC_PACKED_SEMANTIC_LANES],
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

#[inline(always)]
fn atomic_accumulate<const N: usize>(
    packed: &mut [QM31; ATOMIC_PACKED_SEMANTIC_LANES],
    start: usize,
    values: &[QM31; N],
    selector: QM31,
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
        packed[group] = packed[group].add(selector.mul(qm31_pack_base4(&lanes)));
    }
}

#[inline(always)]
fn atomic_retained_initial_sums(selectors: &AtomicSemanticSelectors) -> (QM31, QM31, QM31) {
    let highs = ATOMIC_RETAINED_INITIAL_BLOCK_INDICES.map(|index| {
        let block = usize::from(state_constants::INITIAL_BLOCKS[index].0) >> 4;
        selectors.high[block]
    });
    let high_sum = highs.iter().copied().fold(QM31::ZERO, QM31::add);
    let domains = ATOMIC_RETAINED_INITIAL_BLOCK_INDICES
        .map(|index| M31(state_constants::INITIAL_BLOCKS[index].1));
    let lengths = ATOMIC_RETAINED_INITIAL_BLOCK_INDICES
        .map(|index| M31(state_constants::INITIAL_BLOCKS[index].2));
    (
        high_sum,
        qm31_m31_dot(&highs, &domains),
        qm31_m31_dot(&highs, &lengths),
    )
}

#[inline(never)]
fn atomic_semantic_packed_impl<F>(
    statement: &AtomicPaymentStatementV4,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &AtomicSemanticSelectors,
    mut trace: F,
) -> [QM31; ATOMIC_PACKED_SEMANTIC_LANES]
where
    F: FnMut(StateOnlyTerminalDiagnosticPhase),
{
    let mut packed = [QM31::ZERO; ATOMIC_PACKED_SEMANTIC_LANES];

    // Atomic path blocks 4..=43 carry a dynamic right child in row-0 lanes
    // 8..15 and the left child in row 12.  Their copy tuples bind the dynamic
    // child (including the lane-15 tweak), so only row-0 lanes 0..7 are fixed
    // to zero.  The retained owner/note/nullifier/output blocks keep the
    // original domain/length initial-state constraints.
    let (initial_high_sum, domain_sum, length_sum) = atomic_retained_initial_sums(selectors);
    let initial_selector = selectors.low[0].mul(initial_high_sum);
    for group in 0..4 {
        packed[group] =
            initial_selector.mul(qm31_pack_base4(&openings.z[4 * group..4 * group + 4]));
    }
    packed[2] = packed[2].sub(selectors.low[0].mul(qm31_pack_base4(&[
        domain_sum,
        length_sum,
        QM31::ZERO,
        QM31::ZERO,
    ])));
    let path_initial_selector = selectors.low[0]
        .mul((4..=43).fold(QM31::ZERO, |sum, block| sum.add(selectors.high[block])));
    for group in 0..2 {
        packed[group] = packed[group]
            .add(path_initial_selector.mul(qm31_pack_base4(&openings.z[4 * group..4 * group + 4])));
    }
    trace(StateOnlyTerminalDiagnosticPhase::SemanticInitial);

    for mask in [0x00fcu16, 0xff00, 0xfffc] {
        let high_sum = state_constants::ABSORPTION_ZERO_MASKS
            .iter()
            .copied()
            .enumerate()
            .filter(|(block, candidate)| !(4..=43).contains(block) && *candidate == mask)
            .fold(QM31::ZERO, |sum, (block, _)| sum.add(selectors.high[block]));
        let selector = selectors.low[12].mul(high_sum);
        for group in 0..4 {
            if mask & (0xf << (4 * group)) != 0 {
                let residuals: [QM31; 4] = core::array::from_fn(|slot| {
                    let lane = 4 * group + slot;
                    if mask & (1 << lane) != 0 {
                        openings.z[lane]
                    } else {
                        QM31::ZERO
                    }
                });
                packed[4 + group] =
                    packed[4 + group].add(selector.mul(qm31_pack_base4(&residuals)));
            }
        }
    }
    trace(StateOnlyTerminalDiagnosticPhase::SemanticAbsorption);
    // Atomic path selection is enforced by the copy lane, so there is no
    // separate Merkle semantic polynomial. Keep the named boundary so the
    // atomic and baseline breakdown ledgers remain directly comparable.
    trace(StateOnlyTerminalDiagnosticPhase::SemanticMerkle);

    let range_selectors = [selectors.row(864), selectors.row(866)];
    let range_selector = range_selectors[0].add(range_selectors[1]);
    let range_residuals: [QM31; 33] = core::array::from_fn(|index| {
        if index < 30 {
            let view = match index / 10 {
                0 => &openings.z,
                1 => &openings.succ_z,
                _ => &openings.xor12_z,
            };
            let bit = view[index % 10];
            bit.mul(bit.sub(QM31::ONE))
        } else {
            let view = match index - 30 {
                0 => &openings.z,
                1 => &openings.succ_z,
                _ => &openings.xor12_z,
            };
            let reconstructed = (0..10).fold(QM31::ZERO, |sum, bit| {
                sum.add(view[bit].mul_m31(M31(1 << bit)))
            });
            view[10].sub(reconstructed)
        }
    });
    atomic_accumulate(&mut packed, 32, &range_residuals, range_selector);

    let triple_value = openings.z[10]
        .add(openings.succ_z[10].mul_m31(M31(1 << 10)))
        .add(openings.xor12_z[10].mul_m31(M31(1 << 20)));
    let totals = [
        range_selector.mul(openings.z[11].sub(triple_value)),
        range_selectors[0].mul(
            openings.z[11]
                .sub(openings.z[12])
                .sub(lift(M31(statement.spend.fee))),
        ),
    ];
    atomic_add_preweighted(&mut packed, 65, &totals);
    trace(StateOnlyTerminalDiagnosticPhase::SemanticRange);

    for (block, digest) in [
        (23usize, &statement.spend.anchor),
        (43usize, &statement.output_anchor),
        (45usize, &statement.spend.nullifier),
        (48usize, &statement.spend.output_commitment),
    ] {
        let residuals: [QM31; DIGEST_ELEMS] =
            core::array::from_fn(|limb| openings.z[limb].sub(lift(digest[limb])));
        atomic_accumulate(&mut packed, 67, &residuals, selectors.row(block * 16 + 11));
    }

    let assets: [QM31; 2] = core::array::from_fn(|lane| {
        let (row, column) = [
            state_constants::INPUT_ASSET_CELL,
            state_constants::OUTPUT_ASSET_CELL,
        ][lane];
        selectors
            .row(usize::from(row))
            .mul(openings.z[usize::from(column)].sub(lift(statement.spend.asset_id)))
    });
    atomic_add_preweighted(&mut packed, 75, &assets);
    trace(StateOnlyTerminalDiagnosticPhase::SemanticPublic);
    packed
}

#[inline(never)]
fn atomic_semantic_packed(
    statement: &AtomicPaymentStatementV4,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &AtomicSemanticSelectors,
) -> [QM31; ATOMIC_PACKED_SEMANTIC_LANES] {
    atomic_semantic_packed_impl(statement, openings, selectors, |_| {})
}

fn atomic_equality_value(left: &[QM31; 10], right: &[QM31; 10]) -> QM31 {
    left.iter().zip(right).fold(QM31::ONE, |product, (a, b)| {
        let ab = a.mul(*b);
        product.mul(QM31::ONE.sub(*a).sub(*b).add(ab).add(ab))
    })
}

#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn atomic_state_only_composition_parts_compiled_v3(
    statement: &AtomicPaymentStatementV4,
    claims: &[QM31; ATOMIC_SELECTED_TERMINAL_CLAIMS],
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
) -> Result<
    (
        QM31,
        [QM31; C1_COLUMNS],
        [QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
        QM31,
        QM31,
    ),
    StateOnlyTerminalError,
> {
    if statement.spend.fee >= VALUE_LIMIT {
        return Err(StateOnlyTerminalError::PublicFeeOutOfRange);
    }
    let openings = StateOnlyPoseidonOpenings {
        z: core::array::from_fn(|column| atomic_selected_claim(claims, 0, column)),
        succ_z: core::array::from_fn(|column| atomic_selected_claim(claims, 1, column)),
        xor12_z: core::array::from_fn(|column| atomic_selected_claim(claims, 2, column)),
    };
    let mask_only =
        core::array::from_fn(|column| atomic_selected_claim(claims, 0, C1_COLUMNS + column));
    let selectors = Box::new(AtomicSemanticSelectors::at_point(point));
    let poseidon = evaluate_state_only_poseidon_oracle_projected(&openings, &selectors.poseidon());
    let semantic = atomic_semantic_packed(statement, &openings, &selectors);
    let h1_z = atomic_selected_claim(claims, 0, ATOMIC_SELECTED_H1_COLUMN);
    let copy = atomic_copy_lane_from_shared_semantic_routing_impl(
        &openings.z,
        h1_z,
        &selectors,
        lambda,
        chi,
        |_| {},
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
        atomic_selected_claim(claims, 0, ATOMIC_SELECTED_G_COLUMN),
        h1_z,
    ))
}

/// Exact randomized atomic-v3 constraint composition before the outer
/// zerocheck equality and helper-sum term.  Host tests use this to require
/// every honest Boolean row to vanish, preventing cancellation-only fixtures.
pub fn atomic_state_only_selected_constraint_composition_compiled_v3(
    statement: &AtomicPaymentStatementV4,
    claims: &[QM31; ATOMIC_SELECTED_TERMINAL_CLAIMS],
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
) -> Result<QM31, StateOnlyTerminalError> {
    Ok(atomic_state_only_composition_parts_compiled_v3(
        statement, claims, point, lambda, chi, theta,
    )?
    .0)
}

#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn atomic_state_only_terminal_parts_compiled_v3(
    statement: &AtomicPaymentStatementV4,
    claims: &[QM31; ATOMIC_SELECTED_TERMINAL_CLAIMS],
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
    zerocheck_point: &[QM31; 10],
    mu: QM31,
) -> Result<
    (
        QM31,
        [QM31; C1_COLUMNS],
        [QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
        QM31,
    ),
    StateOnlyTerminalError,
> {
    let (composition, c1, mask_only, g, h1_z) = atomic_state_only_composition_parts_compiled_v3(
        statement, claims, point, lambda, chi, theta,
    )?;
    let original = atomic_equality_value(zerocheck_point, point)
        .mul(composition)
        .add(mu.mul(h1_z));
    Ok((original, c1, mask_only, g))
}

/// Exact unmasked atomic-v3 zerocheck terminal.  The prover uses this same
/// compiled polynomial at every sumcheck oracle point; the verifier later
/// checks its masked affine combination against the transcript-bound claim.
#[allow(clippy::too_many_arguments)]
pub fn atomic_state_only_selected_unmasked_terminal_value_compiled_v3(
    statement: &AtomicPaymentStatementV4,
    claims: &[QM31; ATOMIC_SELECTED_TERMINAL_CLAIMS],
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
    zerocheck_point: &[QM31; 10],
    mu: QM31,
) -> Result<QM31, StateOnlyTerminalError> {
    Ok(atomic_state_only_terminal_parts_compiled_v3(
        statement,
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

/// Complete width-28 masked terminal for the sound same-private-path atomic
/// replacement statement.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
pub fn atomic_state_only_selected_masked_terminal_value_compiled_v3(
    statement: &AtomicPaymentStatementV4,
    claims: &[QM31; ATOMIC_SELECTED_TERMINAL_CLAIMS],
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
    zerocheck_point: &[QM31; 10],
    mu: QM31,
    eta: QM31,
) -> Result<QM31, StateOnlyTerminalError> {
    let (original, c1, mask_only, g) = atomic_state_only_terminal_parts_compiled_v3(
        statement,
        claims,
        point,
        lambda,
        chi,
        theta,
        zerocheck_point,
        mu,
    )?;
    let mask = state_only_selected_mask_value(&c1, &mask_only, g, point);
    Ok(mask.add(eta.mul(original)))
}

/// Diagnostic-only internal boundaries for the exact atomic-v3 terminal.
/// This duplicates the production expression deliberately and is pinned to
/// it by fresh random-QM31 identity tests. It changes no proof or challenge.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
pub fn atomic_state_only_selected_masked_terminal_value_compiled_with_diagnostic_trace_v3<F>(
    statement: &AtomicPaymentStatementV4,
    claims: &[QM31; ATOMIC_SELECTED_TERMINAL_CLAIMS],
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
    zerocheck_point: &[QM31; 10],
    mu: QM31,
    eta: QM31,
    mut trace: F,
) -> Result<QM31, StateOnlyTerminalError>
where
    F: FnMut(StateOnlyTerminalDiagnosticPhase),
{
    if statement.spend.fee >= VALUE_LIMIT {
        return Err(StateOnlyTerminalError::PublicFeeOutOfRange);
    }
    let openings = StateOnlyPoseidonOpenings {
        z: core::array::from_fn(|column| atomic_selected_claim(claims, 0, column)),
        succ_z: core::array::from_fn(|column| atomic_selected_claim(claims, 1, column)),
        xor12_z: core::array::from_fn(|column| atomic_selected_claim(claims, 2, column)),
    };
    let mask_only =
        core::array::from_fn(|column| atomic_selected_claim(claims, 0, C1_COLUMNS + column));
    let semantic_selectors = Box::new(AtomicSemanticSelectors::at_point(point));
    trace(StateOnlyTerminalDiagnosticPhase::Prepared);

    let poseidon =
        evaluate_state_only_poseidon_oracle_projected(&openings, &semantic_selectors.poseidon());
    trace(StateOnlyTerminalDiagnosticPhase::Poseidon);
    let semantic =
        atomic_semantic_packed_impl(statement, &openings, &semantic_selectors, &mut trace);
    let h1_z = atomic_selected_claim(claims, 0, ATOMIC_SELECTED_H1_COLUMN);
    let copy = atomic_copy_lane_from_shared_semantic_routing_impl(
        &openings.z,
        h1_z,
        &semantic_selectors,
        lambda,
        chi,
        &mut trace,
    );
    let prepared_theta = PreparedQm31Multiplier::new(theta);
    let mut composition = copy;
    for lane in semantic.into_iter().rev() {
        composition = prepared_theta.mul(composition).add(lane);
    }
    for lane in poseidon.into_iter().rev() {
        composition = prepared_theta.mul(composition).add(lane);
    }
    let original = atomic_equality_value(zerocheck_point, point)
        .mul(composition)
        .add(mu.mul(h1_z));
    trace(StateOnlyTerminalDiagnosticPhase::CompositionEquality);
    let mask = state_only_selected_mask_value(
        &openings.z,
        &mask_only,
        atomic_selected_claim(claims, 0, ATOMIC_SELECTED_G_COLUMN),
        point,
    );
    trace(StateOnlyTerminalDiagnosticPhase::Mask);
    let output = mask.add(eta.mul(original));
    trace(StateOnlyTerminalDiagnosticPhase::Final);
    Ok(output)
}

const _: () = assert!(ATOMIC_SOURCE_SEMANTIC_LANES == 77);
const _: () = assert!(ATOMIC_PACKED_SEMANTIC_LANES == 20);
const _: () = assert!(ATOMIC_SELECTED_TERMINAL_COLUMNS == 28);
const _: () = assert!(ATOMIC_SELECTED_TERMINAL_CLAIMS == 84);

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::P;

    use crate::atomic_state_only_registry::{
        atomic_state_only_registry_fingerprint_v3, build_atomic_state_only_registry_v3,
        AtomicCopyTupleV3, AtomicTupleLimbV3,
    };
    use crate::SpendPublic;

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

    fn host_pattern(tuple: AtomicCopyTupleV3) -> CompiledAtomicPattern {
        let mut output = CompiledAtomicPattern {
            kinds: [0; 16],
            columns: [0; 16],
            scales: [0; 16],
            offsets: [0; 16],
        };
        for (index, limb) in tuple.limbs.into_iter().enumerate() {
            match limb {
                AtomicTupleLimbV3::Zero => {}
                AtomicTupleLimbV3::Constant(value) => {
                    output.kinds[index] = 1;
                    output.offsets[index] = value.0;
                }
                AtomicTupleLimbV3::AffineCell {
                    cell,
                    scale,
                    offset,
                } => {
                    assert_eq!(cell.row, tuple.row);
                    output.kinds[index] = 2;
                    output.columns[index] = cell.column;
                    output.scales[index] = scale.0;
                    output.offsets[index] = offset.0;
                }
            }
        }
        output
    }

    fn pattern_id(tuple: AtomicCopyTupleV3) -> u8 {
        let host = host_pattern(tuple);
        constants::ATOMIC_COPY_PATTERNS
            .iter()
            .position(|compiled| {
                compiled.kinds == host.kinds
                    && compiled.columns == host.columns
                    && compiled.scales == host.scales
                    && compiled.offsets == host.offsets
            })
            .unwrap() as u8
    }

    fn evaluate_routing_direct(
        selectors: &AtomicSelectors,
    ) -> [QM31; 4 * (2 + ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS)] {
        let mut matrices = [QM31::ZERO; 4 * (2 + ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS)];
        for link in constants::COMPILED_ATOMIC_COPY_LINKS {
            for (side, endpoint) in [(0usize, link.producer), (2usize, link.consumer)] {
                let slot = side + usize::from(endpoint.slot);
                let selector = selectors.row(usize::from(endpoint.row));
                let base = slot * (2 + ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS);
                matrices[base] = matrices[base].add(selector);
                matrices[base + 1] = matrices[base + 1].add(selector.mul_m31(M31(link.tag)));
                matrices[base + 2 + usize::from(endpoint.pattern)] =
                    matrices[base + 2 + usize::from(endpoint.pattern)].add(selector);
            }
        }
        matrices
    }

    fn tuple_value(
        tuple: AtomicCopyTupleV3,
        openings: &[QM31; C1_COLUMNS],
        powers: &[QM31; 16],
    ) -> QM31 {
        tuple
            .limbs
            .into_iter()
            .enumerate()
            .fold(QM31::ZERO, |sum, (limb, source)| {
                let value = match source {
                    AtomicTupleLimbV3::Zero => return sum,
                    AtomicTupleLimbV3::Constant(value) => lift(value),
                    AtomicTupleLimbV3::AffineCell {
                        cell,
                        scale,
                        offset,
                    } => openings[usize::from(cell.column)]
                        .mul_m31(scale)
                        .add(lift(offset)),
                };
                sum.add(powers[limb].mul(value))
            })
    }

    fn copy_lane_direct(
        openings: &[QM31; C1_COLUMNS],
        h1_z: QM31,
        selectors: &AtomicSelectors,
        lambda: QM31,
        chi: QM31,
    ) -> QM31 {
        let registry = build_atomic_state_only_registry_v3().unwrap();
        let mut powers = [QM31::ZERO; 16];
        powers[0] = lambda;
        for index in 1..powers.len() {
            powers[index] = powers[index - 1].mul(lambda);
        }
        let mut values = [QM31::ZERO; 4];
        let mut weights = [QM31::ZERO; 4];
        let mut producer_arity = [0u8; TRACE_ROWS];
        let mut consumer_arity = [0u8; TRACE_ROWS];
        for link in registry.links {
            for (side, tuple, arity) in [
                (0usize, link.producer, &mut producer_arity),
                (2usize, link.consumer, &mut consumer_arity),
            ] {
                let row = usize::from(tuple.row);
                let slot = side + usize::from(arity[row]);
                arity[row] += 1;
                let selector = selectors.row(row);
                weights[slot] = weights[slot].add(selector);
                values[slot] = values[slot]
                    .add(selector.mul(lift(link.tag).add(tuple_value(tuple, openings, &powers))));
            }
        }
        let d = [
            chi.sub(values[0]),
            chi.sub(values[1]),
            chi.sub(values[2]),
            chi.sub(values[3]),
        ];
        let a = d[0].mul(d[1]);
        let b = d[2].mul(d[3]);
        let p = weights[0].mul(d[1]).add(weights[1].mul(d[0]));
        let c = weights[2].mul(d[3]).add(weights[3].mul(d[2]));
        selectors
            .copy_active()
            .mul(a.mul(h1_z.mul(b).add(c)).sub(b.mul(p)))
    }

    #[test]
    fn compiled_constants_match_the_pinned_host_registry_and_every_endpoint() {
        let registry = build_atomic_state_only_registry_v3().unwrap();
        assert_eq!(
            atomic_state_only_registry_fingerprint_v3(&registry).unwrap(),
            constants::COMPILED_ATOMIC_REGISTRY_FINGERPRINT
        );
        assert_eq!(
            registry.links.len(),
            constants::COMPILED_ATOMIC_COPY_LINKS.len()
        );
        let mut producer_arity = [0u8; TRACE_ROWS];
        let mut consumer_arity = [0u8; TRACE_ROWS];
        for (host, compiled) in registry
            .links
            .into_iter()
            .zip(constants::COMPILED_ATOMIC_COPY_LINKS)
        {
            assert_eq!(host.tag.0, compiled.tag);
            for (tuple, endpoint, arity) in [
                (host.producer, compiled.producer, &mut producer_arity),
                (host.consumer, compiled.consumer, &mut consumer_arity),
            ] {
                assert_eq!(endpoint.row, tuple.row);
                assert_eq!(endpoint.slot, arity[usize::from(tuple.row)]);
                arity[usize::from(tuple.row)] += 1;
                assert_eq!(endpoint.pattern, pattern_id(tuple));
            }
        }
    }

    #[test]
    fn six_rectangle_active_selector_and_inactive_masks_match_all_1024_rows() {
        let active = constants::COMPILED_ATOMIC_COPY_ACTIVE_ROWS;
        let masks = atomic_state_only_copy_inactive_row_masks_v3();
        let indicator = atomic_state_only_copy_inactive_indicator_v3();
        for row in 0..TRACE_ROWS {
            let is_active = active.binary_search(&(row as u16)).is_ok();
            assert_eq!(masks[row >> 4] & (1 << (row & 15)) == 0, is_active);
            assert_eq!(indicator[row] == QM31::ZERO, is_active);
        }
        let mut fingerprint = 0xcbf2_9ce4_8422_2325u64;
        for row in active {
            for byte in row.to_le_bytes() {
                fingerprint ^= u64::from(byte);
                fingerprint = fingerprint.wrapping_mul(0x0000_0100_0000_01b3);
            }
        }
        assert_eq!(
            fingerprint,
            PINNED_ATOMIC_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT_V3
        );

        let mut rng = Rng(0x4154_4f4d_4943_4143);
        for _ in 0..64 {
            let point = core::array::from_fn(|_| rng.qm31());
            let selectors = AtomicSelectors::at_point(&point);
            let direct = active.into_iter().fold(QM31::ZERO, |sum, row| {
                sum.add(selectors.row(usize::from(row)))
            });
            assert_eq!(selectors.copy_active(), direct);
        }
    }

    #[test]
    fn shared_semantic_tensor_is_exactly_the_legacy_routing_partition() {
        let mut rng = Rng(0x4154_4f4d_5345_4c53);
        for _ in 0..64 {
            let point = core::array::from_fn(|_| rng.qm31());
            let semantic = AtomicSemanticSelectors::at_point(&point);
            let routing = LegacyAtomicSelectors::at_point(&point);
            assert_eq!(semantic.high, routing.high,);
            assert_eq!(semantic.low, routing.low,);
        }
    }

    #[test]
    fn sparse_atomic_initial_sums_match_dense_zero_weight_reference() {
        let check = |point: [QM31; 10]| {
            let selectors = AtomicSemanticSelectors::at_point(&point);
            let dense_highs: [QM31; 24] = state_constants::INITIAL_BLOCKS.map(|(row, _, _)| {
                let block = usize::from(row) >> 4;
                if (4..=43).contains(&block) {
                    QM31::ZERO
                } else {
                    selectors.high[block]
                }
            });
            let expected = (
                dense_highs.iter().copied().fold(QM31::ZERO, QM31::add),
                qm31_m31_dot(
                    &dense_highs,
                    &state_constants::INITIAL_BLOCKS.map(|(_, domain, _)| M31(domain)),
                ),
                qm31_m31_dot(
                    &dense_highs,
                    &state_constants::INITIAL_BLOCKS.map(|(_, _, length)| M31(length)),
                ),
            );
            assert_eq!(atomic_retained_initial_sums(&selectors), expected);
        };
        check([QM31::ZERO; 10]);
        check([QM31::ONE; 10]);
        let mut rng = Rng(0x4154_4f4d_494e_4954);
        for _ in 0..64 {
            check(core::array::from_fn(|_| rng.qm31()));
        }
    }

    #[test]
    fn sparse_legacy_active_selector_matches_scanning_reference() {
        let check = |point: [QM31; 10]| {
            let selectors = LegacyAtomicSelectors::at_point(&point);
            assert_eq!(
                selectors.high.iter().copied().fold(QM31::ZERO, QM31::add),
                QM31::ONE,
            );
            assert_eq!(
                selectors.low.iter().copied().fold(QM31::ZERO, QM31::add),
                QM31::ONE,
            );
            assert_eq!(
                selectors.copy_active(),
                legacy_copy_active_scanning_reference(&selectors),
            );
        };
        check([QM31::ZERO; 10]);
        check([QM31::ONE; 10]);
        let maximal = QM31 {
            c0: CM31::new(M31(P - 1), M31(P - 1)),
            c1: CM31::new(M31(P - 1), M31(P - 1)),
        };
        check([maximal; 10]);
        check(core::array::from_fn(|index| {
            if index & 1 == 0 {
                QM31::ONE
            } else {
                maximal
            }
        }));
        let mut rng = Rng(0x4154_4f4d_4143_5449);
        for _ in 0..64 {
            check(core::array::from_fn(|_| rng.qm31()));
        }
    }

    #[test]
    fn routing_linear_form_sparse_coefficients_match_reference() {
        fn check(factors: &[(u16, u8)], entries: &[(u8, u32)], selectors: &[QM31]) {
            for &(start, len) in factors {
                let start = usize::from(start);
                let entries = &entries[start..start + usize::from(len)];
                assert_eq!(
                    routing_linear_form(entries, selectors),
                    routing_linear_form_reference(entries, selectors),
                );
                assert_eq!(
                    routing_linear_form(entries, selectors),
                    routing_linear_form_four_entry_reference(entries, selectors),
                );
            }
        }

        let check_point = |point: [QM31; 10]| {
            let rank_74 = AtomicSelectors::at_point(&point);
            check(
                &constants::ATOMIC_COPY_ROUTING_LEFT_FACTORS,
                &constants::ATOMIC_COPY_ROUTING_ENTRIES,
                &rank_74.high,
            );
            check(
                &constants::ATOMIC_COPY_ROUTING_RIGHT_FACTORS,
                &constants::ATOMIC_COPY_ROUTING_ENTRIES,
                &rank_74.low,
            );
            let rank_103 = LegacyAtomicSelectors::at_point(&point);
            check(
                &legacy_partition_constants::ATOMIC_COPY_ROUTING_LEFT_FACTORS,
                &legacy_partition_constants::ATOMIC_COPY_ROUTING_ENTRIES,
                &rank_103.high,
            );
            check(
                &legacy_partition_constants::ATOMIC_COPY_ROUTING_RIGHT_FACTORS,
                &legacy_partition_constants::ATOMIC_COPY_ROUTING_ENTRIES,
                &rank_103.low,
            );
        };
        check_point([QM31::ZERO; 10]);
        check_point([QM31::ONE; 10]);

        let maximal = QM31 {
            c0: CM31::new(M31(P - 1), M31(P - 1)),
            c1: CM31::new(M31(P - 1), M31(P - 1)),
        };
        let alternating = QM31 {
            c0: CM31::new(M31(P - 1), M31::ZERO),
            c1: CM31::new(M31::ONE, M31(P - 2)),
        };
        for selectors in [[maximal; 64], [alternating; 64]] {
            check(
                &constants::ATOMIC_COPY_ROUTING_LEFT_FACTORS,
                &constants::ATOMIC_COPY_ROUTING_ENTRIES,
                &selectors,
            );
            check(
                &legacy_partition_constants::ATOMIC_COPY_ROUTING_LEFT_FACTORS,
                &legacy_partition_constants::ATOMIC_COPY_ROUTING_ENTRIES,
                &selectors,
            );
        }
        for selectors in [[maximal; 16], [alternating; 16]] {
            check(
                &constants::ATOMIC_COPY_ROUTING_RIGHT_FACTORS,
                &constants::ATOMIC_COPY_ROUTING_ENTRIES,
                &selectors,
            );
            check(
                &legacy_partition_constants::ATOMIC_COPY_ROUTING_RIGHT_FACTORS,
                &legacy_partition_constants::ATOMIC_COPY_ROUTING_ENTRIES,
                &selectors,
            );
        }

        let mut rng = Rng(0x4154_4f4d_5350_4152);
        for _ in 0..64 {
            check_point(core::array::from_fn(|_| rng.qm31()));
        }
    }

    #[test]
    fn prepared_lambda_power_chain_matches_direct_multiplication() {
        let check = |lambda: QM31| {
            let prepared = PreparedQm31Multiplier::new(lambda);
            let mut optimized = [QM31::ZERO; 16];
            let mut reference = [QM31::ZERO; 16];
            optimized[0] = lambda;
            reference[0] = lambda;
            for index in 1..optimized.len() {
                optimized[index] = prepared.mul(optimized[index - 1]);
                reference[index] = reference[index - 1].mul(lambda);
            }
            assert_eq!(optimized, reference);
        };
        check(QM31::ZERO);
        check(QM31::ONE);
        check(QM31::ONE.neg());
        let mut rng = Rng(0x4154_4f4d_4c41_4d42);
        for _ in 0..64 {
            check(rng.qm31());
        }
    }

    #[test]
    fn rank_74_routing_matches_the_183_link_walk_at_random_qm31_points() {
        let mut rng = Rng(0x4154_4f4d_5241_4e4b);
        for _ in 0..64 {
            let point = core::array::from_fn(|_| rng.qm31());
            let selectors = AtomicSelectors::at_point(&point);
            assert_eq!(
                evaluate_atomic_copy_routing(&selectors),
                evaluate_routing_direct(&selectors)
            );
        }
    }

    #[test]
    fn five_dot_atomic_patterns_match_all_fifteen_generated_affine_shapes() {
        let mut rng = Rng(0x4154_4f4d_5041_5454);
        for _ in 0..64 {
            let openings = core::array::from_fn(|_| rng.qm31());
            let lambda = rng.qm31();
            let mut powers = [QM31::ZERO; 16];
            powers[0] = lambda;
            for index in 1..powers.len() {
                powers[index] = powers[index - 1].mul(lambda);
            }
            assert_eq!(
                atomic_copy_pattern_values(&openings, &powers),
                atomic_copy_pattern_values_generated_reference(&openings, &powers),
            );
        }
    }

    #[test]
    fn diagnostic_terminal_is_the_same_polynomial_at_random_qm31_points() {
        let mut rng = Rng(0x4154_4f4d_4449_4147);
        let statement = AtomicPaymentStatementV4 {
            pool: [0x5a; 32],
            sequence: 73,
            spend: SpendPublic {
                anchor: core::array::from_fn(|_| rng.m31()),
                nullifier: core::array::from_fn(|_| rng.m31()),
                output_commitment: core::array::from_fn(|_| rng.m31()),
                asset_id: rng.m31(),
                fee: 1,
            },
            output_anchor: core::array::from_fn(|_| rng.m31()),
            deployment_domain: [0x5d; 32],
        };
        for _ in 0..64 {
            let claims = core::array::from_fn(|_| rng.qm31());
            let point = core::array::from_fn(|_| rng.qm31());
            let zerocheck_point = core::array::from_fn(|_| rng.qm31());
            let lambda = rng.qm31();
            let chi = rng.qm31();
            let theta = rng.qm31();
            let mu = rng.qm31();
            let eta = rng.qm31();
            let expected = atomic_state_only_selected_masked_terminal_value_compiled_v3(
                &statement,
                &claims,
                &point,
                lambda,
                chi,
                theta,
                &zerocheck_point,
                mu,
                eta,
            )
            .unwrap();
            let mut phases = Vec::new();
            let actual =
                atomic_state_only_selected_masked_terminal_value_compiled_with_diagnostic_trace_v3(
                    &statement,
                    &claims,
                    &point,
                    lambda,
                    chi,
                    theta,
                    &zerocheck_point,
                    mu,
                    eta,
                    |phase| phases.push(phase),
                )
                .unwrap();
            assert_eq!(actual, expected);
            assert_eq!(
                phases,
                vec![
                    StateOnlyTerminalDiagnosticPhase::Prepared,
                    StateOnlyTerminalDiagnosticPhase::Poseidon,
                    StateOnlyTerminalDiagnosticPhase::SemanticInitial,
                    StateOnlyTerminalDiagnosticPhase::SemanticAbsorption,
                    StateOnlyTerminalDiagnosticPhase::SemanticMerkle,
                    StateOnlyTerminalDiagnosticPhase::SemanticRange,
                    StateOnlyTerminalDiagnosticPhase::SemanticPublic,
                    StateOnlyTerminalDiagnosticPhase::CopyPatterns,
                    StateOnlyTerminalDiagnosticPhase::CopyRouting,
                    StateOnlyTerminalDiagnosticPhase::Copy,
                    StateOnlyTerminalDiagnosticPhase::CompositionEquality,
                    StateOnlyTerminalDiagnosticPhase::Mask,
                    StateOnlyTerminalDiagnosticPhase::Final,
                ]
            );
        }
    }

    #[test]
    fn zero_theta_and_mu_remove_every_h1_sumcheck_contribution() {
        let mut rng = Rng(0x4831_5a45_524f_4d55);
        let statement = AtomicPaymentStatementV4 {
            pool: [0x5a; 32],
            sequence: 73,
            spend: SpendPublic {
                anchor: core::array::from_fn(|_| rng.m31()),
                nullifier: core::array::from_fn(|_| rng.m31()),
                output_commitment: core::array::from_fn(|_| rng.m31()),
                asset_id: rng.m31(),
                fee: 1,
            },
            output_anchor: core::array::from_fn(|_| rng.m31()),
            deployment_domain: [0x5d; 32],
        };
        for _ in 0..64 {
            let claims = core::array::from_fn(|_| rng.qm31());
            let mut changed = claims;
            changed[ATOMIC_SELECTED_H1_COLUMN] = rng.qm31();
            let point = core::array::from_fn(|_| rng.qm31());
            let zerocheck_point = core::array::from_fn(|_| rng.qm31());
            let lambda = rng.qm31();
            let chi = rng.qm31();
            let left = atomic_state_only_selected_unmasked_terminal_value_compiled_v3(
                &statement,
                &claims,
                &point,
                lambda,
                chi,
                QM31::ZERO,
                &zerocheck_point,
                QM31::ZERO,
            )
            .unwrap();
            let right = atomic_state_only_selected_unmasked_terminal_value_compiled_v3(
                &statement,
                &changed,
                &point,
                lambda,
                chi,
                QM31::ZERO,
                &zerocheck_point,
                QM31::ZERO,
            )
            .unwrap();
            assert_eq!(left, right);
        }
    }

    #[test]
    fn compiled_copy_lane_matches_direct_off_domain_and_all_opening_teeth() {
        let mut rng = Rng(0x4154_4f4d_5445_4554);
        for _ in 0..64 {
            let openings = core::array::from_fn(|_| rng.qm31());
            let h1 = rng.qm31();
            let point = core::array::from_fn(|_| rng.qm31());
            let lambda = rng.qm31();
            let chi = rng.qm31();
            let selectors = AtomicSelectors::at_point(&point);
            assert_eq!(
                atomic_copy_lane_from_routing(&openings, h1, &selectors, lambda, chi),
                copy_lane_direct(&openings, h1, &selectors, lambda, chi)
            );
            assert_eq!(
                atomic_state_only_copy_terminal_lane_compiled_v3(
                    &openings, h1, &point, lambda, chi,
                ),
                atomic_state_only_copy_terminal_lane_legacy_partition_v3(
                    &openings, h1, &point, lambda, chi,
                ),
                "row-bit partition must not change the copy polynomial",
            );
        }

        let base = core::array::from_fn(|_| rng.qm31());
        let h1 = rng.qm31();
        let point = core::array::from_fn(|_| rng.qm31());
        let lambda = rng.qm31();
        let chi = rng.qm31();
        let selectors = AtomicSelectors::at_point(&point);
        for column in 0..C1_COLUMNS {
            let mut changed = base;
            changed[column] = changed[column].add(QM31::ONE);
            assert_eq!(
                atomic_copy_lane_from_routing(&changed, h1, &selectors, lambda, chi),
                copy_lane_direct(&changed, h1, &selectors, lambda, chi),
                "C1 corruption tooth {column}"
            );
        }
        for (changed_h1, changed_lambda, changed_chi) in [
            (h1.add(QM31::ONE), lambda, chi),
            (h1, lambda.add(QM31::ONE), chi),
            (h1, lambda, chi.add(QM31::ONE)),
        ] {
            assert_eq!(
                atomic_copy_lane_from_routing(
                    &base,
                    changed_h1,
                    &selectors,
                    changed_lambda,
                    changed_chi,
                ),
                copy_lane_direct(&base, changed_h1, &selectors, changed_lambda, changed_chi,)
            );
        }
    }

    /// Soundness-grade Schwartz-Zippel equivalence checker.
    ///
    /// Every existing equivalence test in this module fixes ~64 random QM31
    /// draws and asserts the compiled point-form evaluator equals an
    /// independent row-form reference.  This test upgrades that regression
    /// witness into a machine-verified polynomial-identity check.
    ///
    /// The soundness statement the on-chain verifier relies on quantifies over
    /// ADVERSARIAL openings: the prover's claimed statement evaluations (the
    /// `claims`/`openings`/`h1` cells) may be any element of QM31, not the
    /// values an honest trace would produce.  We therefore fill the entire
    /// opening space with independent uniform-random QM31 (never an honest
    /// fixture) and independently randomize every challenge (lambda, chi,
    /// theta, mu, eta) and both evaluation points (`point`, `zerocheck_point`),
    /// then assert
    ///
    ///     point_form(random_openings, random_challenges)
    ///         == row_form_MLE(random_openings, random_challenges)
    ///
    /// for each evaluator family.  Both sides are polynomials of bounded total
    /// degree `D` over K = QM31 with |K| = P^4 ~ 2^124.  By Schwartz-Zippel, if
    /// the two sides were NOT the identical polynomial they would agree at a
    /// single uniform-random point except with probability <= D/|K|; over `T`
    /// independent points the escape probability is <= (D/|K|)^T.
    ///
    /// The evaluators are fixed, frozen production code chosen independently of
    /// the PRNG seed, so the deterministic xorshift stream (pinned constants,
    /// per the workspace no-entropy rule) is an adequate stand-in for uniform
    /// QM31: a fixed discrepancy cannot be crafted to dodge a seed it never
    /// saw, and the per-point margin (2^-116 or better) dwarfs any bias in the
    /// stream.  `T` distinct points give defense-in-depth on top of that.
    #[test]
    fn point_form_equals_row_form_at_soundness_grade_over_adversarial_openings() {
        // Trials per family.  A single trial already drives every family's
        // escape probability below 2^-100 (see per-family D below); T = 1024
        // independent points is generous margin, not necessity.
        const T: u32 = 1024;

        // |K| = |QM31| = P^4, with P = 2^31 - 1.
        let p = u128::from(P);
        let field_size = p * p * p * p; // ~2.1268e37 ~ 2^123.9999999.
        let log2_k = 4.0 * f64::from(P).log2();

        // Report one family's Schwartz-Zippel accounting and return the final
        // (D/|K|)^T escape bound as a base-2 exponent.
        let report = |name: &str, degree: u128| -> f64 {
            let per_trial_log2 = (degree as f64).log2() - log2_k;
            let final_log2 = per_trial_log2 * f64::from(T);
            std::println!(
                "  [{name}] D = {degree}, D/|K| = {degree}/{field_size} <= 2^{per_trial_log2:.2}, \
                 T = {T}, (D/|K|)^T <= 2^{final_log2:.1}",
            );
            // Guard the headline claim: one trial must already beat 2^-100.
            assert!(
                per_trial_log2 <= -100.0,
                "family {name}: single-trial bound 2^{per_trial_log2:.2} does not reach 2^-100",
            );
            assert!(
                final_log2 <= -100.0,
                "family {name}: T-trial bound 2^{final_log2:.1} does not reach 2^-100",
            );
            final_log2
        };

        std::println!(
            "Schwartz-Zippel equivalence over K = QM31, |K| = P^4 = {field_size} (~2^{log2_k:.4}); \
             {T} independent adversarial-opening trials per family:"
        );

        // --- Family A: rank-74 routing point-form == 183-link direct row walk.
        // Variables: point (10 QM31 coords).  Both sides are linear
        // combinations of the multilinear selector tensor, whose monomials have
        // total degree <= 10 in the point coordinates.  D_A = 10.
        {
            const D: u128 = 10;
            let mut rng = Rng(0x5344_5f52_4f55_5441); // "SD_ROUTA"
            let mut first: Option<Vec<QM31>> = None;
            let mut saw_variation = false;
            for _ in 0..T {
                let point = core::array::from_fn(|_| rng.qm31());
                let selectors = AtomicSelectors::at_point(&point);
                let point_form = evaluate_atomic_copy_routing(&selectors);
                let row_form = evaluate_routing_direct(&selectors);
                assert_eq!(point_form, row_form.to_vec());
                match &first {
                    None => first = Some(point_form.clone()),
                    Some(f) => saw_variation |= *f != point_form,
                }
            }
            assert!(
                saw_variation,
                "family A appears constant; identity is vacuous"
            );
            report("A rank-74 routing == 183-link direct walk", D);
        }

        // --- Family B: copy/LogUp lane point-form == direct registry row-walk.
        // This is the central point-form == row-form-MLE identity with FREE
        // adversarial openings.  `copy_lane_direct` rebuilds the host registry
        // and sums selector(row) * per-link residual over all 183 links, then
        // forms the cleared LogUp rational; `atomic_copy_lane_from_routing`
        // evaluates the compiled rank-74 factoring of the same object.
        // Variables: openings (16), h1, point (10), lambda, chi.
        // Degree bound: pattern values are deg 1 in openings times lambda^<=16
        // (deg <= 17); routing/selector factors are deg <= 10 in point; the
        // cleared LogUp numerator multiplies two degree-(<=54) denominators
        // against a degree-(<=55) factor, times the degree-<=10 active
        // selector, giving total degree <= 119.  D_B = 119.
        {
            const D: u128 = 119;
            let mut rng = Rng(0x5344_5f43_4f50_594c); // "SD_COPYL"
            let mut first: Option<QM31> = None;
            let mut saw_variation = false;
            for _ in 0..T {
                let openings = core::array::from_fn(|_| rng.qm31());
                let h1 = rng.qm31();
                let point = core::array::from_fn(|_| rng.qm31());
                let lambda = rng.qm31();
                let chi = rng.qm31();
                let selectors = AtomicSelectors::at_point(&point);
                let point_form =
                    atomic_copy_lane_from_routing(&openings, h1, &selectors, lambda, chi);
                let row_form = copy_lane_direct(&openings, h1, &selectors, lambda, chi);
                assert_eq!(point_form, row_form);
                match first {
                    None => first = Some(point_form),
                    Some(f) => saw_variation |= f != point_form,
                }
            }
            assert!(
                saw_variation,
                "family B appears constant; identity is vacuous"
            );
            report("B copy/LogUp lane point-form == registry row-walk MLE", D);
        }

        // --- Family C: rank-74 partition == rank-103 legacy partition.
        // Same copy polynomial evaluated through two independent selector
        // partitions of the 1024 rows.  Same variables and degree as family B.
        {
            const D: u128 = 119;
            let mut rng = Rng(0x5344_5f50_4152_5449); // "SD_PARTI"
            let mut first: Option<QM31> = None;
            let mut saw_variation = false;
            for _ in 0..T {
                let openings = core::array::from_fn(|_| rng.qm31());
                let h1 = rng.qm31();
                let point = core::array::from_fn(|_| rng.qm31());
                let lambda = rng.qm31();
                let chi = rng.qm31();
                let compiled = atomic_state_only_copy_terminal_lane_compiled_v3(
                    &openings, h1, &point, lambda, chi,
                );
                let legacy = atomic_state_only_copy_terminal_lane_legacy_partition_v3(
                    &openings, h1, &point, lambda, chi,
                );
                assert_eq!(compiled, legacy);
                match first {
                    None => first = Some(compiled),
                    Some(f) => saw_variation |= f != compiled,
                }
            }
            assert!(
                saw_variation,
                "family C appears constant; identity is vacuous"
            );
            report("C rank-74 partition == rank-103 legacy partition", D);
        }

        // --- Family D: five-dot pattern compression == 15 generated affine
        // shapes.  Variables: openings (16), lambda.  Openings appear linearly;
        // powers span lambda^1..lambda^16, and the highest shape multiplies a
        // lambda^8 factor into a term already carrying lambda^8 * opening, so
        // total degree <= 17.  D_D = 17.
        {
            const D: u128 = 17;
            let mut rng = Rng(0x5344_5f50_4154_5442); // "SD_PATTB"
            let mut first: Option<[QM31; ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS]> = None;
            let mut saw_variation = false;
            for _ in 0..T {
                let openings = core::array::from_fn(|_| rng.qm31());
                let lambda = rng.qm31();
                let mut powers = [QM31::ZERO; 16];
                powers[0] = lambda;
                for index in 1..powers.len() {
                    powers[index] = powers[index - 1].mul(lambda);
                }
                let point_form = atomic_copy_pattern_values(&openings, &powers);
                let row_form = atomic_copy_pattern_values_generated_reference(&openings, &powers);
                assert_eq!(point_form, row_form);
                match &first {
                    None => first = Some(point_form),
                    Some(f) => saw_variation |= *f != point_form,
                }
            }
            assert!(
                saw_variation,
                "family D appears constant; identity is vacuous"
            );
            report("D five-dot pattern == 15 generated affine shapes", D);
        }

        // --- Family E: shared semantic selector tensor == legacy routing
        // selector tensor.  Variables: point (10).  Both are the multilinear
        // selector tensor, total degree <= 10.  D_E = 10.
        {
            const D: u128 = 10;
            let mut rng = Rng(0x5344_5f54_454e_534f); // "SD_TENSO"
            let mut first: Option<([QM31; 64], [QM31; 16])> = None;
            let mut saw_variation = false;
            for _ in 0..T {
                let point = core::array::from_fn(|_| rng.qm31());
                let semantic = AtomicSemanticSelectors::at_point(&point);
                let routing = LegacyAtomicSelectors::at_point(&point);
                assert_eq!(semantic.high, routing.high);
                assert_eq!(semantic.low, routing.low);
                match &first {
                    None => first = Some((semantic.high, semantic.low)),
                    Some((h, l)) => {
                        saw_variation |= *h != semantic.high || *l != semantic.low;
                    }
                }
            }
            assert!(
                saw_variation,
                "family E appears constant; identity is vacuous"
            );
            report("E semantic tensor == legacy routing tensor", D);
        }

        // --- Family F: full masked terminal == diagnostic-trace duplicate.
        // This is the EXACT composition the on-chain verifier evaluates
        // (state_only_spend.rs::verify_terminal calls
        // atomic_state_only_selected_masked_terminal_value_compiled_v3).  We
        // drive it with 84 free adversarial claim cells plus fully random
        // challenges/points and a random statement.  Both callees are point-
        // form; this is a refactor identity (production == its line-by-line
        // diagnostic-traced duplicate), NOT an independent row-form derivation
        // for the poseidon/semantic lanes (see the report caveats).
        //
        // Degree bound: the copy lane (<=119) is folded through 24 theta lanes
        // (theta^24 * copy => <=143); the outer zerocheck equality is degree
        // <=20 (10 in point, 10 in zerocheck_point), giving original <=163;
        // eta * original plus the mask keeps the whole terminal <=164.  We use
        // a conservative D_F = 200 (>= 164).  Even at 200, D/|K| <= 2^-116.
        {
            const D: u128 = 200;
            let mut rng = Rng(0x5344_5f54_4552_4d46); // "SD_TERMF"
            let mut first: Option<QM31> = None;
            let mut saw_variation = false;
            for _ in 0..T {
                let statement = AtomicPaymentStatementV4 {
                    pool: [0x5a; 32],
                    sequence: 73,
                    spend: SpendPublic {
                        anchor: core::array::from_fn(|_| rng.m31()),
                        nullifier: core::array::from_fn(|_| rng.m31()),
                        output_commitment: core::array::from_fn(|_| rng.m31()),
                        asset_id: rng.m31(),
                        // fee is a public constant in the residuals; keep it in
                        // the valid range so the evaluator does not early-return.
                        fee: (rng.next() % u64::from(crate::spend::VALUE_LIMIT)) as u32,
                    },
                    output_anchor: core::array::from_fn(|_| rng.m31()),
                    deployment_domain: [0x5d; 32],
                };
                let claims = core::array::from_fn(|_| rng.qm31());
                let point = core::array::from_fn(|_| rng.qm31());
                let zerocheck_point = core::array::from_fn(|_| rng.qm31());
                let lambda = rng.qm31();
                let chi = rng.qm31();
                let theta = rng.qm31();
                let mu = rng.qm31();
                let eta = rng.qm31();
                let production = atomic_state_only_selected_masked_terminal_value_compiled_v3(
                    &statement,
                    &claims,
                    &point,
                    lambda,
                    chi,
                    theta,
                    &zerocheck_point,
                    mu,
                    eta,
                )
                .unwrap();
                let diagnostic =
                    atomic_state_only_selected_masked_terminal_value_compiled_with_diagnostic_trace_v3(
                        &statement,
                        &claims,
                        &point,
                        lambda,
                        chi,
                        theta,
                        &zerocheck_point,
                        mu,
                        eta,
                        |_| {},
                    )
                    .unwrap();
                assert_eq!(production, diagnostic);
                match first {
                    None => first = Some(production),
                    Some(f) => saw_variation |= f != production,
                }
            }
            assert!(
                saw_variation,
                "family F appears constant; identity is vacuous"
            );
            report(
                "F masked terminal == diagnostic-trace duplicate (full verifier composition)",
                D,
            );
        }
    }
}
