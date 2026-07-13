//! SBF-safe terminal evaluator for the frozen 29-lane state-only registry.
//!
//! All layout data is checked in as generated constants and this module never
//! calls the host trace/layout builders. The exact inactive-row relation
//! selector is materialized only when constructing the PCS claim.

#[cfg(test)]
use alloc::vec;
use alloc::vec::Vec;

use aspis_core::field::{
    qm31_dot, qm31_m31_dot, qm31_pack_base4, PreparedQm31Multiplier, CM31, M31, QM31,
};
use aspis_core::state_only_hiding::{
    state_only_mask_value, state_only_selected_mask_value, STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS,
};

use crate::poseidon2::{DIGEST_ELEMS, RATE};
use crate::spend::{SpendPublic, VALUE_LIMIT};
use crate::state_only_poseidon::{
    evaluate_state_only_poseidon_oracle_projected, StateOnlyPoseidonOpenings,
    StateOnlyPoseidonSelectors,
};

pub const STATE_ONLY_TERMINAL_COLUMNS: usize = 18;
pub const STATE_ONLY_TERMINAL_POINTS: usize = 3;
pub const STATE_ONLY_TERMINAL_CLAIMS: usize =
    STATE_ONLY_TERMINAL_COLUMNS * STATE_ONLY_TERMINAL_POINTS;
pub const STATE_ONLY_TERMINAL_RANDOMIZED_LANES: usize = 29;
pub const STATE_ONLY_TERMINAL_LAYOUT_FINGERPRINT: u64 = 0x121d_b4ec_14af_2130;
pub const STATE_ONLY_SELECTED_TERMINAL_COLUMNS: usize =
    C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + 2;
pub const STATE_ONLY_SELECTED_TERMINAL_CLAIMS: usize =
    STATE_ONLY_SELECTED_TERMINAL_COLUMNS * STATE_ONLY_TERMINAL_POINTS;

const C1_COLUMNS: usize = 16;
const H1_COLUMN: usize = 16;
const G_COLUMN: usize = 17;
const SELECTED_H1_COLUMN: usize = C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
const SELECTED_G_COLUMN: usize = SELECTED_H1_COLUMN + 1;
const PACKED_SEMANTIC_LANES: usize = 24;
const SOURCE_SEMANTIC_LANES: usize = 94;
const TRACE_ROWS: usize = 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyTerminalError {
    PublicFeeOutOfRange,
}

/// Diagnostic-only boundaries inside the exact width-28 terminal. They are
/// emitted by a separate read-only path so the authoritative terminal CU
/// measurement retains its original marker schedule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyTerminalDiagnosticPhase {
    Prepared,
    Poseidon,
    SemanticInitial,
    SemanticAbsorption,
    SemanticMerkle,
    SemanticRange,
    SemanticPublic,
    CopyPatterns,
    CopyRouting,
    Copy,
    CompositionEquality,
    Mask,
    Final,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StateOnlySemanticDiagnosticPhase {
    Initial,
    Absorption,
    Merkle,
    Range,
    Public,
}

#[derive(Clone, Copy)]
struct CompiledCopyEndpoint {
    row: u16,
    slot: u8,
    present: u16,
    columns: u64,
}

#[derive(Clone, Copy)]
struct CompiledCopyLink {
    tag: u32,
    producer: CompiledCopyEndpoint,
    consumer: CompiledCopyEndpoint,
}

pub(crate) mod constants {
    use super::{CompiledCopyEndpoint, CompiledCopyLink};
    include!("state_only_terminal_constants.rs");
}

pub const STATE_ONLY_COPY_ACTIVE_ROW_COUNT: usize = constants::COMPILED_COPY_ACTIVE_ROWS.len();
pub const PINNED_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT: u64 =
    constants::COMPILED_COPY_ACTIVE_ROWS_FINGERPRINT;

pub fn state_only_copy_active_rows_v4() -> &'static [u16; STATE_ONLY_COPY_ACTIVE_ROW_COUNT] {
    &constants::COMPILED_COPY_ACTIVE_ROWS
}

pub fn state_only_copy_inactive_row_masks_v4() -> [u16; 64] {
    let mut masks = [u16::MAX; 64];
    for &row in &constants::COMPILED_COPY_ACTIVE_ROWS {
        let row = usize::from(row);
        masks[row >> 4] &= !(1u16 << (row & 15));
    }
    masks
}

pub fn state_only_copy_inactive_indicator_v4() -> Vec<QM31> {
    state_only_copy_inactive_row_masks_v4()
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

    #[inline(always)]
    fn row(&self, row: usize) -> QM31 {
        debug_assert!(row < TRACE_ROWS);
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

    fn copy_active(&self) -> QM31 {
        constants::COMPILED_COPY_ACTIVE_FACTORS
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

#[inline(always)]
fn lift(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}

#[inline(always)]
fn claim(claims: &[QM31; STATE_ONLY_TERMINAL_CLAIMS], point: usize, column: usize) -> QM31 {
    claims[point * STATE_ONLY_TERMINAL_COLUMNS + column]
}

fn poseidon_openings(claims: &[QM31; STATE_ONLY_TERMINAL_CLAIMS]) -> StateOnlyPoseidonOpenings {
    StateOnlyPoseidonOpenings {
        z: core::array::from_fn(|column| claim(claims, 0, column)),
        succ_z: core::array::from_fn(|column| claim(claims, 1, column)),
        xor12_z: core::array::from_fn(|column| claim(claims, 2, column)),
    }
}

#[cfg(test)]
#[inline(never)]
fn semantic_packed_reference(
    public: &SpendPublic,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) -> [QM31; PACKED_SEMANTIC_LANES] {
    let mut source = [QM31::ZERO; SOURCE_SEMANTIC_LANES];

    for &(row, domain, length) in &constants::INITIAL_BLOCKS {
        let selector = selectors.row(usize::from(row));
        for lane in 0..16 {
            let expected = match lane {
                RATE => M31(domain),
                value if value == RATE + 1 => M31(length),
                _ => M31::ZERO,
            };
            source[lane] = source[lane].add(selector.mul(openings.z[lane].sub(lift(expected))));
        }
    }

    for (block, &mask) in constants::ABSORPTION_ZERO_MASKS.iter().enumerate() {
        let selector = selectors.row(block * 16 + 12);
        for lane in 0..16 {
            if mask & (1 << lane) != 0 {
                source[16 + lane] = source[16 + lane].add(selector.mul(openings.z[lane]));
            }
        }
    }

    let merkle_high = selectors.high[49..54]
        .iter()
        .copied()
        .fold(QM31::ZERO, QM31::add);
    let merkle_low = [0usize, 2, 4, 6]
        .into_iter()
        .fold(QM31::ZERO, |sum, local| sum.add(selectors.low[local]));
    let merkle_selector = merkle_high.mul(merkle_low);
    let bit = openings.z[0];
    source[32] = merkle_selector.mul(bit.mul(bit.sub(QM31::ONE)));
    for limb in 0..DIGEST_ELEMS {
        let current = openings.z[1 + limb];
        let sibling = openings.xor12_z[limb];
        let delta = sibling.sub(current);
        source[33 + limb] =
            merkle_selector.mul(openings.succ_z[limb].sub(current.add(bit.mul(delta))));
        source[33 + DIGEST_ELEMS + limb] =
            merkle_selector.mul(openings.succ_z[RATE + limb].sub(sibling.sub(bit.mul(delta))));
    }

    let range_selectors = [selectors.row(864), selectors.row(866)];
    let range_selector = range_selectors[0].add(range_selectors[1]);
    for (view_index, view) in [&openings.z, &openings.succ_z, &openings.xor12_z]
        .into_iter()
        .enumerate()
    {
        for bit_index in 0..10 {
            source[49 + view_index * 10 + bit_index] =
                range_selector.mul(view[bit_index].mul(view[bit_index].sub(QM31::ONE)));
        }
        let reconstructed = (0..10).fold(QM31::ZERO, |sum, bit_index| {
            sum.add(view[bit_index].mul_m31(M31(1 << bit_index)))
        });
        source[49 + 30 + view_index] = range_selector.mul(view[10].sub(reconstructed));
    }

    let triple = |activation: QM31| {
        activation.mul(
            openings.z[10]
                .add(openings.succ_z[10].mul_m31(M31(1 << 10)))
                .add(openings.xor12_z[10].mul_m31(M31(1 << 20))),
        )
    };
    let input_total = range_selectors[0].mul(openings.z[11]);
    let output_total = range_selectors[1].mul(openings.z[11]);
    source[82] = input_total
        .sub(triple(range_selectors[0]))
        .add(output_total.sub(triple(range_selectors[1])));
    source[83] = range_selectors[0].mul(
        openings.z[11]
            .sub(openings.z[12])
            .sub(lift(M31(public.fee))),
    );

    for (block, digest) in [
        (43usize, &public.anchor),
        (45usize, &public.nullifier),
        (48usize, &public.output_commitment),
    ] {
        let selector = selectors.row(block * 16 + 11);
        for limb in 0..DIGEST_ELEMS {
            source[84 + limb] =
                source[84 + limb].add(selector.mul(openings.z[limb].sub(lift(digest[limb]))));
        }
    }

    for (lane, &(row, column)) in [constants::INPUT_ASSET_CELL, constants::OUTPUT_ASSET_CELL]
        .iter()
        .enumerate()
    {
        source[92 + lane] = selectors
            .row(usize::from(row))
            .mul(openings.z[usize::from(column)].sub(lift(public.asset_id)));
    }

    core::array::from_fn(|group| {
        let start = group * 4;
        let end = core::cmp::min(start + 4, source.len());
        qm31_pack_base4(&source[start..end])
    })
}

#[inline(always)]
fn accumulate_packed_run<const N: usize>(
    packed: &mut [QM31; PACKED_SEMANTIC_LANES],
    start: usize,
    values: &[QM31; N],
    selector: QM31,
) {
    debug_assert!(N != 0);
    debug_assert!(start + N <= SOURCE_SEMANTIC_LANES);
    let first_group = start / 4;
    let last_group = (start + N - 1) / 4;
    for group in first_group..=last_group {
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
fn add_preweighted_packed_run<const N: usize>(
    packed: &mut [QM31; PACKED_SEMANTIC_LANES],
    start: usize,
    values: &[QM31; N],
) {
    debug_assert!(N != 0);
    debug_assert!(start + N <= SOURCE_SEMANTIC_LANES);
    let first_group = start / 4;
    let last_group = (start + N - 1) / 4;
    for group in first_group..=last_group {
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

/// Direct-to-packed semantic evaluation. Packing is linear, so residuals
/// with a common row selector are packed first and multiplied by that
/// selector once per occupied four-lane group.
#[inline(never)]
fn semantic_packed_impl<F>(
    public: &SpendPublic,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
    mut trace: F,
) -> [QM31; PACKED_SEMANTIC_LANES]
where
    F: FnMut(StateOnlySemanticDiagnosticPhase),
{
    let mut packed = [QM31::ZERO; PACKED_SEMANTIC_LANES];

    let initial_highs: [QM31; 24] =
        constants::INITIAL_BLOCKS.map(|(row, _, _)| selectors.high[usize::from(row) >> 4]);
    let initial_high_sum = initial_highs.iter().copied().fold(QM31::ZERO, QM31::add);
    let initial_selector = selectors.low[0].mul(initial_high_sum);
    for group in 0..4 {
        packed[group] =
            initial_selector.mul(qm31_pack_base4(&openings.z[4 * group..4 * group + 4]));
    }
    let domain_sum = qm31_m31_dot(
        &initial_highs,
        &constants::INITIAL_BLOCKS.map(|(_, domain, _)| M31(domain)),
    );
    let length_sum = qm31_m31_dot(
        &initial_highs,
        &constants::INITIAL_BLOCKS.map(|(_, _, length)| M31(length)),
    );
    packed[2] = packed[2].sub(selectors.low[0].mul(qm31_pack_base4(&[
        domain_sum,
        length_sum,
        QM31::ZERO,
        QM31::ZERO,
    ])));
    trace(StateOnlySemanticDiagnosticPhase::Initial);

    for mask in [0x00fcu16, 0xff00, 0xfffc] {
        let high_sum = constants::ABSORPTION_ZERO_MASKS
            .iter()
            .copied()
            .enumerate()
            .filter(|(_, candidate)| *candidate == mask)
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
    trace(StateOnlySemanticDiagnosticPhase::Absorption);

    let merkle_selector = (0..20usize).fold(QM31::ZERO, |sum, level| {
        sum.add(selectors.row(784 + 16 * (level / 4) + 2 * (level % 4)))
    });
    let bit = openings.z[0];
    let merkle_residuals: [QM31; 17] = core::array::from_fn(|index| {
        if index == 0 {
            bit.mul(bit.sub(QM31::ONE))
        } else {
            let limb = (index - 1) % DIGEST_ELEMS;
            let current = openings.z[1 + limb];
            let sibling = openings.xor12_z[limb];
            let delta = sibling.sub(current);
            if index <= DIGEST_ELEMS {
                openings.succ_z[limb].sub(current.add(bit.mul(delta)))
            } else {
                openings.succ_z[RATE + limb].sub(sibling.sub(bit.mul(delta)))
            }
        }
    });
    accumulate_packed_run(&mut packed, 32, &merkle_residuals, merkle_selector);
    trace(StateOnlySemanticDiagnosticPhase::Merkle);

    let range_selectors = [selectors.row(864), selectors.row(866)];
    let range_selector = range_selectors[0].add(range_selectors[1]);
    let range_residuals: [QM31; 33] = core::array::from_fn(|index| {
        if index < 30 {
            let view_index = index / 10;
            let bit_index = index % 10;
            let view = match view_index {
                0 => &openings.z,
                1 => &openings.succ_z,
                _ => &openings.xor12_z,
            };
            view[bit_index].mul(view[bit_index].sub(QM31::ONE))
        } else {
            let view = match index - 30 {
                0 => &openings.z,
                1 => &openings.succ_z,
                _ => &openings.xor12_z,
            };
            let reconstructed = (0..10).fold(QM31::ZERO, |sum, bit_index| {
                sum.add(view[bit_index].mul_m31(M31(1 << bit_index)))
            });
            view[10].sub(reconstructed)
        }
    });
    accumulate_packed_run(&mut packed, 49, &range_residuals, range_selector);

    let triple_value = openings.z[10]
        .add(openings.succ_z[10].mul_m31(M31(1 << 10)))
        .add(openings.xor12_z[10].mul_m31(M31(1 << 20)));
    let totals = [
        range_selector.mul(openings.z[11].sub(triple_value)),
        range_selectors[0].mul(
            openings.z[11]
                .sub(openings.z[12])
                .sub(lift(M31(public.fee))),
        ),
    ];
    add_preweighted_packed_run(&mut packed, 82, &totals);
    trace(StateOnlySemanticDiagnosticPhase::Range);

    for (block, digest) in [
        (43usize, &public.anchor),
        (45usize, &public.nullifier),
        (48usize, &public.output_commitment),
    ] {
        let residuals: [QM31; DIGEST_ELEMS] =
            core::array::from_fn(|limb| openings.z[limb].sub(lift(digest[limb])));
        accumulate_packed_run(&mut packed, 84, &residuals, selectors.row(block * 16 + 11));
    }

    let assets: [QM31; 2] = core::array::from_fn(|lane| {
        let (row, column) = [constants::INPUT_ASSET_CELL, constants::OUTPUT_ASSET_CELL][lane];
        selectors
            .row(usize::from(row))
            .mul(openings.z[usize::from(column)].sub(lift(public.asset_id)))
    });
    add_preweighted_packed_run(&mut packed, 92, &assets);
    trace(StateOnlySemanticDiagnosticPhase::Public);
    packed
}

#[inline(never)]
fn semantic_packed(
    public: &SpendPublic,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) -> [QM31; PACKED_SEMANTIC_LANES] {
    semantic_packed_impl(public, openings, selectors, |_| {})
}

#[derive(Clone, Copy)]
struct CopyTerminal {
    producer_values: [QM31; 2],
    producer_weights: [QM31; 2],
    consumer_values: [QM31; 2],
    consumer_weights: [QM31; 2],
}

/// Compute each distinct compressed tuple once. The frozen 102-link layout
/// has 204 endpoints but only eleven `(present, columns)` patterns. Factoring
/// `s * (tag + sum lambda^j x_j)` before the endpoint walk is an exact field
/// identity at every off-domain point; it is not a Boolean-domain rewrite.
#[inline(never)]
fn copy_pattern_values(
    openings: &[QM31; C1_COLUMNS],
    powers: &[QM31; 16],
) -> [QM31; constants::COPY_PATTERNS.len()] {
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
    let lambda8 = powers[7];
    [
        powers[0].mul(openings[0]),
        powers[0].mul(openings[11]),
        powers[0].mul(openings[12]),
        d,
        a,
        c,
        b,
        a.add(lambda8.mul(d)),
        a.add(lambda8.mul(e)),
        a.add(lambda8.mul(b)),
        b.add(lambda8.mul(b)),
    ]
}

#[inline(always)]
fn copy_routing_linear_form(entries: &[(u8, u32)], selectors: &[QM31]) -> QM31 {
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
            for limb in 0..4 {
                raw[limb] += u64::from(limbs[limb]) * u64::from(coefficient);
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

/// Evaluate all four `(weight, tag, 11 pattern)` selector tables from the
/// generated rank-51 decomposition. Equal left/right factor pairs are shared,
/// so only 43 extension-field outer products remain. The 32 generated left
/// factors themselves span a 15-dimensional subspace; evaluating a
/// minimum-support basis and reconstructing the other seventeen factors cuts
/// their constant-dot scalar terms from 515 to 365.
#[inline(never)]
fn evaluate_copy_routing(selectors: &Selectors) -> [QM31; 4 * (2 + 11)] {
    let left_basis: [QM31; 15] = core::array::from_fn(|basis| {
        let index = usize::from(constants::COPY_ROUTING_LEFT_BASIS_FACTORS[basis]);
        let (start, len) = constants::COPY_ROUTING_LEFT_FACTORS[index];
        let start = usize::from(start);
        copy_routing_linear_form(
            &constants::COPY_ROUTING_ENTRIES[start..start + usize::from(len)],
            &selectors.high,
        )
    });
    let mut left_values = [QM31::ZERO; 32];
    for (basis, &index) in constants::COPY_ROUTING_LEFT_BASIS_FACTORS
        .iter()
        .enumerate()
    {
        left_values[usize::from(index)] = left_basis[basis];
    }
    for (index, &(start, len)) in constants::COPY_ROUTING_LEFT_RECONSTRUCTION_FACTORS
        .iter()
        .enumerate()
    {
        if len == 0 {
            continue;
        }
        let start = usize::from(start);
        left_values[index] = copy_routing_linear_form(
            &constants::COPY_ROUTING_LEFT_RECONSTRUCTION_ENTRIES[start..start + usize::from(len)],
            &left_basis,
        );
    }
    let right_values: [QM31; 28] = core::array::from_fn(|index| {
        let (start, len) = constants::COPY_ROUTING_RIGHT_FACTORS[index];
        let start = usize::from(start);
        copy_routing_linear_form(
            &constants::COPY_ROUTING_ENTRIES[start..start + usize::from(len)],
            &selectors.low,
        )
    });
    let mut matrices = [QM31::ZERO; 4 * (2 + 11)];
    for &(left, right, matrix_start, matrix_len) in &constants::COPY_ROUTING_PAIR_TERMS {
        let product = left_values[usize::from(left)].mul(right_values[usize::from(right)]);
        let start = usize::from(matrix_start);
        let end = start + usize::from(matrix_len);
        for &matrix in &constants::COPY_ROUTING_DESTINATIONS[start..end] {
            let matrix = usize::from(matrix);
            matrices[matrix] = matrices[matrix].add(product);
        }
    }
    matrices
}

#[cfg(test)]
fn evaluate_copy_routing_direct(selectors: &Selectors) -> [QM31; 4 * (2 + 11)] {
    let mut matrices = [QM31::ZERO; 4 * (2 + 11)];
    for link in &constants::COMPILED_COPY_LINKS {
        for (slot_offset, endpoint) in [(0usize, link.producer), (2usize, link.consumer)] {
            let slot = slot_offset + usize::from(endpoint.slot);
            let selector = selectors.row(usize::from(endpoint.row));
            let base = slot * (2 + constants::COPY_PATTERNS.len());
            matrices[base] = matrices[base].add(selector);
            matrices[base + 1] = matrices[base + 1].add(selector.mul_m31(M31(link.tag)));
            let pattern = constants::COPY_PATTERNS
                .iter()
                .position(|&(present, columns)| {
                    present == endpoint.present && columns == endpoint.columns
                })
                .unwrap();
            matrices[base + 2 + pattern] = matrices[base + 2 + pattern].add(selector);
        }
    }
    matrices
}

#[inline(never)]
fn copy_lane(
    openings: &[QM31; C1_COLUMNS],
    h1_z: QM31,
    selectors: &Selectors,
    lambda: QM31,
    chi: QM31,
) -> QM31 {
    copy_lane_impl(openings, h1_z, selectors, lambda, chi, |_| {})
}

#[inline(never)]
fn copy_lane_impl<F>(
    openings: &[QM31; C1_COLUMNS],
    h1_z: QM31,
    selectors: &Selectors,
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
    let pattern_values = copy_pattern_values(openings, &powers);
    trace(StateOnlyTerminalDiagnosticPhase::CopyPatterns);
    let routing = evaluate_copy_routing(selectors);
    trace(StateOnlyTerminalDiagnosticPhase::CopyRouting);
    let mut values = [QM31::ZERO; 4];
    let mut weights = [QM31::ZERO; 4];
    for slot in 0..4 {
        let base = slot * (2 + constants::COPY_PATTERNS.len());
        weights[slot] = routing[base];
        values[slot] = routing[base + 1];
        let mut support = constants::COPY_ROUTING_PATTERN_MASKS[slot];
        while support != 0 {
            let pattern = support.trailing_zeros() as usize;
            values[slot] =
                values[slot].add(routing[base + 2 + pattern].mul(pattern_values[pattern]));
            support &= support - 1;
        }
    }
    let row = CopyTerminal {
        producer_values: [values[0], values[1]],
        producer_weights: [weights[0], weights[1]],
        consumer_values: [values[2], values[3]],
        consumer_weights: [weights[2], weights[3]],
    };
    let d = [
        chi.sub(row.producer_values[0]),
        chi.sub(row.producer_values[1]),
        chi.sub(row.consumer_values[0]),
        chi.sub(row.consumer_values[1]),
    ];
    let a = d[0].mul(d[1]);
    let b = d[2].mul(d[3]);
    let p = row.producer_weights[0]
        .mul(d[1])
        .add(row.producer_weights[1].mul(d[0]));
    let c = row.consumer_weights[0]
        .mul(d[3])
        .add(row.consumer_weights[1].mul(d[2]));
    let output = selectors
        .copy_active()
        .mul(a.mul(h1_z.mul(b).add(c)).sub(b.mul(p)));
    trace(StateOnlyTerminalDiagnosticPhase::Copy);
    output
}

fn equality_value(left: &[QM31; 10], right: &[QM31; 10]) -> QM31 {
    left.iter().zip(right).fold(QM31::ONE, |product, (a, b)| {
        let ab = a.mul(*b);
        product.mul(QM31::ONE.sub(*a).sub(*b).add(ab).add(ab))
    })
}

/// Evaluate `H(z) + eta * (eq(r,z) C(z) + mu h1(z))` from the exact 54
/// PCS-bound claims ordered point-major as `z`, `succ(z)`, `xor12(z)`, with
/// columns `C1[0..16], h1, G` at every point.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
pub fn state_only_masked_terminal_value_compiled(
    public: &SpendPublic,
    claims: &[QM31; STATE_ONLY_TERMINAL_CLAIMS],
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
    zerocheck_point: &[QM31; 10],
    mu: QM31,
    eta: QM31,
) -> Result<QM31, StateOnlyTerminalError> {
    if public.fee >= VALUE_LIMIT {
        return Err(StateOnlyTerminalError::PublicFeeOutOfRange);
    }
    let openings = poseidon_openings(claims);
    let selectors = Selectors::at_point(point);
    let poseidon = evaluate_state_only_poseidon_oracle_projected(&openings, &selectors.poseidon());
    let semantic = semantic_packed(public, &openings, &selectors);
    let copy = copy_lane(
        &openings.z,
        claim(claims, 0, H1_COLUMN),
        &selectors,
        lambda,
        chi,
    );
    let prepared_theta = PreparedQm31Multiplier::new(theta);
    let mut composition = copy;
    for lane in semantic.into_iter().rev() {
        composition = prepared_theta.mul(composition).add(lane);
    }
    for lane in poseidon.into_iter().rev() {
        composition = prepared_theta.mul(composition).add(lane);
    }
    let original = equality_value(zerocheck_point, point)
        .mul(composition)
        .add(mu.mul(claim(claims, 0, H1_COLUMN)));
    let mask = state_only_mask_value(&openings.z, claim(claims, 0, G_COLUMN), point);
    Ok(mask.add(eta.mul(original)))
}

#[inline(always)]
fn selected_claim(
    claims: &[QM31; STATE_ONLY_SELECTED_TERMINAL_CLAIMS],
    point: usize,
    column: usize,
) -> QM31 {
    claims[point * STATE_ONLY_SELECTED_TERMINAL_COLUMNS + column]
}

/// Hiding-complete width-28 terminal.  The first sixteen C1 columns enter the
/// semantic oracle, columns 16..26 are mask-only, and `(h1,G)` occupy 26,27.
/// All 84 values remain PCS-bound; only the z-row mask-only values enter H(z).
#[allow(clippy::too_many_arguments)]
#[inline(never)]
pub fn state_only_selected_masked_terminal_value_compiled(
    public: &SpendPublic,
    claims: &[QM31; STATE_ONLY_SELECTED_TERMINAL_CLAIMS],
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
    zerocheck_point: &[QM31; 10],
    mu: QM31,
    eta: QM31,
) -> Result<QM31, StateOnlyTerminalError> {
    if public.fee >= VALUE_LIMIT {
        return Err(StateOnlyTerminalError::PublicFeeOutOfRange);
    }
    let openings = StateOnlyPoseidonOpenings {
        z: core::array::from_fn(|column| selected_claim(claims, 0, column)),
        succ_z: core::array::from_fn(|column| selected_claim(claims, 1, column)),
        xor12_z: core::array::from_fn(|column| selected_claim(claims, 2, column)),
    };
    let mask_only = core::array::from_fn(|column| selected_claim(claims, 0, C1_COLUMNS + column));
    let selectors = Selectors::at_point(point);
    let poseidon = evaluate_state_only_poseidon_oracle_projected(&openings, &selectors.poseidon());
    let semantic = semantic_packed(public, &openings, &selectors);
    let h1_z = selected_claim(claims, 0, SELECTED_H1_COLUMN);
    let copy = copy_lane(&openings.z, h1_z, &selectors, lambda, chi);
    let prepared_theta = PreparedQm31Multiplier::new(theta);
    let mut composition = copy;
    for lane in semantic.into_iter().rev() {
        composition = prepared_theta.mul(composition).add(lane);
    }
    for lane in poseidon.into_iter().rev() {
        composition = prepared_theta.mul(composition).add(lane);
    }
    let original = equality_value(zerocheck_point, point)
        .mul(composition)
        .add(mu.mul(h1_z));
    let mask = state_only_selected_mask_value(
        &openings.z,
        &mask_only,
        selected_claim(claims, 0, SELECTED_G_COLUMN),
        point,
    );
    Ok(mask.add(eta.mul(original)))
}

/// Exact width-28 terminal with diagnostic-only internal boundaries.
///
/// This duplicates the production expression intentionally: it is used only
/// by the read-only measurement instruction and never by the acceptance path.
/// Random off-domain tests pin its output to the production evaluator.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
pub fn state_only_selected_masked_terminal_value_compiled_with_diagnostic_trace<F>(
    public: &SpendPublic,
    claims: &[QM31; STATE_ONLY_SELECTED_TERMINAL_CLAIMS],
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
    if public.fee >= VALUE_LIMIT {
        return Err(StateOnlyTerminalError::PublicFeeOutOfRange);
    }
    let openings = StateOnlyPoseidonOpenings {
        z: core::array::from_fn(|column| selected_claim(claims, 0, column)),
        succ_z: core::array::from_fn(|column| selected_claim(claims, 1, column)),
        xor12_z: core::array::from_fn(|column| selected_claim(claims, 2, column)),
    };
    let mask_only = core::array::from_fn(|column| selected_claim(claims, 0, C1_COLUMNS + column));
    let selectors = Selectors::at_point(point);
    trace(StateOnlyTerminalDiagnosticPhase::Prepared);

    let poseidon = evaluate_state_only_poseidon_oracle_projected(&openings, &selectors.poseidon());
    trace(StateOnlyTerminalDiagnosticPhase::Poseidon);

    let semantic = semantic_packed_impl(public, &openings, &selectors, |phase| {
        trace(match phase {
            StateOnlySemanticDiagnosticPhase::Initial => {
                StateOnlyTerminalDiagnosticPhase::SemanticInitial
            }
            StateOnlySemanticDiagnosticPhase::Absorption => {
                StateOnlyTerminalDiagnosticPhase::SemanticAbsorption
            }
            StateOnlySemanticDiagnosticPhase::Merkle => {
                StateOnlyTerminalDiagnosticPhase::SemanticMerkle
            }
            StateOnlySemanticDiagnosticPhase::Range => {
                StateOnlyTerminalDiagnosticPhase::SemanticRange
            }
            StateOnlySemanticDiagnosticPhase::Public => {
                StateOnlyTerminalDiagnosticPhase::SemanticPublic
            }
        })
    });
    let h1_z = selected_claim(claims, 0, SELECTED_H1_COLUMN);
    let copy = copy_lane_impl(&openings.z, h1_z, &selectors, lambda, chi, |phase| {
        trace(phase)
    });
    let prepared_theta = PreparedQm31Multiplier::new(theta);
    let mut composition = copy;
    for lane in semantic.into_iter().rev() {
        composition = prepared_theta.mul(composition).add(lane);
    }
    for lane in poseidon.into_iter().rev() {
        composition = prepared_theta.mul(composition).add(lane);
    }
    let original = equality_value(zerocheck_point, point)
        .mul(composition)
        .add(mu.mul(h1_z));
    trace(StateOnlyTerminalDiagnosticPhase::CompositionEquality);

    let mask = state_only_selected_mask_value(
        &openings.z,
        &mask_only,
        selected_claim(claims, 0, SELECTED_G_COLUMN),
        point,
    );
    trace(StateOnlyTerminalDiagnosticPhase::Mask);
    let output = mask.add(eta.mul(original));
    trace(StateOnlyTerminalDiagnosticPhase::Final);
    Ok(output)
}

/// Exact terminal expression before the additive state-only mask wrapper.
///
/// This read-only probe preserves the candidate needed by an upstream-HVZK
/// branch where opening privacy retires `H(z)`. It deliberately keeps the
/// current width-28 claims and batching order so its CU delta is isolated;
/// adopting it still requires the transcript/claim schedule to remove the
/// now-unused mask columns and `eta` challenge consistently.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
pub fn state_only_selected_unmasked_terminal_value_compiled(
    public: &SpendPublic,
    claims: &[QM31; STATE_ONLY_SELECTED_TERMINAL_CLAIMS],
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
    zerocheck_point: &[QM31; 10],
    mu: QM31,
) -> Result<QM31, StateOnlyTerminalError> {
    if public.fee >= VALUE_LIMIT {
        return Err(StateOnlyTerminalError::PublicFeeOutOfRange);
    }
    let openings = StateOnlyPoseidonOpenings {
        z: core::array::from_fn(|column| selected_claim(claims, 0, column)),
        succ_z: core::array::from_fn(|column| selected_claim(claims, 1, column)),
        xor12_z: core::array::from_fn(|column| selected_claim(claims, 2, column)),
    };
    let selectors = Selectors::at_point(point);
    let poseidon = evaluate_state_only_poseidon_oracle_projected(&openings, &selectors.poseidon());
    let semantic = semantic_packed(public, &openings, &selectors);
    let h1_z = selected_claim(claims, 0, SELECTED_H1_COLUMN);
    let copy = copy_lane(&openings.z, h1_z, &selectors, lambda, chi);
    let prepared_theta = PreparedQm31Multiplier::new(theta);
    let mut composition = copy;
    for lane in semantic.into_iter().rev() {
        composition = prepared_theta.mul(composition).add(lane);
    }
    for lane in poseidon.into_iter().rev() {
        composition = prepared_theta.mul(composition).add(lane);
    }
    Ok(equality_value(zerocheck_point, point)
        .mul(composition)
        .add(mu.mul(h1_z)))
}

const _: () = assert!(constants::COMPILED_COPY_LINKS.len() == 102);
const _: () = assert!(constants::COPY_PATTERNS.len() == 11);
const _: () = assert!(STATE_ONLY_TERMINAL_CLAIMS == 54);
const _: () = assert!(STATE_ONLY_SELECTED_TERMINAL_COLUMNS == 28);
const _: () = assert!(STATE_ONLY_SELECTED_TERMINAL_CLAIMS == 84);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state_only_constraints::{state_only_masked_terminal_value, StateOnlyPointOpenings};
    use crate::state_only_semantic::{
        evaluate_state_only_semantic_oracle, StateOnlySemanticOpenings, STATE_ONLY_COPY_LINK_COUNT,
    };
    use crate::state_only_trace::{
        state_only_copy_layout_v4, state_only_layout_fingerprint_v4,
        PINNED_STATE_ONLY_LAYOUT_FINGERPRINT,
    };
    use crate::TupleLimb;
    use aspis_core::field::P;
    use aspis_core::statement_sumcheck::PaymentConstraintChallenges;

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

    fn public(rng: &mut Rng) -> SpendPublic {
        SpendPublic {
            anchor: core::array::from_fn(|_| rng.m31()),
            nullifier: core::array::from_fn(|_| rng.m31()),
            output_commitment: core::array::from_fn(|_| rng.m31()),
            asset_id: rng.m31(),
            fee: (rng.next() % u64::from(VALUE_LIMIT)) as u32,
        }
    }

    fn compare(
        public: &SpendPublic,
        claims: &[QM31; STATE_ONLY_TERMINAL_CLAIMS],
        point: &[QM31; 10],
        lambda: QM31,
        chi: QM31,
        batching: &PaymentConstraintChallenges,
        eta: QM31,
    ) {
        let c1 = poseidon_openings(claims);
        let host = StateOnlyPointOpenings {
            semantic: StateOnlySemanticOpenings {
                c1,
                h1_z: claim(claims, 0, H1_COLUMN),
            },
            g_z: claim(claims, 0, G_COLUMN),
        };
        let semantic =
            evaluate_state_only_semantic_oracle(public, &host.semantic, point, lambda, chi)
                .unwrap();
        let selectors = Selectors::at_point(point);
        let direct = semantic_packed(public, &c1, &selectors);
        let reference = semantic_packed_reference(public, &c1, &selectors);
        assert_eq!(direct, reference, "direct-to-packed semantic identity");
        assert_eq!(
            direct,
            semantic.packed_base_lanes(),
            "compiled base semantic lanes"
        );
        assert_eq!(
            copy_lane(&c1.z, host.semantic.h1_z, &selectors, lambda, chi),
            semantic.copy,
            "compiled copy lane"
        );
        let expected =
            state_only_masked_terminal_value(public, &host, point, batching, lambda, chi, eta)
                .unwrap();
        let actual = state_only_masked_terminal_value_compiled(
            public,
            claims,
            point,
            lambda,
            chi,
            batching.theta,
            &batching.zerocheck_point,
            batching.mu,
            eta,
        )
        .unwrap();
        assert_eq!(actual, expected);
    }

    #[test]
    fn compiled_layout_matches_independent_host_builder() {
        assert_eq!(
            STATE_ONLY_TERMINAL_LAYOUT_FINGERPRINT,
            PINNED_STATE_ONLY_LAYOUT_FINGERPRINT
        );
        assert_eq!(
            state_only_layout_fingerprint_v4().unwrap(),
            STATE_ONLY_TERMINAL_LAYOUT_FINGERPRINT
        );
        let layout = state_only_copy_layout_v4().unwrap();
        assert_eq!(layout.links.len(), STATE_ONLY_COPY_LINK_COUNT);
        let mut active_rows = [false; TRACE_ROWS];
        for link in &layout.links {
            active_rows[usize::from(link.producer_row)] = true;
            active_rows[usize::from(link.consumer_row)] = true;
        }
        let active_rows = active_rows
            .iter()
            .copied()
            .enumerate()
            .filter_map(|(row, active)| active.then_some(row as u16))
            .collect::<Vec<_>>();
        assert_eq!(active_rows.as_slice(), constants::COMPILED_COPY_ACTIVE_ROWS);
        let mut fingerprint = 0xcbf2_9ce4_8422_2325u64;
        for row in &active_rows {
            for byte in row.to_le_bytes() {
                fingerprint ^= u64::from(byte);
                fingerprint = fingerprint.wrapping_mul(0x0000_0100_0000_01b3);
            }
        }
        assert_eq!(fingerprint, PINNED_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT);
        let inactive = state_only_copy_inactive_indicator_v4();
        assert_eq!(
            inactive.iter().filter(|value| **value == QM31::ONE).count(),
            TRACE_ROWS - STATE_ONLY_COPY_ACTIVE_ROW_COUNT
        );
        let mut producer_arity = [0u8; TRACE_ROWS];
        let mut consumer_arity = [0u8; TRACE_ROWS];
        for (host, compiled) in layout.links.iter().zip(constants::COMPILED_COPY_LINKS) {
            assert_eq!(compiled.tag, host.tag.0);
            for (tuple, row, arity, endpoint) in [
                (
                    host.producer,
                    host.producer_row,
                    &mut producer_arity,
                    compiled.producer,
                ),
                (
                    host.consumer,
                    host.consumer_row,
                    &mut consumer_arity,
                    compiled.consumer,
                ),
            ] {
                assert_eq!(endpoint.row, row);
                assert_eq!(endpoint.slot, arity[usize::from(row)]);
                arity[usize::from(row)] += 1;
                let mut present = 0u16;
                let mut columns = 0u64;
                for (limb, value) in tuple.limbs.into_iter().enumerate() {
                    if let TupleLimb::Cell(cell) = value {
                        present |= 1 << limb;
                        columns |= u64::from(cell.column) << (4 * limb);
                    }
                }
                assert_eq!(endpoint.present, present);
                assert_eq!(endpoint.columns, columns);
            }
        }
    }

    #[test]
    fn seven_rectangle_copy_active_selector_matches_170_row_walk_off_domain() {
        let mut rng = Rng(0x4143_5449_5645_5f37);
        for _ in 0..64 {
            let point = core::array::from_fn(|_| rng.qm31());
            let selectors = Selectors::at_point(&point);
            let direct = constants::COMPILED_COPY_ACTIVE_ROWS
                .iter()
                .copied()
                .fold(QM31::ZERO, |sum, row| {
                    sum.add(selectors.row(usize::from(row)))
                });
            assert_eq!(selectors.copy_active(), direct);
        }
    }

    #[test]
    fn rank_51_copy_routing_matches_102_link_walk_off_domain() {
        let mut rng = Rng(0x5241_4e4b_5f35_315f);
        for _ in 0..64 {
            let point = core::array::from_fn(|_| rng.qm31());
            let selectors = Selectors::at_point(&point);
            assert_eq!(
                evaluate_copy_routing(&selectors),
                evaluate_copy_routing_direct(&selectors)
            );
        }
    }

    #[test]
    fn five_base_copy_pattern_dots_match_all_eleven_literal_patterns() {
        let mut rng = Rng(0x5041_5454_4552_4e35);
        for _ in 0..64 {
            let openings = core::array::from_fn(|_| rng.qm31());
            let lambda = rng.qm31();
            let mut powers = [QM31::ZERO; 16];
            let mut power = lambda;
            for output in &mut powers {
                *output = power;
                power = power.mul(lambda);
            }
            let actual = copy_pattern_values(&openings, &powers);
            for (pattern, &(present, columns)) in constants::COPY_PATTERNS.iter().enumerate() {
                let len = present.count_ones() as usize;
                let selected: [QM31; 16] =
                    core::array::from_fn(|limb| openings[((columns >> (4 * limb)) & 0xf) as usize]);
                assert_eq!(actual[pattern], qm31_dot(&powers[..len], &selected[..len]));
            }
        }
    }

    #[test]
    fn compiled_terminal_matches_host_at_random_off_domain_points_and_mutations() {
        let mut rng = Rng(0x5445_524d_494e_414c);
        for _ in 0..64 {
            let public = public(&mut rng);
            let claims = core::array::from_fn(|_| rng.qm31());
            let point = core::array::from_fn(|_| rng.qm31());
            let batching = PaymentConstraintChallenges {
                theta: rng.qm31(),
                zerocheck_point: core::array::from_fn(|_| rng.qm31()),
                mu: rng.qm31(),
            };
            compare(
                &public,
                &claims,
                &point,
                rng.qm31(),
                rng.qm31(),
                &batching,
                rng.qm31(),
            );
        }

        let public = public(&mut rng);
        let base: [QM31; STATE_ONLY_TERMINAL_CLAIMS] = core::array::from_fn(|_| rng.qm31());
        let point = core::array::from_fn(|_| rng.qm31());
        let batching = PaymentConstraintChallenges {
            theta: rng.qm31(),
            zerocheck_point: core::array::from_fn(|_| rng.qm31()),
            mu: rng.qm31(),
        };
        let lambda = rng.qm31();
        let chi = rng.qm31();
        let eta = rng.qm31();
        for index in 0..STATE_ONLY_TERMINAL_CLAIMS {
            let mut corrupted = base;
            corrupted[index] = corrupted[index].add(QM31::ONE);
            compare(&public, &corrupted, &point, lambda, chi, &batching, eta);
        }
    }

    #[test]
    fn selected_width28_terminal_adds_exactly_the_ten_mask_only_terms() {
        use aspis_core::state_only_hiding::state_only_mask_only_c1_factor;

        let mut rng = Rng(0x5749_4454_4832_3800);
        for _ in 0..16 {
            let public = public(&mut rng);
            let selected: [QM31; STATE_ONLY_SELECTED_TERMINAL_CLAIMS] =
                core::array::from_fn(|_| rng.qm31());
            let compact: [QM31; STATE_ONLY_TERMINAL_CLAIMS] = core::array::from_fn(|index| {
                let point = index / STATE_ONLY_TERMINAL_COLUMNS;
                let column = index % STATE_ONLY_TERMINAL_COLUMNS;
                let selected_column = match column {
                    0..=15 => column,
                    H1_COLUMN => SELECTED_H1_COLUMN,
                    G_COLUMN => SELECTED_G_COLUMN,
                    _ => unreachable!(),
                };
                selected_claim(&selected, point, selected_column)
            });
            let point = core::array::from_fn(|_| rng.qm31());
            let zerocheck_point = core::array::from_fn(|_| rng.qm31());
            let lambda = rng.qm31();
            let chi = rng.qm31();
            let theta = rng.qm31();
            let mu = rng.qm31();
            let eta = rng.qm31();
            let compact_value = state_only_masked_terminal_value_compiled(
                &public,
                &compact,
                &point,
                lambda,
                chi,
                theta,
                &zerocheck_point,
                mu,
                eta,
            )
            .unwrap();
            let mask_only =
                (0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS).fold(QM31::ZERO, |sum, column| {
                    sum.add(
                        state_only_mask_only_c1_factor(column, &point).mul(selected_claim(
                            &selected,
                            0,
                            C1_COLUMNS + column,
                        )),
                    )
                });
            let expected = compact_value.add(mask_only);
            let unmasked = state_only_selected_unmasked_terminal_value_compiled(
                &public,
                &selected,
                &point,
                lambda,
                chi,
                theta,
                &zerocheck_point,
                mu,
            )
            .unwrap();
            let selected_z = core::array::from_fn(|column| selected_claim(&selected, 0, column));
            let selected_mask_only =
                core::array::from_fn(|column| selected_claim(&selected, 0, C1_COLUMNS + column));
            let full_mask = state_only_selected_mask_value(
                &selected_z,
                &selected_mask_only,
                selected_claim(&selected, 0, SELECTED_G_COLUMN),
                &point,
            );
            assert_eq!(expected, full_mask.add(eta.mul(unmasked)));
            assert_eq!(
                state_only_selected_masked_terminal_value_compiled(
                    &public,
                    &selected,
                    &point,
                    lambda,
                    chi,
                    theta,
                    &zerocheck_point,
                    mu,
                    eta,
                ),
                Ok(expected)
            );
            let mut phases = Vec::new();
            assert_eq!(
                state_only_selected_masked_terminal_value_compiled_with_diagnostic_trace(
                    &public,
                    &selected,
                    &point,
                    lambda,
                    chi,
                    theta,
                    &zerocheck_point,
                    mu,
                    eta,
                    |phase| phases.push(phase),
                ),
                Ok(expected)
            );
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
}
