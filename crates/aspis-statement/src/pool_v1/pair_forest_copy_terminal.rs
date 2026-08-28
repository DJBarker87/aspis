//! Allocation-bounded SBF-safe Copy lane for the eight-lane Pool V1
//! pair-forest relation.
//!
//! Runtime evaluation consumes only generated patterns, endpoints and fixed
//! active-row masks. The allocation-heavy typed registry remains the
//! independent host compiler/reference boundary and is not linked on SBF.

use alloc::boxed::Box;

use aspis_core::field::{PreparedQm31Multiplier, CM31, M31, QM31};

use crate::poseidon2::POSEIDON2_WIDTH;

pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1: usize = 1024;
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_COLUMNS_V1: usize = 16;
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1: usize = 136;
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1: usize = 14;
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_FIXED_HEAP_ALLOCATIONS_V1: usize = 1;
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_SELECTOR_HEAP_BYTES_V1: usize =
    core::mem::size_of::<Selectors>();
pub const PINNED_POOL_V1_PAIR_FOREST_COPY_TERMINAL_ACTIVE_ROWS_FINGERPRINT_V1: u64 =
    constants::ACTIVE_ROWS_FINGERPRINT;

/// Exact SBF-safe active-row schedule consumed by the selected verifier.
/// Host generation tests independently replay it from the typed tuple registry.
pub fn pool_v1_pair_forest_copy_active_row_masks_compiled_v1() -> &'static [u16; 64] {
    &constants::ACTIVE_ROW_MASKS
}

const _: () = assert!(POSEIDON2_WIDTH == POOL_V1_PAIR_FOREST_COPY_TERMINAL_COLUMNS_V1);
const _: () = assert!(constants::COPY_LINKS.len() == POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1);
const _: () =
    assert!(constants::COPY_PATTERNS.len() == POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1);
const _: () = assert!(constants::ACTIVE_ROW_MASKS.len() == 64);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairForestCompiledVariantV1 {
    PrivateTransfer,
    Withdrawal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestCompiledCopyTerminalV1 {
    pub residual: QM31,
    pub active: QM31,
}

#[derive(Clone, Copy)]
struct CompiledPoolV1PairForestPattern {
    /// 0 = zero, 1 = row-local C1 cell plus a canonical M31 offset.
    kinds: [u8; POSEIDON2_WIDTH],
    columns: [u8; POSEIDON2_WIDTH],
    offsets: [u32; POSEIDON2_WIDTH],
}

#[derive(Clone, Copy)]
struct CompiledPoolV1PairForestEndpoint {
    row: u16,
    slot: u8,
    pattern: u8,
}

#[derive(Clone, Copy)]
struct CompiledPoolV1PairForestLink {
    tag: u32,
    /// 0 = one, 1 = transfer, 2 = withdrawal, 3 = append-left,
    /// 4 = append-right.
    weight_kind: u8,
    weight_level: u8,
    producer: CompiledPoolV1PairForestEndpoint,
    consumer: CompiledPoolV1PairForestEndpoint,
}

mod constants {
    use super::{
        CompiledPoolV1PairForestEndpoint, CompiledPoolV1PairForestLink,
        CompiledPoolV1PairForestPattern,
    };
    include!("pair_forest_copy_terminal_constants.rs");
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
pub(crate) struct Selectors {
    pub(crate) high: [QM31; 64],
    pub(crate) low: [QM31; 16],
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

    pub(crate) fn at_point(point: &[QM31; 10]) -> Self {
        Self {
            high: Self::expand(&point[..6]),
            low: Self::expand(&point[6..]),
        }
    }

    #[inline(never)]
    pub(crate) fn boxed_at_point(point: &[QM31; 10]) -> Box<Self> {
        Box::new(Self::at_point(point))
    }

    #[inline(always)]
    pub(crate) fn row(&self, row: usize) -> QM31 {
        debug_assert!(row < POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1);
        self.high[row >> 4].mul(self.low[row & 15])
    }

    fn active(&self) -> QM31 {
        let mut sum = QM31::ZERO;
        let mut block = 0usize;
        while block < 64 {
            let mask = constants::ACTIVE_ROW_MASKS[block];
            if mask != 0 {
                sum = sum.add(self.high[block].mul(selector_mask_sum_16(&self.low, mask)));
            }
            block += 1;
        }
        sum
    }
}

fn pattern_values(
    openings: &[QM31; POSEIDON2_WIDTH],
    lambda: QM31,
) -> [QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1] {
    let mut powers = [QM31::ZERO; POSEIDON2_WIDTH];
    let mut power = lambda;
    let mut limb = 0usize;
    while limb < POSEIDON2_WIDTH {
        powers[limb] = power;
        power = power.mul(lambda);
        limb += 1;
    }
    let mut result = [QM31::ZERO; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1];
    let mut pattern_index = 0usize;
    while pattern_index < POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1 {
        let pattern = constants::COPY_PATTERNS[pattern_index];
        let mut value = QM31::ZERO;
        limb = 0;
        while limb < POSEIDON2_WIDTH {
            if pattern.kinds[limb] == 1 {
                let source = openings[usize::from(pattern.columns[limb])]
                    .add(lift(M31(pattern.offsets[limb])));
                value = value.add(powers[limb].mul(source));
            }
            limb += 1;
        }
        result[pattern_index] = value;
        pattern_index += 1;
    }
    result
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

#[inline(always)]
fn link_weight(
    link: CompiledPoolV1PairForestLink,
    append_index: u64,
    variant: PoolV1PairForestCompiledVariantV1,
) -> M31 {
    match link.weight_kind {
        0 => M31::ONE,
        1 => M31(u32::from(
            variant == PoolV1PairForestCompiledVariantV1::PrivateTransfer,
        )),
        2 => M31(u32::from(
            variant == PoolV1PairForestCompiledVariantV1::Withdrawal,
        )),
        3 => M31(1 - ((append_index >> link.weight_level) & 1) as u32),
        4 => M31(((append_index >> link.weight_level) & 1) as u32),
        _ => unreachable!("generated Pool V1 pair-forest Copy weight"),
    }
}

fn accumulate_endpoint(
    values: &mut [QM31; 2],
    weights: &mut [QM31; 2],
    endpoint: CompiledPoolV1PairForestEndpoint,
    tag: u32,
    weight: M31,
    patterns: &[QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1],
    selectors: &Selectors,
) {
    let selector = selectors.row(usize::from(endpoint.row));
    let slot = usize::from(endpoint.slot);
    weights[slot] = weights[slot].add(selector.mul_m31(weight));
    let compressed = lift(M31(tag)).add(patterns[usize::from(endpoint.pattern)]);
    values[slot] = values[slot].add(selector.mul(compressed));
}

pub(crate) fn evaluate_with_selectors(
    openings: &[QM31; POSEIDON2_WIDTH],
    h1_z: QM31,
    selectors: &Selectors,
    lambda: QM31,
    chi: QM31,
    append_index: u64,
    variant: PoolV1PairForestCompiledVariantV1,
) -> PoolV1PairForestCompiledCopyTerminalV1 {
    let patterns = pattern_values(openings, lambda);
    let mut row = CopyRowExtension {
        producer_values: [QM31::ZERO; 2],
        producer_weights: [QM31::ZERO; 2],
        consumer_values: [QM31::ZERO; 2],
        consumer_weights: [QM31::ZERO; 2],
    };
    let mut link_index = 0usize;
    while link_index < POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1 {
        let link = constants::COPY_LINKS[link_index];
        let weight = link_weight(link, append_index, variant);
        accumulate_endpoint(
            &mut row.producer_values,
            &mut row.producer_weights,
            link.producer,
            link.tag,
            weight,
            &patterns,
            selectors,
        );
        accumulate_endpoint(
            &mut row.consumer_values,
            &mut row.consumer_weights,
            link.consumer,
            link.tag,
            weight,
            &patterns,
            selectors,
        );
        link_index += 1;
    }
    let active = selectors.active();
    PoolV1PairForestCompiledCopyTerminalV1 {
        residual: active.mul(copy_residual(row, h1_z, chi)),
        active,
    }
}

/// Evaluate the exact 136-link pair-forest Copy lane from the frozen sixteen
/// merged-C1 openings and one H1 opening. This performs one fixed-size
/// selector allocation and no registry- or input-dependent allocation.
pub fn evaluate_pool_v1_pair_forest_copy_terminal_compiled_v1(
    openings: &[QM31; POSEIDON2_WIDTH],
    h1_z: QM31,
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    append_index: u64,
    variant: PoolV1PairForestCompiledVariantV1,
) -> PoolV1PairForestCompiledCopyTerminalV1 {
    let selectors = Selectors::boxed_at_point(point);
    evaluate_with_selectors(
        openings,
        h1_z,
        &selectors,
        lambda,
        chi,
        append_index,
        variant,
    )
}

pub fn pool_v1_pair_forest_copy_active_at_point_compiled_v1(point: &[QM31; 10]) -> QM31 {
    Selectors::at_point(point).active()
}

/// Source-extraction wrapper for a Boolean terminal row. `variant` is zero
/// for private transfer and one for withdrawal.
#[doc(hidden)]
pub fn pool_v1_pair_forest_copy_lane_boolean_extraction_v1(
    variant: u8,
    selected_row: u16,
    openings: &[QM31; POSEIDON2_WIDTH],
    h1_z: QM31,
    lambda: QM31,
    chi: QM31,
    append_index: u64,
) -> Option<PoolV1PairForestCompiledCopyTerminalV1> {
    if usize::from(selected_row) >= POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1 {
        return None;
    }
    let variant = match variant {
        0 => PoolV1PairForestCompiledVariantV1::PrivateTransfer,
        1 => PoolV1PairForestCompiledVariantV1::Withdrawal,
        _ => return None,
    };
    let mut high = [QM31::ZERO; 64];
    let mut low = [QM31::ZERO; 16];
    high[usize::from(selected_row >> 4)] = QM31::ONE;
    low[usize::from(selected_row & 15)] = QM31::ONE;
    let selectors = Selectors { high, low };
    Some(evaluate_with_selectors(
        openings,
        h1_z,
        &selectors,
        lambda,
        chi,
        append_index,
        variant,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;
    use aspis_core::field::P;

    use crate::pool_v1::{
        pair_forest_semantic_oracle::{
            evaluate_pool_v1_pair_forest_copy_terminal_v1,
            pool_v1_pair_forest_copy_active_at_point_v1,
        },
        pair_forest_trace::build_pool_v1_pair_forest_copy_registry_v1,
        pair_trace::{PoolV1PairCopyWeightV1, PoolV1PairTraceVariantV1, PoolV1PairTupleLimbV1},
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

    fn host_pattern(
        tuple: crate::pool_v1::pair_trace::PoolV1PairCopyTupleV1,
    ) -> CompiledPoolV1PairForestPattern {
        let mut output = CompiledPoolV1PairForestPattern {
            kinds: [0; 16],
            columns: [0; 16],
            offsets: [0; 16],
        };
        for (index, limb) in tuple.limbs.into_iter().enumerate() {
            match limb {
                PoolV1PairTupleLimbV1::Zero => {}
                PoolV1PairTupleLimbV1::Cell { source, offset } => {
                    assert_eq!(source.cell.row, tuple.row);
                    output.kinds[index] = 1;
                    output.columns[index] = source.cell.column;
                    output.offsets[index] = offset.0;
                }
            }
        }
        output
    }

    fn weight_code(weight: PoolV1PairCopyWeightV1) -> (u8, u8) {
        match weight {
            PoolV1PairCopyWeightV1::One => (0, 0),
            PoolV1PairCopyWeightV1::PrivateTransferOnly => (1, 0),
            PoolV1PairCopyWeightV1::WithdrawalOnly => (2, 0),
            PoolV1PairCopyWeightV1::AppendCurrentLeft { level } => (3, level),
            PoolV1PairCopyWeightV1::AppendCurrentRight { level } => (4, level),
        }
    }

    #[test]
    fn generated_constants_equal_the_typed_forest_registry() {
        let registry = build_pool_v1_pair_forest_copy_registry_v1().unwrap();
        assert_eq!(registry.len(), constants::COPY_LINKS.len());
        let mut host_patterns = Vec::<CompiledPoolV1PairForestPattern>::new();
        for link in &registry {
            for tuple in [link.producer, link.consumer] {
                let candidate = host_pattern(tuple);
                if !host_patterns.iter().any(|item| {
                    item.kinds == candidate.kinds
                        && item.columns == candidate.columns
                        && item.offsets == candidate.offsets
                }) {
                    host_patterns.push(candidate);
                }
            }
        }
        assert_eq!(host_patterns.len(), constants::COPY_PATTERNS.len());
        for (host, compiled) in host_patterns.iter().zip(constants::COPY_PATTERNS) {
            assert_eq!(host.kinds, compiled.kinds);
            assert_eq!(host.columns, compiled.columns);
            assert_eq!(host.offsets, compiled.offsets);
        }

        let mut producer_arity = [0u8; 1024];
        let mut consumer_arity = [0u8; 1024];
        let mut active_masks = [0u16; 64];
        for (host, compiled) in registry.iter().zip(constants::COPY_LINKS) {
            assert_eq!(host.tag.0, compiled.tag);
            assert_eq!(
                weight_code(host.weight),
                (compiled.weight_kind, compiled.weight_level)
            );
            for (tuple, arity, endpoint) in [
                (host.producer, &mut producer_arity, compiled.producer),
                (host.consumer, &mut consumer_arity, compiled.consumer),
            ] {
                let row = usize::from(tuple.row);
                active_masks[row >> 4] |= 1 << (row & 15);
                assert_eq!(endpoint.row, tuple.row);
                assert_eq!(endpoint.slot, arity[row]);
                arity[row] += 1;
                let expected = host_pattern(tuple);
                let expected = host_patterns
                    .iter()
                    .position(|item| {
                        item.kinds == expected.kinds
                            && item.columns == expected.columns
                            && item.offsets == expected.offsets
                    })
                    .unwrap();
                assert_eq!(usize::from(endpoint.pattern), expected);
            }
        }
        assert_eq!(active_masks, constants::ACTIVE_ROW_MASKS);
        assert_eq!(
            PINNED_POOL_V1_PAIR_FOREST_COPY_TERMINAL_ACTIVE_ROWS_FINGERPRINT_V1,
            0xdf39_4a5a_8554_d09c,
        );
    }

    #[test]
    fn compiled_copy_lane_matches_host_reference_off_domain() {
        let mut rng = Rng(0x7061_6972_666f_7265);
        for (compiled_variant, host_variant) in [
            (
                PoolV1PairForestCompiledVariantV1::PrivateTransfer,
                PoolV1PairTraceVariantV1::PrivateTransfer,
            ),
            (
                PoolV1PairForestCompiledVariantV1::Withdrawal,
                PoolV1PairTraceVariantV1::Withdrawal,
            ),
        ] {
            for _ in 0..32 {
                let openings = core::array::from_fn(|_| rng.qm31());
                let h1_z = rng.qm31();
                let point = core::array::from_fn(|_| rng.qm31());
                let lambda = rng.qm31();
                let chi = rng.qm31();
                let append_index = rng.next() & ((1 << 20) - 1);
                let compiled = evaluate_pool_v1_pair_forest_copy_terminal_compiled_v1(
                    &openings,
                    h1_z,
                    &point,
                    lambda,
                    chi,
                    append_index,
                    compiled_variant,
                );
                let host = evaluate_pool_v1_pair_forest_copy_terminal_v1(
                    &openings,
                    h1_z,
                    &point,
                    lambda,
                    chi,
                    append_index,
                    host_variant,
                )
                .unwrap();
                assert_eq!(compiled.residual, host.residual);
                assert_eq!(compiled.active, host.active);
                assert_eq!(
                    pool_v1_pair_forest_copy_active_at_point_compiled_v1(&point),
                    pool_v1_pair_forest_copy_active_at_point_v1(&point).unwrap(),
                );
            }
        }
    }

    #[test]
    fn boolean_extraction_is_exact_and_fail_closed() {
        let mut rng = Rng(0x626f_6f6c_6561_6e31);
        for (variant_byte, variant) in [
            (0, PoolV1PairForestCompiledVariantV1::PrivateTransfer),
            (1, PoolV1PairForestCompiledVariantV1::Withdrawal),
        ] {
            for row in [0u16, 11, 412, 912, 1008, 1023] {
                let openings = core::array::from_fn(|_| rng.qm31());
                let h1_z = rng.qm31();
                let lambda = rng.qm31();
                let chi = rng.qm31();
                let append_index = rng.next() & ((1 << 20) - 1);
                let point = core::array::from_fn(|coordinate| {
                    if (usize::from(row) >> (9 - coordinate)) & 1 == 0 {
                        QM31::ZERO
                    } else {
                        QM31::ONE
                    }
                });
                let expected = evaluate_pool_v1_pair_forest_copy_terminal_compiled_v1(
                    &openings,
                    h1_z,
                    &point,
                    lambda,
                    chi,
                    append_index,
                    variant,
                );
                assert_eq!(
                    pool_v1_pair_forest_copy_lane_boolean_extraction_v1(
                        variant_byte,
                        row,
                        &openings,
                        h1_z,
                        lambda,
                        chi,
                        append_index,
                    ),
                    Some(expected),
                );
            }
        }
        let zero = [QM31::ZERO; 16];
        assert_eq!(
            pool_v1_pair_forest_copy_lane_boolean_extraction_v1(
                2,
                0,
                &zero,
                QM31::ZERO,
                QM31::ZERO,
                QM31::ZERO,
                0,
            ),
            None,
        );
        assert_eq!(
            pool_v1_pair_forest_copy_lane_boolean_extraction_v1(
                0,
                1024,
                &zero,
                QM31::ZERO,
                QM31::ZERO,
                QM31::ZERO,
                0,
            ),
            None,
        );
    }
}
