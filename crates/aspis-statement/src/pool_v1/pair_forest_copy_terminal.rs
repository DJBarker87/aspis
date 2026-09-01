//! Allocation-bounded SBF-safe Copy lane for the eight-lane Pool V1
//! pair-forest relation.
//!
//! Runtime evaluation consumes only generated patterns, endpoints and fixed
//! active-row masks. The allocation-heavy typed registry remains the
//! independent host compiler/reference boundary and is not linked on SBF.

use alloc::{boxed::Box, vec};

#[cfg(any(test, feature = "pool-v1-pair-forest-copy-finish-dot-basis-audit"))]
use aspis_core::field::{qm31_sum_products2, qm31_sum_products3, qm31_sum_products4};
use aspis_core::field::{PreparedQm31Multiplier, CM31, M31, QM31};

use crate::poseidon2::POSEIDON2_WIDTH;

pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1: usize = 1024;
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_COLUMNS_V1: usize = 16;
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1: usize = 136;
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1: usize = 14;
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_FIXED_HEAP_ALLOCATIONS_V1: usize =
    if cfg!(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit") {
        2
    } else {
        1
    };
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_SELECTOR_HEAP_BYTES_V1: usize =
    core::mem::size_of::<Selectors>();
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_TENSOR_HEAP_BYTES_V1: usize =
    if cfg!(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit") {
        103 * core::mem::size_of::<QM31>()
    } else {
        0
    };
pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_FIXED_HEAP_BYTES_V1: usize =
    POOL_V1_PAIR_FOREST_COPY_TERMINAL_SELECTOR_HEAP_BYTES_V1
        + POOL_V1_PAIR_FOREST_COPY_TERMINAL_TENSOR_HEAP_BYTES_V1;
pub const PINNED_POOL_V1_PAIR_FOREST_COPY_TERMINAL_ACTIVE_ROWS_FINGERPRINT_V1: u64 =
    constants::ACTIVE_ROWS_FINGERPRINT;

/// Exact SBF-safe active-row schedule consumed by the selected verifier.
/// Host generation tests independently replay it from the typed tuple registry.
pub fn pool_v1_pair_forest_copy_active_row_masks_compiled_v1() -> &'static [u16; 64] {
    &constants::ACTIVE_ROW_MASKS
}

/// Frozen row-to-group schedule generated from the exact pair-forest copy
/// registry.  The selected verifier consumes this directly instead of
/// rebuilding and deduplicating public layout data on every transaction.
pub fn pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1() -> &'static [u8; 64] {
    &constants::INACTIVE_ROW_GROUPS
}

/// Deduplicated inactive masks referenced by
/// [`pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1`].
pub fn pool_v1_pair_forest_copy_inactive_group_masks_compiled_v1() -> &'static [u16] {
    &constants::INACTIVE_GROUP_MASKS
}

const _: () = assert!(POSEIDON2_WIDTH == POOL_V1_PAIR_FOREST_COPY_TERMINAL_COLUMNS_V1);
const _: () = assert!(constants::COPY_LINKS.len() == POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1);
const _: () =
    assert!(constants::COPY_PATTERNS.len() == POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1);
const _: () = assert!(constants::ACTIVE_ROW_MASKS.len() == 64);
const _: () = assert!(constants::INACTIVE_ROW_GROUPS.len() == 64);
const _: () = assert!(constants::INACTIVE_GROUP_MASKS.len() <= 64);

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
fn lift_m31(value: M31) -> QM31 {
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

    #[cfg(any(test, not(feature = "pool-v1-pair-forest-active-mask-basis-audit")))]
    fn active_literal(&self) -> QM31 {
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

    #[cfg(any(test, feature = "pool-v1-pair-forest-active-mask-basis-audit"))]
    fn active_mask_basis(&self) -> QM31 {
        const MASKS: [u16; 7] = [6144, 6145, 4097, 2048, 2049, 26214, 1749];
        let mut high_sums = [QM31::ZERO; MASKS.len()];
        let mut block = 0usize;
        while block < constants::ACTIVE_ROW_MASKS.len() {
            let mask = constants::ACTIVE_ROW_MASKS[block];
            let coordinate = match mask {
                6144 => 0,
                6145 => 1,
                4097 => 2,
                2048 => 3,
                2049 => 4,
                26214 => 5,
                1749 => 6,
                _ => unreachable!("generated Copy active mask outside frozen basis"),
            };
            high_sums[coordinate] = high_sums[coordinate].add(self.high[block]);
            block += 1;
        }
        let mut sum = QM31::ZERO;
        let mut coordinate = 0usize;
        while coordinate < MASKS.len() {
            sum = sum
                .add(high_sums[coordinate].mul(selector_mask_sum_16(&self.low, MASKS[coordinate])));
            coordinate += 1;
        }
        sum
    }

    #[inline(always)]
    fn active(&self) -> QM31 {
        #[cfg(not(feature = "pool-v1-pair-forest-active-mask-basis-audit"))]
        return self.active_literal();
        #[cfg(feature = "pool-v1-pair-forest-active-mask-basis-audit")]
        return self.active_mask_basis();
    }
}

#[cfg(any(test, not(feature = "pool-v1-pair-forest-pattern-window-audit")))]
fn pattern_values_literal(
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
                    .add(lift_m31(M31(pattern.offsets[limb])));
                value = value.add(powers[limb].mul(source));
            }
            limb += 1;
        }
        result[pattern_index] = value;
        pattern_index += 1;
    }
    result
}

/// Exact CSE for the frozen fourteen-pattern table. Pattern 0 is the two
/// adjacent eight-limb windows, patterns 2 and 3 are exact six-limb prefixes,
/// and pattern 10 differs from pattern 13 only by its final public offset.
#[cfg(any(test, feature = "pool-v1-pair-forest-pattern-window-audit"))]
fn pattern_values_windowed(
    openings: &[QM31; POSEIDON2_WIDTH],
    lambda: QM31,
) -> [QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1] {
    let mut powers = [QM31::ZERO; 8];
    let mut power = lambda;
    let mut slot = 0usize;
    while slot < powers.len() {
        powers[slot] = power;
        power = power.mul(lambda);
        slot += 1;
    }
    let prepared: [PreparedQm31Multiplier; 8] = powers.map(PreparedQm31Multiplier::new);
    let window = |start: usize| {
        let mut value = QM31::ZERO;
        let mut slot = 0usize;
        while slot < 8 {
            value = value.add(prepared[slot].mul(openings[start + slot]));
            slot += 1;
        }
        value
    };
    let window_0 = window(0);
    let window_1 = window(1);
    let window_2 = window(2);
    let window_8 = window(8);
    let mut result = [QM31::ZERO; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1];
    result[0] = window_0.add(prepared[7].mul(window_8));
    result[1] = window_0;
    result[2] = window_2
        .sub(prepared[6].mul(openings[8]))
        .sub(prepared[7].mul(openings[9]));
    result[3] = window_0
        .sub(prepared[6].mul(openings[6]))
        .sub(prepared[7].mul(openings[7]));
    result[4] = prepared[0]
        .mul(openings[0])
        .add(prepared[1].mul(openings[1]));
    result[5] = prepared[0]
        .mul(openings[6])
        .add(prepared[1].mul(openings[7]));
    result[6] = prepared[0].mul(openings[0]);
    result[7] = prepared[0].mul(openings[10]);
    result[8] = prepared[0].mul(openings[1]);
    result[9] = prepared[0].mul(openings[2]);
    result[10] = window_8.add(prepared[7].mul(lift_m31(M31(1_051_521_018))));
    result[11] = window_2;
    result[12] = window_1;
    result[13] = window_8;
    result
}

fn pattern_values(
    openings: &[QM31; POSEIDON2_WIDTH],
    lambda: QM31,
) -> [QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1] {
    #[cfg(not(feature = "pool-v1-pair-forest-pattern-window-audit"))]
    return pattern_values_literal(openings, lambda);
    #[cfg(feature = "pool-v1-pair-forest-pattern-window-audit")]
    return pattern_values_windowed(openings, lambda);
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

/// Exact specialization of `sum + selector * weight` for the generated Copy
/// grammar. `link_weight` has image `{0,1}` for every variant and append
/// index; focused tests bind that image to every checked-in generated link.
#[cfg(any(test, feature = "pool-v1-pair-forest-binary-copy-weights-audit"))]
#[inline(always)]
fn add_binary_weight(sum: QM31, selector: QM31, weight: M31) -> QM31 {
    match weight.0 {
        0 => sum,
        1 => sum.add(selector),
        _ => unreachable!("generated Pool V1 pair-forest Copy weight is not binary"),
    }
}

/// Small direct-mapped memo for the checked-in generated endpoint stream.
/// The row tag makes collision behavior purely a performance concern: a
/// collision always recomputes the literal selector before replacing a slot.
#[cfg(any(test, feature = "pool-v1-pair-forest-endpoint-selector-cache-audit"))]
struct EndpointSelectorCache {
    rows: [u16; 32],
    values: [QM31; 32],
}

#[cfg(any(test, feature = "pool-v1-pair-forest-endpoint-selector-cache-audit"))]
impl EndpointSelectorCache {
    fn new() -> Self {
        Self {
            rows: [u16::MAX; 32],
            values: [QM31::ZERO; 32],
        }
    }

    #[inline(always)]
    fn selector(&mut self, row: u16, selectors: &Selectors) -> QM31 {
        let slot = usize::from(row) & (self.rows.len() - 1);
        if self.rows[slot] == row {
            self.values[slot]
        } else {
            let value = selectors.row(usize::from(row));
            self.rows[slot] = row;
            self.values[slot] = value;
            value
        }
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
    #[cfg(feature = "pool-v1-pair-forest-endpoint-selector-cache-audit")]
    selector_cache: &mut EndpointSelectorCache,
) {
    #[cfg(not(feature = "pool-v1-pair-forest-endpoint-selector-cache-audit"))]
    let selector = selectors.row(usize::from(endpoint.row));
    #[cfg(feature = "pool-v1-pair-forest-endpoint-selector-cache-audit")]
    let selector = selector_cache.selector(endpoint.row, selectors);
    let slot = usize::from(endpoint.slot);
    #[cfg(not(feature = "pool-v1-pair-forest-binary-copy-weights-audit"))]
    {
        weights[slot] = weights[slot].add(selector.mul_m31(weight));
    }
    #[cfg(feature = "pool-v1-pair-forest-binary-copy-weights-audit")]
    {
        weights[slot] = add_binary_weight(weights[slot], selector, weight);
    }
    let compressed = lift_m31(M31(tag)).add(patterns[usize::from(endpoint.pattern)]);
    values[slot] = values[slot].add(selector.mul(compressed));
}

/// Exact support of the four `(side, slot)` linear forms in the generated
/// fourteen-pattern basis.  The masks are derived from `COPY_LINKS` and are
/// checked against that table in the focused tests below.
#[cfg(any(test, feature = "pool-v1-pair-forest-copy-pattern-basis-audit"))]
const COPY_PATTERN_GROUP_SUPPORT: [u16; 4] = [0x0ed7, 0x2042, 0x1dcb, 0x01e2];
#[cfg(any(test, feature = "pool-v1-pair-forest-copy-pattern-basis-audit"))]
const COPY_PATTERN_COORDINATES: [[u8; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1]; 4] = [
    [
        0,
        1,
        2,
        u8::MAX,
        3,
        u8::MAX,
        4,
        5,
        u8::MAX,
        6,
        7,
        8,
        u8::MAX,
        u8::MAX,
    ],
    [
        u8::MAX,
        9,
        u8::MAX,
        u8::MAX,
        u8::MAX,
        u8::MAX,
        10,
        u8::MAX,
        u8::MAX,
        u8::MAX,
        u8::MAX,
        u8::MAX,
        u8::MAX,
        11,
    ],
    [
        12,
        13,
        u8::MAX,
        14,
        u8::MAX,
        u8::MAX,
        15,
        16,
        17,
        u8::MAX,
        18,
        19,
        20,
        u8::MAX,
    ],
    [
        u8::MAX,
        21,
        u8::MAX,
        u8::MAX,
        u8::MAX,
        22,
        23,
        24,
        25,
        u8::MAX,
        u8::MAX,
        u8::MAX,
        u8::MAX,
        u8::MAX,
    ],
];
#[cfg(any(test, feature = "pool-v1-pair-forest-copy-pattern-basis-audit"))]
const COPY_PATTERN_COORDINATE_PATTERNS: [u8; 26] = [
    0, 1, 2, 4, 6, 7, 9, 10, 11, 1, 6, 13, 0, 1, 3, 6, 7, 8, 10, 11, 12, 1, 5, 6, 7, 8,
];
#[cfg(any(test, feature = "pool-v1-pair-forest-copy-pattern-basis-audit"))]
const COPY_PATTERN_GROUP_OFFSETS: [usize; 5] = [0, 9, 12, 21, 26];

#[cfg(any(test, feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit"))]
const COPY_GROUP_LOCAL_COORDINATE_GROUPS: [u8; 30] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3,
];
#[cfg(any(test, feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit"))]
const COPY_GROUP_LOCAL_COORDINATE_LOCALS: [u8; 30] = [
    0, 1, 2, 4, 6, 10, 11, 12, 14, 2, 6, 10, 11, 12, 14, 0, 1, 2, 4, 5, 6, 7, 9, 10, 12, 13, 6, 7,
    9, 12,
];
#[cfg(any(test, feature = "pool-v1-pair-forest-copy-finish-dot-basis-audit"))]
const COPY_GROUP_LOCAL_GROUP_OFFSETS: [usize; 5] = [0, 9, 15, 26, 30];
#[cfg(any(test, feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit"))]
const COPY_PATTERN_LOCAL_COORDINATE_GROUPS: [u8; 43] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3,
];
#[cfg(any(test, feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit"))]
const COPY_PATTERN_LOCAL_COORDINATE_PATTERNS: [u8; 43] = [
    0, 1, 1, 1, 1, 1, 1, 2, 4, 6, 6, 7, 7, 7, 9, 10, 11, 1, 6, 13, 13, 13, 13, 0, 1, 3, 6, 7, 7, 7,
    8, 10, 11, 11, 12, 12, 12, 12, 1, 5, 6, 7, 8,
];
#[cfg(any(test, feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit"))]
const COPY_PATTERN_LOCAL_COORDINATE_LOCALS: [u8; 43] = [
    11, 2, 6, 10, 11, 12, 14, 12, 12, 1, 12, 0, 2, 4, 6, 0, 10, 11, 12, 2, 6, 10, 14, 0, 12, 12, 6,
    0, 2, 4, 7, 0, 9, 10, 1, 5, 9, 13, 12, 12, 7, 9, 6,
];
#[cfg(any(test, feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit"))]
const COPY_PATTERN_LOCAL_OUTPUT_COORDINATES: [u8; 43] = [
    0, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 5, 5, 5, 6, 7, 8, 9, 10, 11, 11, 11, 11, 12, 13, 14, 15, 16,
    16, 16, 17, 18, 19, 19, 20, 20, 20, 20, 21, 22, 23, 24, 25,
];

#[cfg(any(test, feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit"))]
const fn build_group_local_coordinates() -> [[u8; 16]; 4] {
    let mut output = [[u8::MAX; 16]; 4];
    let mut coordinate = 0usize;
    while coordinate < COPY_GROUP_LOCAL_COORDINATE_GROUPS.len() {
        output[COPY_GROUP_LOCAL_COORDINATE_GROUPS[coordinate] as usize]
            [COPY_GROUP_LOCAL_COORDINATE_LOCALS[coordinate] as usize] = coordinate as u8;
        coordinate += 1;
    }
    output
}

#[cfg(any(test, feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit"))]
const fn build_pattern_local_coordinates() -> [[[u8; 16]; 14]; 4] {
    let mut output = [[[u8::MAX; 16]; 14]; 4];
    let mut coordinate = 0usize;
    while coordinate < COPY_PATTERN_LOCAL_COORDINATE_GROUPS.len() {
        output[COPY_PATTERN_LOCAL_COORDINATE_GROUPS[coordinate] as usize]
            [COPY_PATTERN_LOCAL_COORDINATE_PATTERNS[coordinate] as usize]
            [COPY_PATTERN_LOCAL_COORDINATE_LOCALS[coordinate] as usize] = coordinate as u8;
        coordinate += 1;
    }
    output
}

#[cfg(any(test, feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit"))]
const COPY_GROUP_LOCAL_COORDINATES: [[u8; 16]; 4] = build_group_local_coordinates();
#[cfg(any(test, feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit"))]
const COPY_PATTERN_LOCAL_COORDINATES: [[[u8; 16]; 14]; 4] = build_pattern_local_coordinates();
#[cfg(any(test, feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit"))]
const COPY_SELECTOR_TENSOR_TAG_OFFSET: usize = 0;
#[cfg(any(test, feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit"))]
const COPY_SELECTOR_TENSOR_WEIGHT_OFFSET: usize = 30;
#[cfg(any(test, feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit"))]
const COPY_SELECTOR_TENSOR_PATTERN_OFFSET: usize = 60;
#[cfg(any(test, feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit"))]
const COPY_SELECTOR_TENSOR_SCRATCH: usize = 103;

#[cfg(any(test, feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit"))]
const fn build_copy_tag_coordinate_offsets() -> [u16; 31] {
    let mut counts = [0u16; 30];
    let mut link_index = 0usize;
    while link_index < constants::COPY_LINKS.len() {
        let link = constants::COPY_LINKS[link_index];
        let producer_group = link.producer.slot as usize;
        let producer_local = link.producer.row as usize & 15;
        let producer_coordinate =
            COPY_GROUP_LOCAL_COORDINATES[producer_group][producer_local] as usize;
        counts[producer_coordinate] += 1;

        let consumer_group = 2 + link.consumer.slot as usize;
        let consumer_local = link.consumer.row as usize & 15;
        let consumer_coordinate =
            COPY_GROUP_LOCAL_COORDINATES[consumer_group][consumer_local] as usize;
        counts[consumer_coordinate] += 1;
        link_index += 1;
    }
    let mut offsets = [0u16; 31];
    let mut coordinate = 0usize;
    while coordinate < counts.len() {
        offsets[coordinate + 1] = offsets[coordinate] + counts[coordinate];
        coordinate += 1;
    }
    offsets
}

#[cfg(any(test, feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit"))]
const COPY_TAG_COORDINATE_OFFSETS: [u16; 31] = build_copy_tag_coordinate_offsets();

#[cfg(any(test, feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit"))]
const fn build_copy_tag_terms() -> ([u8; 272], [u32; 272]) {
    let mut blocks = [0u8; 272];
    let mut tags = [0u32; 272];
    let mut cursors = [0u16; 30];
    let mut coordinate = 0usize;
    while coordinate < cursors.len() {
        cursors[coordinate] = COPY_TAG_COORDINATE_OFFSETS[coordinate];
        coordinate += 1;
    }

    let mut link_index = 0usize;
    while link_index < constants::COPY_LINKS.len() {
        let link = constants::COPY_LINKS[link_index];

        let producer_group = link.producer.slot as usize;
        let producer_row = link.producer.row as usize;
        let producer_coordinate =
            COPY_GROUP_LOCAL_COORDINATES[producer_group][producer_row & 15] as usize;
        let producer_output = cursors[producer_coordinate] as usize;
        blocks[producer_output] = (producer_row >> 4) as u8;
        tags[producer_output] = link.tag;
        cursors[producer_coordinate] += 1;

        let consumer_group = 2 + link.consumer.slot as usize;
        let consumer_row = link.consumer.row as usize;
        let consumer_coordinate =
            COPY_GROUP_LOCAL_COORDINATES[consumer_group][consumer_row & 15] as usize;
        let consumer_output = cursors[consumer_coordinate] as usize;
        blocks[consumer_output] = (consumer_row >> 4) as u8;
        tags[consumer_output] = link.tag;
        cursors[consumer_coordinate] += 1;

        link_index += 1;
    }
    (blocks, tags)
}

#[cfg(any(test, feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit"))]
static COPY_TAG_TERMS: ([u8; 272], [u32; 272]) = build_copy_tag_terms();

/// Evaluate one frozen Copy-tag coordinate with four-product lazy M31
/// reduction. Each raw channel is strictly below
/// `4 * (P - 1)^2 < 2^64` before reduction.
#[cfg(any(test, feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit"))]
#[inline(never)]
fn copy_tag_coordinate_dot(coordinate: usize, selectors: &Selectors) -> QM31 {
    let mut output = [M31::ZERO; 4];
    let mut index = usize::from(COPY_TAG_COORDINATE_OFFSETS[coordinate]);
    let end = usize::from(COPY_TAG_COORDINATE_OFFSETS[coordinate + 1]);
    while index < end {
        let chunk_end = core::cmp::min(index + 4, end);
        let mut raw = [0u64; 4];
        while index < chunk_end {
            let value = selectors.high[usize::from(COPY_TAG_TERMS.0[index])];
            let tag = u64::from(COPY_TAG_TERMS.1[index]);
            raw[0] += u64::from(value.c0.a.0) * tag;
            raw[1] += u64::from(value.c0.b.0) * tag;
            raw[2] += u64::from(value.c1.a.0) * tag;
            raw[3] += u64::from(value.c1.b.0) * tag;
            index += 1;
        }
        let mut limb = 0usize;
        while limb < output.len() {
            output[limb] = output[limb].add(M31::reduce_u64(raw[limb]));
            limb += 1;
        }
    }
    QM31 {
        c0: CM31::new(output[0], output[1]),
        c1: CM31::new(output[2], output[3]),
    }
}

#[cfg(any(test, feature = "pool-v1-pair-forest-copy-finish-dot-basis-audit"))]
#[inline(always)]
fn qm31_sum_products_up_to4(left: [QM31; 4], right: [QM31; 4], count: usize) -> QM31 {
    match count {
        1 => left[0].mul(right[0]),
        2 => qm31_sum_products2([left[0], left[1]], [right[0], right[1]]),
        3 => qm31_sum_products3([left[0], left[1], left[2]], [right[0], right[1], right[2]]),
        4 => qm31_sum_products4(left, right),
        _ => unreachable!("Copy finish dot batch width"),
    }
}

#[cfg(all(
    any(test, feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit"),
    not(feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit")
))]
#[inline(always)]
fn copy_tag_coordinate_value(scratch: &[QM31], coordinate: usize, _selectors: &Selectors) -> QM31 {
    scratch[COPY_SELECTOR_TENSOR_TAG_OFFSET + coordinate]
}

#[cfg(feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit")]
#[inline(always)]
fn copy_tag_coordinate_value(_scratch: &[QM31], coordinate: usize, selectors: &Selectors) -> QM31 {
    copy_tag_coordinate_dot(coordinate, selectors)
}

/// Accumulate one compiled endpoint after changing from the endpoint basis to
/// the fixed tuple-pattern basis:
///
/// `s * (tag + pattern[p]) = s * tag + pattern[p] * s`.
///
/// The first product is by an M31 value.  Dynamic QM31 pattern values are
/// multiplied only once per nonzero `(side, slot, pattern)` coordinate after
/// all 272 endpoint selectors have been collected.
#[cfg(any(test, feature = "pool-v1-pair-forest-copy-pattern-basis-audit"))]
fn accumulate_endpoint_pattern_basis(
    tag_values: &mut [QM31; 4],
    pattern_selectors: &mut [QM31; 26],
    weights: &mut [QM31; 2],
    side: usize,
    endpoint: CompiledPoolV1PairForestEndpoint,
    tag: u32,
    weight: M31,
    selectors: &Selectors,
    #[cfg(feature = "pool-v1-pair-forest-endpoint-selector-cache-audit")]
    selector_cache: &mut EndpointSelectorCache,
) {
    #[cfg(not(feature = "pool-v1-pair-forest-endpoint-selector-cache-audit"))]
    let selector = selectors.row(usize::from(endpoint.row));
    #[cfg(feature = "pool-v1-pair-forest-endpoint-selector-cache-audit")]
    let selector = selector_cache.selector(endpoint.row, selectors);
    let slot = usize::from(endpoint.slot);
    let group = side + slot;
    tag_values[group] = tag_values[group].add(selector.mul_m31(M31(tag)));
    let pattern = usize::from(endpoint.pattern);
    let coordinate = COPY_PATTERN_COORDINATES[group][pattern];
    debug_assert_ne!(coordinate, u8::MAX);
    let coordinate = usize::from(coordinate);
    pattern_selectors[coordinate] = pattern_selectors[coordinate].add(selector);
    #[cfg(not(feature = "pool-v1-pair-forest-binary-copy-weights-audit"))]
    {
        weights[slot] = weights[slot].add(selector.mul_m31(weight));
    }
    #[cfg(feature = "pool-v1-pair-forest-binary-copy-weights-audit")]
    {
        weights[slot] = add_binary_weight(weights[slot], selector, weight);
    }
}

#[cfg(any(test, feature = "pool-v1-pair-forest-copy-pattern-basis-audit"))]
fn finish_pattern_basis_values(
    mut values: [QM31; 4],
    pattern_selectors: [QM31; 26],
    patterns: &[QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1],
) -> [QM31; 4] {
    let mut group = 0usize;
    while group < values.len() {
        let mut coordinate = COPY_PATTERN_GROUP_OFFSETS[group];
        while coordinate < COPY_PATTERN_GROUP_OFFSETS[group + 1] {
            let pattern = usize::from(COPY_PATTERN_COORDINATE_PATTERNS[coordinate]);
            values[group] = values[group].add(patterns[pattern].mul(pattern_selectors[coordinate]));
            coordinate += 1;
        }
        group += 1;
    }
    values
}

#[cfg(any(test, feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit"))]
#[inline(never)]
fn selected_binary_weight(high: QM31, weight: M31) -> QM31 {
    if weight.0 == 1 {
        high
    } else {
        QM31::ZERO
    }
}

#[cfg(any(test, feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit"))]
fn accumulate_endpoint_selector_tensor_basis(
    scratch: &mut [QM31],
    side: usize,
    endpoint: CompiledPoolV1PairForestEndpoint,
    tag: u32,
    weight: M31,
    selectors: &Selectors,
) {
    let group = side + usize::from(endpoint.slot);
    let row = usize::from(endpoint.row);
    let local = row & 15;
    let high = selectors.high[row >> 4];
    let group_local = usize::from(COPY_GROUP_LOCAL_COORDINATES[group][local]);
    #[cfg(not(feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit"))]
    {
        scratch[COPY_SELECTOR_TENSOR_TAG_OFFSET + group_local] =
            scratch[COPY_SELECTOR_TENSOR_TAG_OFFSET + group_local].add(high.mul_m31(M31(tag)));
    }
    #[cfg(feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit")]
    let _ = tag;
    let weight_index = COPY_SELECTOR_TENSOR_WEIGHT_OFFSET + group_local;
    scratch[weight_index] =
        scratch[weight_index].add(selected_binary_weight(high, weight));
    let pattern_local =
        usize::from(COPY_PATTERN_LOCAL_COORDINATES[group][usize::from(endpoint.pattern)][local]);
    scratch[COPY_SELECTOR_TENSOR_PATTERN_OFFSET + pattern_local] =
        scratch[COPY_SELECTOR_TENSOR_PATTERN_OFFSET + pattern_local].add(high);
}

#[cfg(any(test, feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit"))]
fn finish_selector_tensor_basis(
    scratch: &[QM31],
    patterns: &[QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1],
    selectors: &Selectors,
) -> ([QM31; 4], [QM31; 4]) {
    let mut values = [QM31::ZERO; 4];
    let mut weights = [QM31::ZERO; 4];
    #[cfg(not(feature = "pool-v1-pair-forest-copy-finish-dot-basis-audit"))]
    {
        let mut coordinate = 0usize;
        while coordinate < COPY_GROUP_LOCAL_COORDINATE_GROUPS.len() {
            let group = usize::from(COPY_GROUP_LOCAL_COORDINATE_GROUPS[coordinate]);
            let low = selectors.low[usize::from(COPY_GROUP_LOCAL_COORDINATE_LOCALS[coordinate])];
            let tag_value = copy_tag_coordinate_value(scratch, coordinate, selectors);
            values[group] = values[group].add(tag_value.mul(low));
            weights[group] = weights[group]
                .add(scratch[COPY_SELECTOR_TENSOR_WEIGHT_OFFSET + coordinate].mul(low));
            coordinate += 1;
        }
    }
    #[cfg(feature = "pool-v1-pair-forest-copy-finish-dot-basis-audit")]
    {
        let mut group = 0usize;
        while group < values.len() {
            let end = COPY_GROUP_LOCAL_GROUP_OFFSETS[group + 1];
            let mut coordinate = COPY_GROUP_LOCAL_GROUP_OFFSETS[group];
            while coordinate < end {
                let count = core::cmp::min(4, end - coordinate);
                let tag_values: [QM31; 4] = core::array::from_fn(|index| {
                    if index < count {
                        copy_tag_coordinate_value(scratch, coordinate + index, selectors)
                    } else {
                        QM31::ZERO
                    }
                });
                let weight_values: [QM31; 4] = core::array::from_fn(|index| {
                    if index < count {
                        scratch[COPY_SELECTOR_TENSOR_WEIGHT_OFFSET + coordinate + index]
                    } else {
                        QM31::ZERO
                    }
                });
                let lows: [QM31; 4] = core::array::from_fn(|index| {
                    if index < count {
                        selectors.low
                            [usize::from(COPY_GROUP_LOCAL_COORDINATE_LOCALS[coordinate + index])]
                    } else {
                        QM31::ZERO
                    }
                });
                values[group] =
                    values[group].add(qm31_sum_products_up_to4(tag_values, lows, count));
                weights[group] =
                    weights[group].add(qm31_sum_products_up_to4(weight_values, lows, count));
                coordinate += count;
            }
            group += 1;
        }
    }
    let mut pattern_selectors = [QM31::ZERO; 26];
    let mut coordinate = 0;
    while coordinate < COPY_PATTERN_LOCAL_COORDINATE_GROUPS.len() {
        let output = usize::from(COPY_PATTERN_LOCAL_OUTPUT_COORDINATES[coordinate]);
        let low = selectors.low[usize::from(COPY_PATTERN_LOCAL_COORDINATE_LOCALS[coordinate])];
        pattern_selectors[output] = pattern_selectors[output]
            .add(scratch[COPY_SELECTOR_TENSOR_PATTERN_OFFSET + coordinate].mul(low));
        coordinate += 1;
    }
    (
        finish_pattern_basis_values(values, pattern_selectors, patterns),
        weights,
    )
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
    #[cfg(all(
        feature = "pool-v1-pair-forest-endpoint-selector-cache-audit",
        not(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")
    ))]
    let mut selector_cache = EndpointSelectorCache::new();
    #[cfg(all(
        feature = "pool-v1-pair-forest-copy-pattern-basis-audit",
        not(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")
    ))]
    let mut tag_values = [QM31::ZERO; 4];
    #[cfg(all(
        feature = "pool-v1-pair-forest-copy-pattern-basis-audit",
        not(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")
    ))]
    let mut pattern_selectors = [QM31::ZERO; 26];
    #[cfg(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")]
    let mut selector_tensor_scratch = vec![QM31::ZERO; COPY_SELECTOR_TENSOR_SCRATCH];
    let mut link_index = 0usize;
    while link_index < POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1 {
        let link = constants::COPY_LINKS[link_index];
        let weight = link_weight(link, append_index, variant);
        #[cfg(all(
            not(feature = "pool-v1-pair-forest-copy-pattern-basis-audit"),
            not(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")
        ))]
        #[cfg(not(feature = "pool-v1-pair-forest-endpoint-selector-cache-audit"))]
        {
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
        }
        #[cfg(all(
            not(feature = "pool-v1-pair-forest-copy-pattern-basis-audit"),
            not(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")
        ))]
        #[cfg(feature = "pool-v1-pair-forest-endpoint-selector-cache-audit")]
        {
            accumulate_endpoint(
                &mut row.producer_values,
                &mut row.producer_weights,
                link.producer,
                link.tag,
                weight,
                &patterns,
                selectors,
                &mut selector_cache,
            );
            accumulate_endpoint(
                &mut row.consumer_values,
                &mut row.consumer_weights,
                link.consumer,
                link.tag,
                weight,
                &patterns,
                selectors,
                &mut selector_cache,
            );
        }
        #[cfg(all(
            feature = "pool-v1-pair-forest-copy-pattern-basis-audit",
            not(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")
        ))]
        {
            accumulate_endpoint_pattern_basis(
                &mut tag_values,
                &mut pattern_selectors,
                &mut row.producer_weights,
                0,
                link.producer,
                link.tag,
                weight,
                selectors,
                #[cfg(feature = "pool-v1-pair-forest-endpoint-selector-cache-audit")]
                &mut selector_cache,
            );
            accumulate_endpoint_pattern_basis(
                &mut tag_values,
                &mut pattern_selectors,
                &mut row.consumer_weights,
                2,
                link.consumer,
                link.tag,
                weight,
                selectors,
                #[cfg(feature = "pool-v1-pair-forest-endpoint-selector-cache-audit")]
                &mut selector_cache,
            );
        }
        #[cfg(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")]
        {
            accumulate_endpoint_selector_tensor_basis(
                &mut selector_tensor_scratch,
                0,
                link.producer,
                link.tag,
                weight,
                selectors,
            );
            accumulate_endpoint_selector_tensor_basis(
                &mut selector_tensor_scratch,
                2,
                link.consumer,
                link.tag,
                weight,
                selectors,
            );
        }
        link_index += 1;
    }
    #[cfg(all(
        feature = "pool-v1-pair-forest-copy-pattern-basis-audit",
        not(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")
    ))]
    {
        let values = finish_pattern_basis_values(tag_values, pattern_selectors, &patterns);
        row.producer_values = [values[0], values[1]];
        row.consumer_values = [values[2], values[3]];
    }
    #[cfg(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")]
    {
        let (values, weights) =
            finish_selector_tensor_basis(&selector_tensor_scratch, &patterns, selectors);
        row.producer_values = [values[0], values[1]];
        row.consumer_values = [values[2], values[3]];
        row.producer_weights = [weights[0], weights[1]];
        row.consumer_weights = [weights[2], weights[3]];
    }
    let active = selectors.active();
    PoolV1PairForestCompiledCopyTerminalV1 {
        residual: active.mul(copy_residual(row, h1_z, chi)),
        active,
    }
}

/// Evaluate the exact 136-link pair-forest Copy lane from the frozen sixteen
/// merged-C1 openings and one H1 opening. This performs one fixed-size
/// selector allocation and, under the selected tensor-basis evaluator, one
/// fixed 103-QM31 scratch allocation. There is no registry- or input-dependent
/// allocation.
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
        let mut pattern_group_support = [0u16; 4];
        let mut group_local_seen = [false; 30];
        let mut pattern_local_seen = [false; 43];
        for (host, compiled) in registry.iter().zip(constants::COPY_LINKS) {
            assert_eq!(host.tag.0, compiled.tag);
            assert_eq!(
                weight_code(host.weight),
                (compiled.weight_kind, compiled.weight_level)
            );
            for (side, (tuple, arity, endpoint)) in [
                (host.producer, &mut producer_arity, compiled.producer),
                (host.consumer, &mut consumer_arity, compiled.consumer),
            ]
            .into_iter()
            .enumerate()
            {
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
                let group = 2 * side + usize::from(endpoint.slot);
                pattern_group_support[group] |= 1 << endpoint.pattern;
                let local = row & 15;
                let group_local = COPY_GROUP_LOCAL_COORDINATES[group][local];
                assert_ne!(group_local, u8::MAX);
                let group_local = usize::from(group_local);
                assert_eq!(
                    usize::from(COPY_GROUP_LOCAL_COORDINATE_GROUPS[group_local]),
                    group
                );
                assert_eq!(
                    usize::from(COPY_GROUP_LOCAL_COORDINATE_LOCALS[group_local]),
                    local
                );
                group_local_seen[group_local] = true;
                let pattern_local =
                    COPY_PATTERN_LOCAL_COORDINATES[group][usize::from(endpoint.pattern)][local];
                assert_ne!(pattern_local, u8::MAX);
                let pattern_local = usize::from(pattern_local);
                assert_eq!(
                    usize::from(COPY_PATTERN_LOCAL_COORDINATE_GROUPS[pattern_local]),
                    group
                );
                assert_eq!(
                    COPY_PATTERN_LOCAL_COORDINATE_PATTERNS[pattern_local],
                    endpoint.pattern
                );
                assert_eq!(
                    usize::from(COPY_PATTERN_LOCAL_COORDINATE_LOCALS[pattern_local]),
                    local
                );
                assert_eq!(
                    COPY_PATTERN_LOCAL_OUTPUT_COORDINATES[pattern_local],
                    COPY_PATTERN_COORDINATES[group][usize::from(endpoint.pattern)]
                );
                pattern_local_seen[pattern_local] = true;
            }
        }
        assert_eq!(active_masks, constants::ACTIVE_ROW_MASKS);
        assert_eq!(pattern_group_support, COPY_PATTERN_GROUP_SUPPORT);
        assert!(group_local_seen.into_iter().all(core::convert::identity));
        assert!(pattern_local_seen.into_iter().all(core::convert::identity));
        assert_eq!(
            PINNED_POOL_V1_PAIR_FOREST_COPY_TERMINAL_ACTIVE_ROWS_FINGERPRINT_V1,
            0xdf39_4a5a_8554_d09c,
        );
    }

    #[test]
    fn every_generated_copy_weight_is_binary_and_skip_add_is_exact() {
        let mut rng = Rng(0x6269_6e61_7279_7731);
        for variant in [
            PoolV1PairForestCompiledVariantV1::PrivateTransfer,
            PoolV1PairForestCompiledVariantV1::Withdrawal,
        ] {
            for append_index in [0, 13, 0x5_5555, 0xa_aaaa, (1 << 20) - 1] {
                for link in constants::COPY_LINKS {
                    let weight = link_weight(link, append_index, variant);
                    assert!(weight == M31::ZERO || weight == M31::ONE);
                    let sum = rng.qm31();
                    let selector = rng.qm31();
                    assert_eq!(
                        add_binary_weight(sum, selector, weight),
                        sum.add(selector.mul_m31(weight)),
                    );
                }
            }
        }
    }

    fn assert_endpoint_selector_cache_matches_literal(selectors: &Selectors) {
        let mut cache = EndpointSelectorCache::new();
        for link in constants::COPY_LINKS {
            for endpoint in [link.producer, link.consumer] {
                assert_eq!(
                    cache.selector(endpoint.row, selectors),
                    selectors.row(usize::from(endpoint.row)),
                );
            }
        }
    }

    #[test]
    fn endpoint_selector_cache_matches_every_generated_endpoint_exactly() {
        let mut expected_hits = 0usize;
        let mut row_tags = [u16::MAX; 32];
        for link in constants::COPY_LINKS {
            for endpoint in [link.producer, link.consumer] {
                let slot = usize::from(endpoint.row) & (row_tags.len() - 1);
                if row_tags[slot] == endpoint.row {
                    expected_hits += 1;
                } else {
                    row_tags[slot] = endpoint.row;
                }
            }
        }
        assert_eq!(expected_hits, 56);

        for selected_row in 0..POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1 {
            let mut high = [QM31::ZERO; 64];
            let mut low = [QM31::ZERO; 16];
            high[selected_row >> 4] = QM31::ONE;
            low[selected_row & 15] = QM31::ONE;
            assert_endpoint_selector_cache_matches_literal(&Selectors { high, low });
        }

        let mut rng = Rng(0x7365_6c65_6374_6f72);
        for _ in 0..64 {
            let point = core::array::from_fn(|_| rng.qm31());
            assert_endpoint_selector_cache_matches_literal(&Selectors::at_point(&point));
        }
    }

    #[test]
    fn windowed_copy_patterns_equal_literal_off_domain() {
        let mut rng = Rng(0x7061_7474_6572_6e31);
        for sample in 0..256 {
            let openings = core::array::from_fn(|_| rng.qm31());
            let lambda = rng.qm31();
            assert_eq!(
                pattern_values_windowed(&openings, lambda),
                pattern_values_literal(&openings, lambda),
                "generated pattern mismatch at sample {sample}",
            );
        }
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
    fn active_mask_basis_matches_literal_off_domain() {
        let mut rng = Rng(0x6163_7469_7665_7631);
        for sample in 0..128 {
            let point = core::array::from_fn(|_| rng.qm31());
            let selectors = Selectors::at_point(&point);
            assert_eq!(
                selectors.active_mask_basis(),
                selectors.active_literal(),
                "active selector basis mismatch at sample {sample}"
            );
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
