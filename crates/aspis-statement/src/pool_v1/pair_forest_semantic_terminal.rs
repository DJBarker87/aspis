//! Allocation-bounded selected terminal for the eight-lane Pool V1 pair
//! forest. The relation keeps the frozen Tag-73 three-opening geometry and
//! packs Poseidon, 94 semantic source lanes and the 136-link Copy argument
//! into the same 29 theta lanes as the one-tree payment terminal.

use aspis_core::{
    field::{qm31_pack_base4, PreparedQm31Multiplier, CM31, M31, QM31},
    state_only_hiding::{state_only_selected_mask_value, STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS},
};

use crate::{
    poseidon2::{Digest, DIGEST_ELEMS, MERKLE_NODE_COMPRESSION_V3_TWEAK, POSEIDON2_WIDTH, RATE},
    spend::{DOMAIN_NOTE, DOMAIN_NULLIFIER, DOMAIN_OWNER_KEY},
    state_only_poseidon::{
        evaluate_state_only_poseidon_oracle_projected, StateOnlyPoseidonOpenings,
        StateOnlyPoseidonSelectors,
    },
};

use super::{
    pair_forest_copy_terminal::{
        evaluate_with_selectors, PoolV1PairForestCompiledVariantV1, Selectors,
    },
    pair_tree_profile::{PoolV1PairLatePublicStatementV1, POOL_V1_PAIR_CAPACITY},
    payment_relation::{PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1},
};

pub const POOL_V1_PAIR_FOREST_TERMINAL_ROWS_V1: usize = 1024;
pub const POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1: usize = 16;
pub const POOL_V1_PAIR_FOREST_TERMINAL_POINTS_V1: usize = 3;
pub const POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1: usize =
    POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + 2;
pub const POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1: usize =
    POOL_V1_PAIR_FOREST_TERMINAL_POINTS_V1 * POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1;
pub const POOL_V1_PAIR_FOREST_SOURCE_SEMANTIC_LANES_V1: usize = 94;
pub const POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1: usize = 24;
pub const POOL_V1_PAIR_FOREST_POSEIDON_LANES_V1: usize = 4;
pub const POOL_V1_PAIR_FOREST_COPY_LANES_V1: usize = 1;
pub const POOL_V1_PAIR_FOREST_THETA_LANES_V1: usize = POOL_V1_PAIR_FOREST_POSEIDON_LANES_V1
    + POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1
    + POOL_V1_PAIR_FOREST_COPY_LANES_V1;
pub const POOL_V1_PAIR_FOREST_THETA_COLLISION_DEGREE_V1: usize =
    POOL_V1_PAIR_FOREST_THETA_LANES_V1 - 1;
pub const POOL_V1_PAIR_FOREST_SEMANTIC_ORACLE_INDIVIDUAL_DEGREE_V1: usize = 26;
pub const POOL_V1_PAIR_FOREST_SEMANTIC_ZEROCHECK_INDIVIDUAL_DEGREE_V1: usize = 27;
pub const POOL_V1_PAIR_FOREST_MASKED_TERMINAL_DEGREE_V1: usize = 27;
pub const POOL_V1_PAIR_FOREST_TERMINAL_FIXED_HEAP_ALLOCATIONS_V1: usize = 1;
pub const POOL_V1_PAIR_FOREST_TERMINAL_SELECTOR_HEAP_BYTES_V1: usize =
    core::mem::size_of::<Selectors>();

const SELECTED_H1_COLUMN: usize =
    POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
const SELECTED_G_COLUMN: usize = SELECTED_H1_COLUMN + 1;
const VALUE_AUXILIARY_BLOCK: usize = 63;
const INPUT_OCCUPANCY_ROW: usize = 63 * 16 + 9;
const OUTPUT_OCCUPANCY_ROW: usize = 63 * 16 + 10;

const _: () = assert!(DIGEST_ELEMS == 8);
const _: () = assert!(POSEIDON2_WIDTH == 16);
const _: () = assert!(POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 == 28);
const _: () = assert!(POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1 == 84);
const _: () = assert!(POOL_V1_PAIR_FOREST_THETA_LANES_V1 == 29);
const _: () = assert!(POOL_V1_PAIR_FOREST_THETA_COLLISION_DEGREE_V1 == 28);

mod constants {
    include!("pair_forest_semantic_terminal_constants.rs");
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairForestSemanticTerminalErrorV1 {
    InvalidPublicAmount,
    InvalidAppendTransition,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CompiledVariant {
    PrivateTransfer,
    Withdrawal,
}

#[derive(Clone, Copy)]
struct SemanticPublic<'a> {
    variant: CompiledVariant,
    pool: [u8; 32],
    deployment_domain: [u8; 32],
    anchor: Digest,
    nullifier: Digest,
    asset_id: M31,
    recipient: Option<Digest>,
    change: Digest,
    withdrawal_amount: Option<u32>,
    transition: &'a PoolV1PairLatePublicStatementV1,
}

#[inline(always)]
fn lift(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}

#[inline(always)]
fn add_preweighted<const N: usize>(
    packed: &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
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
fn sum_high(selectors: &Selectors, ranges: &[core::ops::Range<usize>]) -> QM31 {
    let mut sum = QM31::ZERO;
    for range in ranges {
        for block in range.clone() {
            sum = sum.add(selectors.high[block]);
        }
    }
    sum
}

#[inline(always)]
fn reconstruct_10(view: &[QM31; 16]) -> QM31 {
    view[..9]
        .iter()
        .rev()
        .fold(view[9], |acc, bit| acc.add(acc).add(*bit))
}

#[inline(always)]
fn empty_root(level: usize) -> Digest {
    constants::POOL_V1_PAIR_EMPTY_ROOTS_V1[level].map(M31)
}

fn validate_transition(
    public: SemanticPublic<'_>,
) -> Result<(), PoolV1PairForestSemanticTerminalErrorV1> {
    let source = public.transition.live_snapshot;
    let after = public.transition.candidate_afterstate;
    if source.pool != public.pool
        || source.deployment_domain != public.deployment_domain
        || source.sequence != source.next_pair_index
        || source.next_pair_index >= POOL_V1_PAIR_CAPACITY
        || source.next_pair_index.checked_add(1) != Some(after.next_pair_index)
    {
        return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidAppendTransition);
    }
    let index = source.next_pair_index;
    let carry = core::cmp::min(index.trailing_ones() as usize, 20);
    for level in 0..20 {
        if level == carry && carry < 20 {
            continue;
        }
        let expected = if level < carry || ((index >> level) & 1) == 0 {
            empty_root(level)
        } else {
            source.frontier[level]
        };
        if after.next_frontier[level] != expected {
            return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidAppendTransition);
        }
    }
    Ok(())
}

fn poseidon_selectors(selectors: &Selectors) -> StateOnlyPoseidonSelectors {
    StateOnlyPoseidonSelectors {
        block: sum_high(selectors, &[0..57]),
        local: selectors.low,
    }
}

fn semantic_initial_and_absorption(
    public: SemanticPublic<'_>,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) -> ([QM31; 16], [QM31; 16]) {
    let nodes = sum_high(selectors, &[4..25, 33..57]);
    let first_common = selectors.high[0]
        .add(selectors.high[1])
        .add(selectors.high[25])
        .add(selectors.high[30]);
    let transfer_first = if public.variant == CompiledVariant::PrivateTransfer {
        selectors.high[27]
    } else {
        QM31::ZERO
    };
    let fixed = if public.variant == CompiledVariant::Withdrawal {
        selectors.high[27]
            .add(selectors.high[28])
            .add(selectors.high[29])
    } else {
        QM31::ZERO
    };
    let full_initial_selector = selectors.low[0].mul(first_common.add(transfer_first).add(fixed));
    let rate_initial_selector = selectors.low[0].mul(nodes);
    let full = PreparedQm31Multiplier::new(full_initial_selector);
    let full_or_rate =
        PreparedQm31Multiplier::new(full_initial_selector.add(rate_initial_selector));
    let mut initial = core::array::from_fn(|lane| {
        if lane < RATE {
            full_or_rate.mul(openings.z[lane])
        } else {
            full.mul(openings.z[lane])
        }
    });
    let note_first = selectors.high[1]
        .add(selectors.high[30])
        .add(transfer_first);
    let domain = selectors.high[0]
        .mul_m31(DOMAIN_OWNER_KEY)
        .add(note_first.mul_m31(DOMAIN_NOTE))
        .add(selectors.high[25].mul_m31(DOMAIN_NULLIFIER));
    let length = selectors.high[0]
        .mul_m31(M31(8))
        .add(note_first.mul_m31(M31(18)))
        .add(selectors.high[25].mul_m31(M31(16)));
    initial[RATE] = initial[RATE].sub(selectors.low[0].mul(domain));
    initial[RATE + 1] = initial[RATE + 1].sub(selectors.low[0].mul(length));

    let mut chunk_eight = selectors.high[0]
        .add(selectors.high[1])
        .add(selectors.high[2])
        .add(selectors.high[25])
        .add(selectors.high[26])
        .add(selectors.high[30])
        .add(selectors.high[31]);
    let mut chunk_two = selectors.high[3].add(selectors.high[32]);
    if public.variant == CompiledVariant::PrivateTransfer {
        chunk_eight = chunk_eight.add(selectors.high[27]).add(selectors.high[28]);
        chunk_two = chunk_two.add(selectors.high[29]);
    }
    #[cfg(not(feature = "pool-v1-pair-forest-semantic-factor-audit"))]
    let absorption = absorption_lanes_literal(
        selectors.low[12],
        fixed,
        chunk_two,
        chunk_eight,
        nodes,
        &openings.z,
    );
    #[cfg(feature = "pool-v1-pair-forest-semantic-factor-audit")]
    let absorption = absorption_lanes_factored(
        selectors.low[12],
        fixed,
        chunk_two,
        chunk_eight,
        nodes,
        &openings.z,
    );
    (initial, absorption)
}

#[cfg(any(test, not(feature = "pool-v1-pair-forest-semantic-factor-audit")))]
fn absorption_lanes_literal(
    low: QM31,
    fixed: QM31,
    chunk_two: QM31,
    chunk_eight: QM31,
    nodes: QM31,
    openings: &[QM31; 16],
) -> [QM31; 16] {
    core::array::from_fn(|lane| {
        let blocks = if lane < 2 {
            fixed
        } else if lane < RATE {
            fixed.add(chunk_two)
        } else {
            fixed.add(chunk_two).add(chunk_eight).add(nodes)
        };
        low.mul(blocks).mul(openings[lane])
    })
}

#[cfg(any(test, feature = "pool-v1-pair-forest-semantic-factor-audit"))]
fn absorption_lanes_factored(
    low: QM31,
    fixed: QM31,
    chunk_two: QM31,
    chunk_eight: QM31,
    nodes: QM31,
    openings: &[QM31; 16],
) -> [QM31; 16] {
    let scales = [
        PreparedQm31Multiplier::new(low.mul(fixed)),
        PreparedQm31Multiplier::new(low.mul(fixed.add(chunk_two))),
        PreparedQm31Multiplier::new(low.mul(fixed.add(chunk_two).add(chunk_eight).add(nodes))),
    ];
    core::array::from_fn(|lane| {
        let scale = if lane < 2 {
            scales[0]
        } else if lane < RATE {
            scales[1]
        } else {
            scales[2]
        };
        scale.mul(openings[lane])
    })
}

#[inline(always)]
#[cfg(any(test, not(feature = "pool-v1-pair-forest-packed-digest-audit")))]
fn add_digest_binding(
    output: &mut [QM31; DIGEST_ELEMS],
    selector: QM31,
    opened: &[QM31; POSEIDON2_WIDTH],
    start: usize,
    expected: &Digest,
    right_tweak: bool,
) {
    for lane in 0..DIGEST_ELEMS {
        let mut target = expected[lane];
        if right_tweak && lane + 1 == DIGEST_ELEMS {
            target = target.add(MERKLE_NODE_COMPRESSION_V3_TWEAK);
        }
        output[lane] = output[lane].add(selector.mul(opened[start + lane].sub(lift(target))));
    }
}

#[inline(never)]
fn add_schedule_lanes(
    packed: &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
    public: SemanticPublic<'_>,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) {
    let (initial, absorption) = semantic_initial_and_absorption(public, openings, selectors);
    add_preweighted(packed, 0, &initial);
    add_preweighted(packed, 16, &absorption);
}

#[inline(never)]
fn add_path_lanes(
    packed: &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) {
    let path_selector = sum_high(selectors, &[57..63]).mul(
        selectors.low[1]
            .add(selectors.low[5])
            .add(selectors.low[9])
            .add(selectors.low[13]),
    );
    #[cfg(not(feature = "pool-v1-pair-forest-semantic-factor-audit"))]
    let path = path_lanes_literal(path_selector, openings);
    #[cfg(feature = "pool-v1-pair-forest-semantic-factor-audit")]
    let path = path_lanes_factored(path_selector, openings);
    add_preweighted(packed, 32, &path);
}

#[cfg(any(test, not(feature = "pool-v1-pair-forest-semantic-factor-audit")))]
fn path_lanes_literal(path_selector: QM31, openings: &StateOnlyPoseidonOpenings) -> [QM31; 17] {
    let bit = openings.z[0];
    let mut path = [QM31::ZERO; 17];
    path[0] = path_selector.mul(bit.mul(bit.sub(QM31::ONE)));
    for lane in 0..DIGEST_ELEMS {
        let current = openings.z[1 + lane];
        path[1 + lane] = path_selector
            .mul(QM31::ONE.sub(bit))
            .mul(openings.succ_z[lane].sub(current));
        path[1 + DIGEST_ELEMS + lane] = path_selector
            .mul(bit)
            .mul(openings.succ_z[RATE + lane].sub(current));
    }
    path
}

#[cfg(any(test, feature = "pool-v1-pair-forest-semantic-factor-audit"))]
fn path_lanes_factored(path_selector: QM31, openings: &StateOnlyPoseidonOpenings) -> [QM31; 17] {
    let bit = openings.z[0];
    let selected_bit = path_selector.mul(bit);
    let selected_empty = path_selector.sub(selected_bit);
    let left = PreparedQm31Multiplier::new(selected_empty);
    let right = PreparedQm31Multiplier::new(selected_bit);
    let mut path = [QM31::ZERO; 17];
    path[0] = selected_bit.mul(bit.sub(QM31::ONE));
    for lane in 0..DIGEST_ELEMS {
        let current = openings.z[1 + lane];
        path[1 + lane] = left.mul(openings.succ_z[lane].sub(current));
        path[1 + DIGEST_ELEMS + lane] = right.mul(openings.succ_z[RATE + lane].sub(current));
    }
    path
}

#[inline(never)]
fn add_value_lanes(
    packed: &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) {
    let value_selectors =
        [0usize, 2, 4].map(|local| selectors.row(16 * VALUE_AUXILIARY_BLOCK + local));
    let range_selector = value_selectors.iter().copied().fold(QM31::ZERO, QM31::add);
    let views = [&openings.z, &openings.succ_z, &openings.xor12_z];
    let mut range = [QM31::ZERO; 33];
    for (view, values) in views.into_iter().zip(range[..30].chunks_mut(10)) {
        for index in 0..10 {
            values[index] = range_selector.mul(view[index].square().sub(view[index]));
        }
    }
    let reconstructed = reconstruct_10(&openings.z)
        .add(reconstruct_10(&openings.succ_z).mul_m31(M31(1 << 10)))
        .add(reconstruct_10(&openings.xor12_z).mul_m31(M31(1 << 20)));
    range[30] = range_selector.mul(openings.z[10].sub(reconstructed));
    range[31] = range_selector.mul(openings.succ_z[10]);
    range[32] = range_selector.mul(openings.xor12_z[10]);
    add_preweighted(packed, 49, &range);

    let conservation_selector = selectors.row(16 * VALUE_AUXILIARY_BLOCK + 6);
    let conservation = [
        conservation_selector.mul(openings.z[0].sub(openings.z[1]).sub(openings.z[2])),
        conservation_selector.mul(openings.succ_z[0].sub(openings.succ_z[1])),
    ];
    add_preweighted(packed, 82, &conservation);
}

#[inline(never)]
fn add_occupancy_lanes(
    packed: &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
    public: SemanticPublic<'_>,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) {
    let input_occupancy = selectors.row(INPUT_OCCUPANCY_ROW);
    let output_occupancy = selectors.row(OUTPUT_OCCUPANCY_ROW);
    let expected_output = M31(u32::from(
        public.variant == CompiledVariant::PrivateTransfer,
    ));
    #[cfg(not(feature = "pool-v1-pair-forest-semantic-factor-audit"))]
    let occupancy = occupancy_lanes_literal(
        input_occupancy,
        output_occupancy,
        expected_output,
        &openings.z,
    );
    #[cfg(feature = "pool-v1-pair-forest-semantic-factor-audit")]
    let occupancy = occupancy_lanes_factored(
        input_occupancy,
        output_occupancy,
        expected_output,
        &openings.z,
    );
    add_preweighted(packed, 0, &occupancy);
}

#[cfg(any(test, not(feature = "pool-v1-pair-forest-semantic-factor-audit")))]
fn occupancy_lanes_literal(
    input_occupancy: QM31,
    output_occupancy: QM31,
    expected_output: M31,
    opened: &[QM31; 16],
) -> [QM31; 12] {
    let occupied = opened[0];
    let inverse = opened[1];
    let one_minus = QM31::ONE.sub(occupied);
    let mut occupancy = [QM31::ZERO; 12];
    let both = input_occupancy.add(output_occupancy);
    occupancy[0] = both.mul(occupied.mul(occupied.sub(QM31::ONE)));
    occupancy[1] = both.mul(opened[9].mul(inverse).sub(occupied));
    occupancy[2] = both.mul(one_minus.mul(inverse));
    for lane in 0..DIGEST_ELEMS {
        occupancy[3 + lane] = both.mul(one_minus.mul(opened[2 + lane]));
    }
    occupancy[11] = input_occupancy
        .mul(opened[10].mul(one_minus))
        .add(output_occupancy.mul(occupied.sub(lift(expected_output))));
    occupancy
}

#[cfg(any(test, feature = "pool-v1-pair-forest-semantic-factor-audit"))]
fn occupancy_lanes_factored(
    input_occupancy: QM31,
    output_occupancy: QM31,
    expected_output: M31,
    opened: &[QM31; 16],
) -> [QM31; 12] {
    let occupied = opened[0];
    let inverse = opened[1];
    let one_minus = QM31::ONE.sub(occupied);
    let both = input_occupancy.add(output_occupancy);
    let occupied_selector = both.mul(occupied);
    let empty_selector = both.sub(occupied_selector);
    let empty = PreparedQm31Multiplier::new(empty_selector);
    let mut occupancy = [QM31::ZERO; 12];
    occupancy[0] = occupied_selector.mul(occupied.sub(QM31::ONE));
    occupancy[1] = both.mul(opened[9].mul(inverse).sub(occupied));
    occupancy[2] = empty.mul(inverse);
    for lane in 0..DIGEST_ELEMS {
        occupancy[3 + lane] = empty.mul(opened[2 + lane]);
    }
    occupancy[11] = input_occupancy
        .mul(opened[10].mul(one_minus))
        .add(output_occupancy.mul(occupied.sub(lift(expected_output))));
    occupancy
}

#[inline(never)]
#[cfg(any(test, not(feature = "pool-v1-pair-forest-packed-digest-audit")))]
fn public_digest_lanes(
    public: SemanticPublic<'_>,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) -> [QM31; DIGEST_ELEMS] {
    let mut digests = [QM31::ZERO; DIGEST_ELEMS];
    add_digest_binding(
        &mut digests,
        selectors.row(56 * 16 + 11),
        &openings.z,
        0,
        &public.anchor,
        false,
    );
    add_digest_binding(
        &mut digests,
        selectors.row(26 * 16 + 11),
        &openings.z,
        0,
        &public.nullifier,
        false,
    );
    if let Some(recipient) = public.recipient {
        add_digest_binding(
            &mut digests,
            selectors.row(29 * 16 + 11),
            &openings.z,
            0,
            &recipient,
            false,
        );
    }
    add_digest_binding(
        &mut digests,
        selectors.row(32 * 16 + 11),
        &openings.z,
        0,
        &public.change,
        false,
    );

    let source = public.transition.live_snapshot;
    let after = public.transition.candidate_afterstate;
    for level in 0..20 {
        let block = 34 + level;
        if ((source.next_pair_index >> level) & 1) == 0 {
            add_digest_binding(
                &mut digests,
                selectors.row(block * 16),
                &openings.z,
                RATE,
                &empty_root(level),
                true,
            );
        } else {
            add_digest_binding(
                &mut digests,
                selectors.row(block * 16 + 12),
                &openings.z,
                0,
                &source.frontier[level],
                false,
            );
        }
    }
    add_digest_binding(
        &mut digests,
        selectors.row(53 * 16 + 11),
        &openings.z,
        0,
        &after.next_root,
        false,
    );
    let carry = core::cmp::min(source.next_pair_index.trailing_ones() as usize, 20);
    if carry < 20 {
        add_digest_binding(
            &mut digests,
            selectors.row((33 + carry) * 16 + 11),
            &openings.z,
            0,
            &after.next_frontier[carry],
            false,
        );
    }
    digests
}

/// Audit-only form of `public_digest_lanes` after applying the exact identity
///
/// `pack(s * d0, ..., s * d3) = s * pack(d0, ..., d3)`.
///
/// The two outputs are the unchanged semantic theta lanes 21 and 22.  Keeping
/// the literal evaluator above available to tests makes the source-level
/// equivalence executable for both variants and every selector point.
#[cfg(any(test, feature = "pool-v1-pair-forest-packed-digest-audit"))]
#[inline(always)]
fn add_digest_binding_packed(
    output: &mut [QM31; DIGEST_ELEMS / 4],
    selector: QM31,
    opened: &[QM31; POSEIDON2_WIDTH],
    start: usize,
    expected: &Digest,
    right_tweak: bool,
) {
    for group in 0..DIGEST_ELEMS / 4 {
        let residuals: [QM31; 4] = core::array::from_fn(|slot| {
            let lane = 4 * group + slot;
            let mut target = expected[lane];
            if right_tweak && lane + 1 == DIGEST_ELEMS {
                target = target.add(MERKLE_NODE_COMPRESSION_V3_TWEAK);
            }
            opened[start + lane].sub(lift(target))
        });
        output[group] = output[group].add(selector.mul(qm31_pack_base4(&residuals)));
    }
}

#[cfg(any(test, feature = "pool-v1-pair-forest-packed-digest-audit"))]
#[inline(never)]
fn public_digest_packed(
    public: SemanticPublic<'_>,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) -> [QM31; DIGEST_ELEMS / 4] {
    let mut digests = [QM31::ZERO; DIGEST_ELEMS / 4];
    add_digest_binding_packed(
        &mut digests,
        selectors.row(56 * 16 + 11),
        &openings.z,
        0,
        &public.anchor,
        false,
    );
    add_digest_binding_packed(
        &mut digests,
        selectors.row(26 * 16 + 11),
        &openings.z,
        0,
        &public.nullifier,
        false,
    );
    if let Some(recipient) = public.recipient {
        add_digest_binding_packed(
            &mut digests,
            selectors.row(29 * 16 + 11),
            &openings.z,
            0,
            &recipient,
            false,
        );
    }
    add_digest_binding_packed(
        &mut digests,
        selectors.row(32 * 16 + 11),
        &openings.z,
        0,
        &public.change,
        false,
    );

    let source = public.transition.live_snapshot;
    let after = public.transition.candidate_afterstate;
    for level in 0..20 {
        let block = 34 + level;
        if ((source.next_pair_index >> level) & 1) == 0 {
            add_digest_binding_packed(
                &mut digests,
                selectors.row(block * 16),
                &openings.z,
                RATE,
                &empty_root(level),
                true,
            );
        } else {
            add_digest_binding_packed(
                &mut digests,
                selectors.row(block * 16 + 12),
                &openings.z,
                0,
                &source.frontier[level],
                false,
            );
        }
    }
    add_digest_binding_packed(
        &mut digests,
        selectors.row(53 * 16 + 11),
        &openings.z,
        0,
        &after.next_root,
        false,
    );
    let carry = core::cmp::min(source.next_pair_index.trailing_ones() as usize, 20);
    if carry < 20 {
        add_digest_binding_packed(
            &mut digests,
            selectors.row((33 + carry) * 16 + 11),
            &openings.z,
            0,
            &after.next_frontier[carry],
            false,
        );
    }
    digests
}

#[inline(never)]
fn add_scalar_lanes(
    packed: &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
    public: SemanticPublic<'_>,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) {
    let withdrawal_value_selector = selectors.row(16 * VALUE_AUXILIARY_BLOCK + 2);
    let input_asset = selectors
        .row(2 * 16 + 12)
        .mul(openings.z[1].sub(lift(public.asset_id)));
    let mut output_scalar = selectors
        .row(31 * 16 + 12)
        .mul(openings.z[1].sub(lift(public.asset_id)));
    match (public.variant, public.withdrawal_amount) {
        (CompiledVariant::PrivateTransfer, _) => {
            output_scalar = output_scalar.add(
                selectors
                    .row(28 * 16 + 12)
                    .mul(openings.z[1].sub(lift(public.asset_id))),
            );
        }
        (CompiledVariant::Withdrawal, Some(amount)) => {
            output_scalar = output_scalar
                .add(withdrawal_value_selector.mul(openings.z[10].sub(lift(M31(amount)))));
        }
        (CompiledVariant::Withdrawal, None) => {}
    }
    add_preweighted(packed, 92, &[input_asset, output_scalar]);
}

fn semantic_packed(
    public: SemanticPublic<'_>,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) -> [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1] {
    let mut packed = [QM31::ZERO; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1];
    add_schedule_lanes(&mut packed, public, openings, selectors);
    add_path_lanes(&mut packed, openings, selectors);
    add_value_lanes(&mut packed, openings, selectors);
    add_occupancy_lanes(&mut packed, public, openings, selectors);
    #[cfg(not(feature = "pool-v1-pair-forest-packed-digest-audit"))]
    add_preweighted(
        &mut packed,
        84,
        &public_digest_lanes(public, openings, selectors),
    );
    #[cfg(feature = "pool-v1-pair-forest-packed-digest-audit")]
    {
        let digests = public_digest_packed(public, openings, selectors);
        packed[84 / 4] = packed[84 / 4].add(digests[0]);
        packed[84 / 4 + 1] = packed[84 / 4 + 1].add(digests[1]);
    }
    add_scalar_lanes(&mut packed, public, openings, selectors);
    packed
}

fn selected_claim(
    claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
    point: usize,
    column: usize,
) -> QM31 {
    claims[point * POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 + column]
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
    public: SemanticPublic<'_>,
    claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
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
    PoolV1PairForestSemanticTerminalErrorV1,
> {
    if public
        .withdrawal_amount
        .is_some_and(|amount| amount == 0 || amount >= (1 << 30))
    {
        return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidPublicAmount);
    }
    validate_transition(public)?;
    let openings = StateOnlyPoseidonOpenings {
        z: core::array::from_fn(|column| selected_claim(claims, 0, column)),
        succ_z: core::array::from_fn(|column| selected_claim(claims, 1, column)),
        xor12_z: core::array::from_fn(|column| selected_claim(claims, 2, column)),
    };
    let mask_only = core::array::from_fn(|column| {
        selected_claim(
            claims,
            0,
            POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 + column,
        )
    });
    let selectors = Selectors::boxed_at_point(point);
    let poseidon =
        evaluate_state_only_poseidon_oracle_projected(&openings, &poseidon_selectors(&selectors));
    let semantic = semantic_packed(public, &openings, &selectors);
    let h1_z = selected_claim(claims, 0, SELECTED_H1_COLUMN);
    let copy = evaluate_with_selectors(
        &openings.z,
        h1_z,
        &selectors,
        lambda,
        chi,
        public.transition.live_snapshot.next_pair_index,
        match public.variant {
            CompiledVariant::PrivateTransfer => PoolV1PairForestCompiledVariantV1::PrivateTransfer,
            CompiledVariant::Withdrawal => PoolV1PairForestCompiledVariantV1::Withdrawal,
        },
    );
    let prepared_theta = PreparedQm31Multiplier::new(theta);
    let mut composition = copy.residual;
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
        copy.active,
    ))
}

fn terminal_parts(
    public: SemanticPublic<'_>,
    claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
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
    PoolV1PairForestSemanticTerminalErrorV1,
> {
    let (composition, c1, mask_only, g, h1_z, copy_active) =
        composition_parts(public, claims, point, lambda, chi, theta)?;
    let original = equality_value(zerocheck_point, point)
        .mul(composition)
        .add(mu.mul(h1_z))
        .add(mu.mul(mu).mul(QM31::ONE.sub(copy_active).mul(h1_z)));
    Ok((original, c1, mask_only, g))
}

fn private_public<'a>(
    public: &PoolV1PrivateTransferPublicV1,
    transition: &'a PoolV1PairLatePublicStatementV1,
) -> SemanticPublic<'a> {
    SemanticPublic {
        variant: CompiledVariant::PrivateTransfer,
        pool: public.pool,
        deployment_domain: public.deployment_domain,
        anchor: public.anchor_root,
        nullifier: public.nullifier,
        asset_id: public.asset_id,
        recipient: Some(public.recipient_commitment),
        change: public.change_commitment,
        withdrawal_amount: None,
        transition,
    }
}

fn withdrawal_public<'a>(
    public: &PoolV1WithdrawalPublicV1,
    transition: &'a PoolV1PairLatePublicStatementV1,
) -> SemanticPublic<'a> {
    SemanticPublic {
        variant: CompiledVariant::Withdrawal,
        pool: public.pool,
        deployment_domain: public.deployment_domain,
        anchor: public.anchor_root,
        nullifier: public.nullifier,
        asset_id: public.asset_id,
        recipient: None,
        change: public.change_commitment,
        withdrawal_amount: Some(public.amount),
        transition,
    }
}

macro_rules! define_variant_terminal {
    ($composition:ident, $unmasked:ident, $masked:ident, $public_ty:ty, $convert:ident) => {
        #[allow(clippy::too_many_arguments)]
        pub fn $composition(
            public: &$public_ty,
            transition: &PoolV1PairLatePublicStatementV1,
            claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
            point: &[QM31; 10],
            lambda: QM31,
            chi: QM31,
            theta: QM31,
        ) -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
            Ok(composition_parts(
                $convert(public, transition),
                claims,
                point,
                lambda,
                chi,
                theta,
            )?
            .0)
        }

        #[allow(clippy::too_many_arguments)]
        pub fn $unmasked(
            public: &$public_ty,
            transition: &PoolV1PairLatePublicStatementV1,
            claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
            point: &[QM31; 10],
            lambda: QM31,
            chi: QM31,
            theta: QM31,
            zerocheck_point: &[QM31; 10],
            mu: QM31,
        ) -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
            Ok(terminal_parts(
                $convert(public, transition),
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
            transition: &PoolV1PairLatePublicStatementV1,
            claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
            point: &[QM31; 10],
            lambda: QM31,
            chi: QM31,
            theta: QM31,
            zerocheck_point: &[QM31; 10],
            mu: QM31,
            eta: QM31,
        ) -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
            let (original, c1, mask_only, g) = terminal_parts(
                $convert(public, transition),
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
    evaluate_pool_v1_pair_forest_private_transfer_selected_constraint_composition_compiled_v1,
    evaluate_pool_v1_pair_forest_private_transfer_selected_unmasked_terminal_compiled_tag73_v1,
    evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1,
    PoolV1PrivateTransferPublicV1,
    private_public
);

define_variant_terminal!(
    evaluate_pool_v1_pair_forest_withdrawal_selected_constraint_composition_compiled_v1,
    evaluate_pool_v1_pair_forest_withdrawal_selected_unmasked_terminal_compiled_tag73_v1,
    evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1,
    PoolV1WithdrawalPublicV1,
    withdrawal_public
);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        pool_v1::{
            build_pool_v1_pair_forest_copy_helper_v1,
            pair_forest_trace::{
                compile_pool_v1_pair_forest_private_transfer_merged_c1_v1,
                compile_pool_v1_pair_forest_withdrawal_merged_c1_v1,
                PoolV1PairForestInputNoteWitnessV1, PoolV1PairForestMergedC1CompilationV1,
                PoolV1PairForestPrivateTransferWitnessV1, PoolV1PairForestWithdrawalWitnessV1,
            },
            pair_trace::PoolV1PairInputNoteWitnessV1,
            pool_v1_note_commitment, pool_v1_nullifier, pool_v1_tree_parent,
            IncrementalMerkleTreeV1, PoolV1MembershipWitnessV1, PoolV1OutputNoteWitnessV1,
            PoolV1PairLeafWitnessV1, PoolV1PaymentRelationContextV1, PoolV1PaymentRuntimeBindingV1,
            POOL_V1_PAIR_TREE_DEPTH,
        },
        spend::derive_owner_key,
    };

    #[test]
    fn generated_pair_empty_roots_replay_exactly() {
        let zero = [M31::ZERO; DIGEST_ELEMS];
        let mut expected = [zero; 21];
        expected[0] = pool_v1_tree_parent(&zero, &zero);
        for level in 0..20 {
            expected[level + 1] = pool_v1_tree_parent(&expected[level], &expected[level]);
        }
        assert_eq!(expected, core::array::from_fn(empty_root));
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|lane| M31(seed + 17 * lane as u32 + 1))
    }

    fn pair_empty_roots() -> [Digest; POOL_V1_PAIR_TREE_DEPTH + 1] {
        core::array::from_fn(empty_root)
    }

    fn snapshot_at(
        pool: [u8; 32],
        deployment_domain: [u8; 32],
        index: u64,
    ) -> super::super::PoolV1PairLiveSnapshotV1 {
        let empty = pair_empty_roots();
        let mut tree = IncrementalMerkleTreeV1::from_parts_with_empty_roots(
            0,
            empty[POOL_V1_PAIR_TREE_DEPTH],
            core::array::from_fn(|level| empty[level]),
            &empty,
        )
        .unwrap();
        for leaf in 0..index {
            tree = tree
                .append_one_with_empty_roots(digest(20_000 + 32 * leaf as u32), &empty)
                .unwrap()
                .0;
        }
        super::super::PoolV1PairLiveSnapshotV1 {
            pool,
            deployment_domain,
            sequence: index,
            next_pair_index: index,
            current_root: tree.root,
            frontier: tree.frontier,
        }
    }

    fn input_witness(value: u32) -> PoolV1PairForestInputNoteWitnessV1 {
        let nullifier_key = digest(10);
        let salt = digest(100);
        let asset = M31(77);
        let owner = derive_owner_key(&nullifier_key);
        let input_commitment = pool_v1_note_commitment(&owner, value, asset, &salt);
        PoolV1PairForestInputNoteWitnessV1 {
            pair: PoolV1PairInputNoteWitnessV1 {
                nullifier_key,
                salt,
                value,
                pair_leaf: PoolV1PairLeafWitnessV1::two_outputs(input_commitment, digest(900))
                    .unwrap(),
                selected_second: false,
                membership: PoolV1MembershipWitnessV1 {
                    siblings: core::array::from_fn(|level| digest(2_000 + 20 * level as u32)),
                    index: 0x5_4321,
                },
            },
            super_root_siblings: [digest(3_000), digest(3_100), digest(3_200)],
            super_root_directions: [true, false, true],
        }
    }

    fn global_anchor(input: &PoolV1PairForestInputNoteWitnessV1) -> Digest {
        let mut current = input.pair.pair_leaf.leaf_digest().unwrap();
        for level in 0..POOL_V1_PAIR_TREE_DEPTH {
            let sibling = input.pair.membership.siblings[level];
            current = if ((input.pair.membership.index >> level) & 1) == 0 {
                pool_v1_tree_parent(&current, &sibling)
            } else {
                pool_v1_tree_parent(&sibling, &current)
            };
        }
        for level in 0..3 {
            let sibling = input.super_root_siblings[level];
            current = if input.super_root_directions[level] {
                pool_v1_tree_parent(&sibling, &current)
            } else {
                pool_v1_tree_parent(&current, &sibling)
            };
        }
        current
    }

    fn output(seed: u32, value: u32) -> PoolV1OutputNoteWitnessV1 {
        PoolV1OutputNoteWitnessV1 {
            owner_key: digest(seed),
            salt: digest(seed + 100),
            value,
        }
    }

    fn context<'a>(
        pool: [u8; 32],
        deployment_domain: [u8; 32],
        anchor: Digest,
        asset_id: M31,
    ) -> PoolV1PaymentRelationContextV1<'a> {
        PoolV1PaymentRelationContextV1 {
            runtime_binding: PoolV1PaymentRuntimeBindingV1 {
                pool,
                deployment_domain,
                anchor_sequence: 42,
                anchor_root: anchor,
                asset_id,
            },
            spent_nullifiers: &[],
        }
    }

    fn transfer_at(
        index: u64,
    ) -> (
        PoolV1PrivateTransferPublicV1,
        PoolV1PairForestMergedC1CompilationV1,
    ) {
        let input = input_witness(1_000);
        let witness = PoolV1PairForestPrivateTransferWitnessV1 {
            input,
            recipient: output(300, 600),
            change: output(500, 400),
        };
        let asset_id = M31(77);
        let anchor = global_anchor(&witness.input);
        let public = PoolV1PrivateTransferPublicV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            anchor_sequence: 42,
            anchor_root: anchor,
            nullifier: pool_v1_nullifier(
                &witness.input.pair.nullifier_key,
                &witness.input.pair.salt,
            ),
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
        let compiled = compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
            &public,
            &witness,
            context(public.pool, public.deployment_domain, anchor, asset_id),
            snapshot_at(public.pool, public.deployment_domain, index),
        )
        .unwrap();
        (public, compiled)
    }

    fn withdrawal_at(
        index: u64,
    ) -> (
        PoolV1WithdrawalPublicV1,
        PoolV1PairForestMergedC1CompilationV1,
    ) {
        let input = input_witness(1_000);
        let witness = PoolV1PairForestWithdrawalWitnessV1 {
            input,
            change: output(700, 750),
        };
        let asset_id = M31(77);
        let anchor = global_anchor(&witness.input);
        let public = PoolV1WithdrawalPublicV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            anchor_sequence: 42,
            anchor_root: anchor,
            nullifier: pool_v1_nullifier(
                &witness.input.pair.nullifier_key,
                &witness.input.pair.salt,
            ),
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
        let compiled = compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(
            &public,
            &witness,
            context(public.pool, public.deployment_domain, anchor, asset_id),
            snapshot_at(public.pool, public.deployment_domain, index),
        )
        .unwrap();
        (public, compiled)
    }

    fn boolean_point(row: usize) -> [QM31; 10] {
        core::array::from_fn(|coordinate| lift(M31(((row >> (9 - coordinate)) & 1) as u32)))
    }

    fn compiled_openings_at(
        compiled: &PoolV1PairForestMergedC1CompilationV1,
        row: usize,
    ) -> StateOnlyPoseidonOpenings {
        let rows = [row, (row + 1) & 1023, row ^ 12];
        StateOnlyPoseidonOpenings {
            z: core::array::from_fn(|column| lift(compiled.semantic_c1.c1[column][rows[0]])),
            succ_z: core::array::from_fn(|column| lift(compiled.semantic_c1.c1[column][rows[1]])),
            xor12_z: core::array::from_fn(|column| lift(compiled.semantic_c1.c1[column][rows[2]])),
        }
    }

    fn literal_public_digest_packed(
        public: SemanticPublic<'_>,
        openings: &StateOnlyPoseidonOpenings,
        selectors: &Selectors,
    ) -> [QM31; DIGEST_ELEMS / 4] {
        let lanes = public_digest_lanes(public, openings, selectors);
        core::array::from_fn(|group| qm31_pack_base4(&lanes[4 * group..4 * group + 4]))
    }

    fn assert_public_digest_factoring_on_every_boolean_row(
        public: SemanticPublic<'_>,
        compiled: &PoolV1PairForestMergedC1CompilationV1,
        variant: &str,
    ) {
        for row in 0..POOL_V1_PAIR_FOREST_TERMINAL_ROWS_V1 {
            let selectors = Selectors::boxed_at_point(&boolean_point(row));
            let openings = compiled_openings_at(compiled, row);
            assert_eq!(
                public_digest_packed(public, &openings, &selectors),
                literal_public_digest_packed(public, &openings, &selectors),
                "{variant} public-digest factoring mismatch at Boolean row {row}"
            );
        }
    }

    fn next_test_m31(state: &mut u64) -> M31 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        M31(((*state >> 32) as u32) % 2_147_483_647)
    }

    fn next_test_qm31(state: &mut u64) -> QM31 {
        QM31 {
            c0: CM31 {
                a: next_test_m31(state),
                b: next_test_m31(state),
            },
            c1: CM31 {
                a: next_test_m31(state),
                b: next_test_m31(state),
            },
        }
    }

    #[test]
    fn semantic_common_factor_kernels_equal_literal_off_domain() {
        let mut state = 0x6661_6374_6f72_7631u64;
        for sample in 0..128 {
            let low = next_test_qm31(&mut state);
            let fixed = next_test_qm31(&mut state);
            let chunk_two = next_test_qm31(&mut state);
            let chunk_eight = next_test_qm31(&mut state);
            let nodes = next_test_qm31(&mut state);
            let openings = StateOnlyPoseidonOpenings {
                z: core::array::from_fn(|_| next_test_qm31(&mut state)),
                succ_z: core::array::from_fn(|_| next_test_qm31(&mut state)),
                xor12_z: core::array::from_fn(|_| next_test_qm31(&mut state)),
            };
            assert_eq!(
                absorption_lanes_factored(low, fixed, chunk_two, chunk_eight, nodes, &openings.z,),
                absorption_lanes_literal(low, fixed, chunk_two, chunk_eight, nodes, &openings.z,),
                "absorption mismatch at sample {sample}",
            );
            let path_selector = next_test_qm31(&mut state);
            assert_eq!(
                path_lanes_factored(path_selector, &openings),
                path_lanes_literal(path_selector, &openings),
                "path mismatch at sample {sample}",
            );
            let input_selector = next_test_qm31(&mut state);
            let output_selector = next_test_qm31(&mut state);
            let expected_output = M31((sample & 1) as u32);
            assert_eq!(
                occupancy_lanes_factored(
                    input_selector,
                    output_selector,
                    expected_output,
                    &openings.z,
                ),
                occupancy_lanes_literal(
                    input_selector,
                    output_selector,
                    expected_output,
                    &openings.z,
                ),
                "occupancy mismatch at sample {sample}",
            );
        }
    }

    fn assert_public_digest_factoring_off_domain(public: SemanticPublic<'_>, variant: &str) {
        let mut state = 0x51ec_70a5_d163_357bu64;
        for sample in 0..64 {
            let point = core::array::from_fn(|_| next_test_qm31(&mut state));
            let selectors = Selectors::boxed_at_point(&point);
            let openings = StateOnlyPoseidonOpenings {
                z: core::array::from_fn(|_| next_test_qm31(&mut state)),
                succ_z: core::array::from_fn(|_| next_test_qm31(&mut state)),
                xor12_z: core::array::from_fn(|_| next_test_qm31(&mut state)),
            };
            assert_eq!(
                public_digest_packed(public, &openings, &selectors),
                literal_public_digest_packed(public, &openings, &selectors),
                "{variant} public-digest factoring mismatch at off-domain sample {sample}"
            );
        }
    }

    fn claims_at(
        compiled: &PoolV1PairForestMergedC1CompilationV1,
        helper: &[QM31],
        row: usize,
    ) -> [QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1] {
        let rows = [row, (row + 1) & 1023, row ^ 12];
        let mut claims = [QM31::ZERO; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1];
        for point in 0..3 {
            for column in 0..16 {
                claims[point * 28 + column] = lift(compiled.semantic_c1.c1[column][rows[point]]);
            }
        }
        claims[SELECTED_H1_COLUMN] = helper[row];
        claims
    }

    fn assert_honest_transfer_rows(
        public: &PoolV1PrivateTransferPublicV1,
        compiled: &PoolV1PairForestMergedC1CompilationV1,
    ) {
        let lambda = lift(M31(19));
        let chi = lift(M31(23));
        let theta = lift(M31(29));
        let helper = build_pool_v1_pair_forest_copy_helper_v1(
            &compiled.trace,
            compiled.public_statement.live_snapshot.next_pair_index,
            lambda,
            chi,
        )
        .unwrap();
        for row in 0..1024 {
            let point = boolean_point(row);
            let value = evaluate_pool_v1_pair_forest_private_transfer_selected_constraint_composition_compiled_v1(
                public,
                &compiled.public_statement,
                &claims_at(compiled, &helper, row),
                &point,
                lambda,
                chi,
                theta,
            )
            .unwrap();
            assert_eq!(value, QM31::ZERO, "nonzero transfer row {row}");
        }
    }

    fn assert_honest_withdrawal_rows(
        public: &PoolV1WithdrawalPublicV1,
        compiled: &PoolV1PairForestMergedC1CompilationV1,
    ) {
        let lambda = lift(M31(31));
        let chi = lift(M31(37));
        let theta = lift(M31(41));
        let helper = build_pool_v1_pair_forest_copy_helper_v1(
            &compiled.trace,
            compiled.public_statement.live_snapshot.next_pair_index,
            lambda,
            chi,
        )
        .unwrap();
        for row in 0..1024 {
            let point = boolean_point(row);
            let value = evaluate_pool_v1_pair_forest_withdrawal_selected_constraint_composition_compiled_v1(
                public,
                &compiled.public_statement,
                &claims_at(compiled, &helper, row),
                &point,
                lambda,
                chi,
                theta,
            )
            .unwrap();
            assert_eq!(value, QM31::ZERO, "nonzero withdrawal row {row}");
        }
    }

    #[test]
    fn honest_transfer_and_withdrawal_vanish_on_every_boolean_row() {
        let (transfer_public, transfer) = transfer_at(13);
        assert_honest_transfer_rows(&transfer_public, &transfer);
        let (withdrawal_public, withdrawal) = withdrawal_at(13);
        assert_honest_withdrawal_rows(&withdrawal_public, &withdrawal);
    }

    #[test]
    fn packed_public_digest_matches_all_transfer_and_withdrawal_bindings() {
        let (transfer_public, transfer) = transfer_at(13);
        for index in [0, 13, 0x5_5555, 0xa_aaaa, (1 << 20) - 1] {
            let mut transition = transfer.public_statement;
            transition.live_snapshot.next_pair_index = index;
            let transfer_semantic = private_public(&transfer_public, &transition);
            assert_public_digest_factoring_on_every_boolean_row(
                transfer_semantic,
                &transfer,
                "transfer",
            );
            assert_public_digest_factoring_off_domain(transfer_semantic, "transfer");
        }

        let (withdrawal_request, withdrawal) = withdrawal_at(13);
        for index in [0, 13, 0x5_5555, 0xa_aaaa, (1 << 20) - 1] {
            let mut transition = withdrawal.public_statement;
            transition.live_snapshot.next_pair_index = index;
            let withdrawal_semantic = withdrawal_public(&withdrawal_request, &transition);
            assert_public_digest_factoring_on_every_boolean_row(
                withdrawal_semantic,
                &withdrawal,
                "withdrawal",
            );
            assert_public_digest_factoring_off_domain(withdrawal_semantic, "withdrawal");
        }
    }

    #[test]
    fn output_occupancy_and_append_afterstate_fail_closed() {
        let (public, compiled) = transfer_at(13);
        let lambda = lift(M31(19));
        let chi = lift(M31(23));
        let theta = lift(M31(29));
        let helper =
            build_pool_v1_pair_forest_copy_helper_v1(&compiled.trace, 13, lambda, chi).unwrap();
        let row = OUTPUT_OCCUPANCY_ROW;
        let mut claims = claims_at(&compiled, &helper, row);
        claims[0] = QM31::ZERO;
        assert_ne!(
            evaluate_pool_v1_pair_forest_private_transfer_selected_constraint_composition_compiled_v1(
                &public,
                &compiled.public_statement,
                &claims,
                &boolean_point(row),
                lambda,
                chi,
                theta,
            )
            .unwrap(),
            QM31::ZERO
        );

        let mut bad = compiled.public_statement;
        bad.candidate_afterstate.next_frontier[0][0] =
            bad.candidate_afterstate.next_frontier[0][0].add(M31::ONE);
        assert_eq!(
            evaluate_pool_v1_pair_forest_private_transfer_selected_constraint_composition_compiled_v1(
                &public,
                &bad,
                &claims_at(&compiled, &helper, 0),
                &boolean_point(0),
                lambda,
                chi,
                theta,
            ),
            Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidAppendTransition)
        );
    }
}
