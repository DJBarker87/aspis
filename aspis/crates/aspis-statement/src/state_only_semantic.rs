//! Host oracle for the non-Poseidon part of the state-only candidate.
//!
//! This is deliberately a research-profile module. It does not alter the
//! frozen v4 constraint registry. The twenty Merkle selections and two
//! three-limb range checks reuse the already-bound `(z, succ(z), xor12(z))`
//! openings; the 102 surviving copy links use one ordinary LogUp helper.

use alloc::vec;
use alloc::vec::Vec;

use aspis_core::field::{qm31_pack_base4, CM31, M31, QM31};

use crate::constraints_v4::multilinear_evaluate_qm31;
use crate::logup::{build_copy_logup_helper, CopyLogUpRow, LogUpError};
use crate::poseidon2::{DIGEST_ELEMS, POSEIDON2_WIDTH, RATE};
use crate::spend::{
    SpendPublic, DOMAIN_MERKLE_NODE, DOMAIN_NOTE, DOMAIN_NULLIFIER, DOMAIN_OWNER_KEY, VALUE_LIMIT,
};
use crate::state_only_poseidon::{
    state_only_poseidon_openings_at_point, StateOnlyPoseidonOpenings,
};
use crate::state_only_trace::{
    build_state_only_cell_map_v4, state_only_copy_layout_v4, StateOnlyCopyLayout,
    StateOnlyLayoutError, StateOnlyTraceFoundation, STATE_ONLY_DIRECT_RANGE_BALANCE_OUTPUT_COLUMN,
    STATE_ONLY_DIRECT_RANGE_BITS, STATE_ONLY_DIRECT_RANGE_INPUT_TOTAL_COLUMN,
    STATE_ONLY_DIRECT_RANGE_RECONSTRUCTION_COLUMN,
};
use crate::trace_v4::{
    has_carry_payload, permutation_block_schedule, HashInvocationKind, TraceCell, TupleLimb,
    ACTIVE_ROWS_PER_BLOCK, BLOCK_ROWS, PERMUTATION_COUNT, TRACE_ROWS,
};

pub const STATE_ONLY_INITIAL_LANES: usize = 16;
pub const STATE_ONLY_ABSORPTION_ZERO_LANES: usize = 16;
pub const STATE_ONLY_MERKLE_LANES: usize = 1 + 2 * DIGEST_ELEMS;
pub const STATE_ONLY_DIRECT_RANGE_LANES: usize = 3 * STATE_ONLY_DIRECT_RANGE_BITS + 3;
pub const STATE_ONLY_VALUE_LANES: usize = 2;
pub const STATE_ONLY_PUBLIC_DIGEST_LANES: usize = DIGEST_ELEMS;
pub const STATE_ONLY_PUBLIC_ASSET_LANES: usize = 2;
pub const STATE_ONLY_COPY_LANES: usize = 1;
pub const STATE_ONLY_BASE_SOURCE_LANE_COUNT: usize = STATE_ONLY_INITIAL_LANES
    + STATE_ONLY_ABSORPTION_ZERO_LANES
    + STATE_ONLY_MERKLE_LANES
    + STATE_ONLY_DIRECT_RANGE_LANES
    + STATE_ONLY_VALUE_LANES
    + STATE_ONLY_PUBLIC_DIGEST_LANES
    + STATE_ONLY_PUBLIC_ASSET_LANES;
pub const STATE_ONLY_PACKED_BASE_LANE_COUNT: usize = (STATE_ONLY_BASE_SOURCE_LANE_COUNT + 3) / 4;
pub const STATE_ONLY_RANDOMIZED_SEMANTIC_LANE_COUNT: usize =
    STATE_ONLY_PACKED_BASE_LANE_COUNT + STATE_ONLY_COPY_LANES;
pub const STATE_ONLY_SEMANTIC_LANE_COUNT: usize = STATE_ONLY_INITIAL_LANES
    + STATE_ONLY_ABSORPTION_ZERO_LANES
    + STATE_ONLY_MERKLE_LANES
    + STATE_ONLY_DIRECT_RANGE_LANES
    + STATE_ONLY_VALUE_LANES
    + STATE_ONLY_PUBLIC_DIGEST_LANES
    + STATE_ONLY_PUBLIC_ASSET_LANES
    + STATE_ONLY_COPY_LANES;
pub const STATE_ONLY_STRUCTURAL_SOURCE_ALIAS_COUNT: usize = 60;
pub const STATE_ONLY_COPY_LINK_COUNT: usize = 102;

/// The direct-range bitness branch dominates this oracle: composing an MLE
/// with binary successor has individual degree at most ten, squaring has
/// degree twenty, and the activation selector adds one. The outer zerocheck
/// equality factor gives degree 22. The separate two-round Poseidon oracle
/// still dominates the complete statement at degree 27.
pub const STATE_ONLY_SEMANTIC_ORACLE_INDIVIDUAL_DEGREE: usize = 21;
pub const STATE_ONLY_SEMANTIC_ZEROCHECK_INDIVIDUAL_DEGREE: usize = 22;

const _: () = assert!(STATE_ONLY_SEMANTIC_LANE_COUNT == 95);
const _: () = assert!(STATE_ONLY_BASE_SOURCE_LANE_COUNT == 94);
const _: () = assert!(STATE_ONLY_PACKED_BASE_LANE_COUNT == 24);
const _: () = assert!(STATE_ONLY_RANDOMIZED_SEMANTIC_LANE_COUNT == 25);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlySemanticOpenings {
    pub c1: StateOnlyPoseidonOpenings,
    pub h1_z: QM31,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateOnlySemanticPrepared {
    copy: StateOnlyCopyLayout,
    input_asset: TraceCell,
    output_asset: TraceCell,
}

pub fn prepare_state_only_semantic_oracle(
) -> Result<StateOnlySemanticPrepared, StateOnlySemanticError> {
    let old_aux = crate::trace_v4::witness_aux_layout();
    let output_asset_old = TraceCell {
        row: (crate::trace_v4::AUX_ABSORPTION_PRODUCER_ROW_START + 47) as u16,
        column: 34,
    };
    let map = build_state_only_cell_map_v4()?;
    Ok(StateOnlySemanticPrepared {
        copy: state_only_copy_layout_v4()?,
        input_asset: map
            .map(old_aux.input_asset_id)
            .ok_or(StateOnlySemanticError::Shape)?,
        output_asset: map
            .map(output_asset_old)
            .ok_or(StateOnlySemanticError::Shape)?,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateOnlySemanticResiduals {
    pub initial: [QM31; STATE_ONLY_INITIAL_LANES],
    pub absorption_zero: [QM31; STATE_ONLY_ABSORPTION_ZERO_LANES],
    pub merkle: [QM31; STATE_ONLY_MERKLE_LANES],
    pub direct_range: [QM31; STATE_ONLY_DIRECT_RANGE_LANES],
    pub value: [QM31; STATE_ONLY_VALUE_LANES],
    pub public_digest: [QM31; STATE_ONLY_PUBLIC_DIGEST_LANES],
    pub public_asset: [QM31; STATE_ONLY_PUBLIC_ASSET_LANES],
    pub copy: QM31,
}

impl StateOnlySemanticResiduals {
    pub fn all_zero(&self) -> bool {
        self.initial
            .iter()
            .chain(&self.absorption_zero)
            .chain(&self.merkle)
            .chain(&self.direct_range)
            .chain(&self.value)
            .chain(&self.public_digest)
            .chain(&self.public_asset)
            .all(|value| *value == QM31::ZERO)
            && self.copy == QM31::ZERO
    }

    /// Injectively pack the 94 M31-valued Boolean-row residuals into 24
    /// QM31 lanes. The copy LogUp residual remains the 25th randomized lane.
    pub fn packed_base_lanes(&self) -> [QM31; STATE_ONLY_PACKED_BASE_LANE_COUNT] {
        let source = self
            .initial
            .iter()
            .chain(&self.absorption_zero)
            .chain(&self.merkle)
            .chain(&self.direct_range)
            .chain(&self.value)
            .chain(&self.public_digest)
            .chain(&self.public_asset)
            .copied()
            .collect::<Vec<_>>();
        debug_assert_eq!(source.len(), STATE_ONLY_BASE_SOURCE_LANE_COUNT);
        core::array::from_fn(|group| {
            let start = 4 * group;
            let end = core::cmp::min(start + 4, source.len());
            qm31_pack_base4(&source[start..end])
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlySemanticError {
    Shape,
    PublicFeeOutOfRange,
    Layout(StateOnlyLayoutError),
    CopyEndpointOverflow { row: u16 },
    LogUp(LogUpError),
}

impl From<StateOnlyLayoutError> for StateOnlySemanticError {
    fn from(error: StateOnlyLayoutError) -> Self {
        Self::Layout(error)
    }
}

impl From<LogUpError> for StateOnlySemanticError {
    fn from(error: LogUpError) -> Self {
        Self::LogUp(error)
    }
}

#[inline(always)]
fn lift(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}

#[derive(Clone)]
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

    fn copy_active(&self, layout: &StateOnlyCopyLayout) -> QM31 {
        let mut active = [false; TRACE_ROWS];
        for link in &layout.links {
            active[usize::from(link.producer_row)] = true;
            active[usize::from(link.consumer_row)] = true;
        }
        active
            .iter()
            .copied()
            .enumerate()
            .filter(|(_, active)| *active)
            .fold(QM31::ZERO, |sum, (row, _)| sum.add(self.row(row)))
    }
}

fn expected_initial_state(block: usize) -> [M31; POSEIDON2_WIDTH] {
    let invocation = permutation_block_schedule(block)
        .expect("pinned state-only block")
        .invocation;
    let (domain, length) = match invocation {
        HashInvocationKind::OwnerKey => (DOMAIN_OWNER_KEY, 8),
        HashInvocationKind::Note => (DOMAIN_NOTE, 18),
        HashInvocationKind::MerkleLevel(_) => (DOMAIN_MERKLE_NODE, 16),
        HashInvocationKind::Nullifier => (DOMAIN_NULLIFIER, 16),
        HashInvocationKind::Output => (DOMAIN_NOTE, 18),
    };
    let mut state = [M31::ZERO; POSEIDON2_WIDTH];
    state[RATE] = domain;
    state[RATE + 1] = M31(length);
    state
}

fn absorption_must_be_zero(block: usize, lane: usize) -> bool {
    let schedule = permutation_block_schedule(block).expect("pinned state-only block");
    if lane < RATE {
        lane >= usize::from(schedule.absorbed_len)
    } else {
        !has_carry_payload(block)
    }
}

#[derive(Clone, Copy)]
struct CopyRowExtension {
    producer_values: [QM31; 2],
    producer_weights: [QM31; 2],
    consumer_values: [QM31; 2],
    consumer_weights: [QM31; 2],
}

fn copy_residual(row: CopyRowExtension, helper: QM31, chi: QM31) -> QM31 {
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
    a.mul(helper.mul(b).add(c)).sub(b.mul(p))
}

fn compressed_opened_tuple(
    tuple: crate::trace_v4::CopyTuple,
    tag: M31,
    selector: QM31,
    openings: &[QM31; 16],
    powers: &[QM31; 16],
) -> QM31 {
    let mut value = selector.mul_m31(tag);
    for (limb, power) in tuple.limbs.into_iter().zip(powers) {
        if let TupleLimb::Cell(cell) = limb {
            value = value.add(selector.mul(openings[usize::from(cell.column)]).mul(*power));
        }
    }
    value
}

fn copy_terminal(
    layout: &StateOnlyCopyLayout,
    openings: &[QM31; 16],
    selectors: &Selectors,
    lambda: QM31,
) -> Result<CopyRowExtension, StateOnlySemanticError> {
    let mut powers = [QM31::ZERO; 16];
    let mut power = lambda;
    for value in &mut powers {
        *value = power;
        power = power.mul(lambda);
    }
    let mut row = CopyRowExtension {
        producer_values: [QM31::ZERO; 2],
        producer_weights: [QM31::ZERO; 2],
        consumer_values: [QM31::ZERO; 2],
        consumer_weights: [QM31::ZERO; 2],
    };
    let mut producer_arity = [0u8; TRACE_ROWS];
    let mut consumer_arity = [0u8; TRACE_ROWS];
    for link in &layout.links {
        for (endpoint, endpoint_row, arity, values, weights) in [
            (
                link.producer,
                usize::from(link.producer_row),
                &mut producer_arity,
                &mut row.producer_values,
                &mut row.producer_weights,
            ),
            (
                link.consumer,
                usize::from(link.consumer_row),
                &mut consumer_arity,
                &mut row.consumer_values,
                &mut row.consumer_weights,
            ),
        ] {
            let slot = usize::from(arity[endpoint_row]);
            if slot >= 2 {
                return Err(StateOnlySemanticError::CopyEndpointOverflow {
                    row: endpoint_row as u16,
                });
            }
            arity[endpoint_row] += 1;
            let selector = selectors.row(endpoint_row);
            weights[slot] = weights[slot].add(selector);
            values[slot] = values[slot].add(compressed_opened_tuple(
                endpoint, link.tag, selector, openings, &powers,
            ));
        }
    }
    Ok(row)
}

/// Evaluate all 95 non-Poseidon lanes. The sixty source equalities are not
/// lanes: the layout aliases both logical names to one committed cell.
pub fn evaluate_state_only_semantic_oracle(
    public: &SpendPublic,
    openings: &StateOnlySemanticOpenings,
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
) -> Result<StateOnlySemanticResiduals, StateOnlySemanticError> {
    let prepared = prepare_state_only_semantic_oracle()?;
    evaluate_state_only_semantic_oracle_prepared(public, openings, point, lambda, chi, &prepared)
}

pub fn evaluate_state_only_semantic_oracle_prepared(
    public: &SpendPublic,
    openings: &StateOnlySemanticOpenings,
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    prepared: &StateOnlySemanticPrepared,
) -> Result<StateOnlySemanticResiduals, StateOnlySemanticError> {
    if public.fee >= VALUE_LIMIT {
        return Err(StateOnlySemanticError::PublicFeeOutOfRange);
    }
    let selectors = Selectors::at_point(point);

    let mut initial = [QM31::ZERO; STATE_ONLY_INITIAL_LANES];
    for block in 0..PERMUTATION_COUNT {
        if permutation_block_schedule(block).unwrap().chunk_index != 0 {
            continue;
        }
        let selector = selectors.row(block * BLOCK_ROWS);
        let expected = expected_initial_state(block);
        for lane in 0..POSEIDON2_WIDTH {
            initial[lane] =
                initial[lane].add(selector.mul(openings.c1.z[lane].sub(lift(expected[lane]))));
        }
    }

    let mut absorption_zero = [QM31::ZERO; STATE_ONLY_ABSORPTION_ZERO_LANES];
    for block in 0..PERMUTATION_COUNT {
        let selector = selectors.row(block * BLOCK_ROWS + 12);
        for lane in 0..POSEIDON2_WIDTH {
            if absorption_must_be_zero(block, lane) {
                absorption_zero[lane] =
                    absorption_zero[lane].add(selector.mul(openings.c1.z[lane]));
            }
        }
    }

    let merkle_selector = (0..20usize).fold(QM31::ZERO, |sum, level| {
        let row = 784 + 16 * (level / 4) + 2 * (level % 4);
        sum.add(selectors.row(row))
    });
    let bit = openings.c1.z[0];
    let mut merkle = [QM31::ZERO; STATE_ONLY_MERKLE_LANES];
    merkle[0] = merkle_selector.mul(bit.mul(bit.sub(QM31::ONE)));
    for limb in 0..DIGEST_ELEMS {
        let current = openings.c1.z[1 + limb];
        let sibling = openings.c1.xor12_z[limb];
        let delta = sibling.sub(current);
        merkle[1 + limb] =
            merkle_selector.mul(openings.c1.succ_z[limb].sub(current.add(bit.mul(delta))));
        merkle[1 + DIGEST_ELEMS + limb] =
            merkle_selector.mul(openings.c1.succ_z[RATE + limb].sub(sibling.sub(bit.mul(delta))));
    }

    let range_selectors = [selectors.row(864), selectors.row(866)];
    let range_selector = range_selectors[0].add(range_selectors[1]);
    let views = [&openings.c1.z, &openings.c1.succ_z, &openings.c1.xor12_z];
    let mut direct_range = [QM31::ZERO; STATE_ONLY_DIRECT_RANGE_LANES];
    for (view_index, view) in views.into_iter().enumerate() {
        for bit in 0..STATE_ONLY_DIRECT_RANGE_BITS {
            direct_range[view_index * STATE_ONLY_DIRECT_RANGE_BITS + bit] =
                range_selector.mul(view[bit].mul(view[bit].sub(QM31::ONE)));
        }
        let reconstructed = (0..STATE_ONLY_DIRECT_RANGE_BITS).fold(QM31::ZERO, |sum, bit| {
            sum.add(view[bit].mul_m31(M31(1 << bit)))
        });
        direct_range[3 * STATE_ONLY_DIRECT_RANGE_BITS + view_index] = range_selector
            .mul(view[STATE_ONLY_DIRECT_RANGE_RECONSTRUCTION_COLUMN].sub(reconstructed));
    }

    let triple_value = |activation: QM31| {
        activation.mul(
            openings.c1.z[STATE_ONLY_DIRECT_RANGE_RECONSTRUCTION_COLUMN]
                .add(
                    openings.c1.succ_z[STATE_ONLY_DIRECT_RANGE_RECONSTRUCTION_COLUMN]
                        .mul_m31(M31(1 << 10)),
                )
                .add(
                    openings.c1.xor12_z[STATE_ONLY_DIRECT_RANGE_RECONSTRUCTION_COLUMN]
                        .mul_m31(M31(1 << 20)),
                ),
        )
    };
    let input_total =
        range_selectors[0].mul(openings.c1.z[STATE_ONLY_DIRECT_RANGE_INPUT_TOTAL_COLUMN]);
    let output_total =
        range_selectors[1].mul(openings.c1.z[STATE_ONLY_DIRECT_RANGE_INPUT_TOTAL_COLUMN]);
    let value = [
        input_total
            .sub(triple_value(range_selectors[0]))
            .add(output_total.sub(triple_value(range_selectors[1]))),
        range_selectors[0].mul(
            openings.c1.z[STATE_ONLY_DIRECT_RANGE_INPUT_TOTAL_COLUMN]
                .sub(openings.c1.z[STATE_ONLY_DIRECT_RANGE_BALANCE_OUTPUT_COLUMN])
                .sub(lift(M31(public.fee))),
        ),
    ];

    let mut public_digest = [QM31::ZERO; STATE_ONLY_PUBLIC_DIGEST_LANES];
    for (block, digest) in [
        (43usize, &public.anchor),
        (45usize, &public.nullifier),
        (48usize, &public.output_commitment),
    ] {
        let selector = selectors.row(block * BLOCK_ROWS + ACTIVE_ROWS_PER_BLOCK);
        for limb in 0..DIGEST_ELEMS {
            public_digest[limb] =
                public_digest[limb].add(selector.mul(openings.c1.z[limb].sub(lift(digest[limb]))));
        }
    }

    let asset_residual = |cell: TraceCell| {
        selectors
            .row(usize::from(cell.row))
            .mul(openings.c1.z[usize::from(cell.column)].sub(lift(public.asset_id)))
    };
    let public_asset = [
        asset_residual(prepared.input_asset),
        asset_residual(prepared.output_asset),
    ];

    let terminal = copy_terminal(&prepared.copy, &openings.c1.z, &selectors, lambda)?;
    let copy =
        selectors
            .copy_active(&prepared.copy)
            .mul(copy_residual(terminal, openings.h1_z, chi));
    Ok(StateOnlySemanticResiduals {
        initial,
        absorption_zero,
        merkle,
        direct_range,
        value,
        public_digest,
        public_asset,
        copy,
    })
}

fn tuple_value(trace: &StateOnlyTraceFoundation, tuple: crate::trace_v4::CopyTuple) -> Vec<M31> {
    tuple
        .limbs
        .into_iter()
        .map(|limb| match limb {
            TupleLimb::Cell(cell) => trace.c1[usize::from(cell.column)][usize::from(cell.row)],
            TupleLimb::Zero => M31::ZERO,
        })
        .collect()
}

pub fn build_state_only_copy_helper_v4(
    trace: &StateOnlyTraceFoundation,
    lambda: QM31,
    chi: QM31,
) -> Result<Vec<QM31>, StateOnlySemanticError> {
    if trace.c1.iter().any(|column| column.len() != TRACE_ROWS) {
        return Err(StateOnlySemanticError::Shape);
    }
    let mut rows = vec![
        CopyLogUpRow {
            producer_values: [QM31::ZERO; 2],
            producer_weights: [M31::ZERO; 2],
            consumer_values: [QM31::ZERO; 2],
            consumer_weights: [M31::ZERO; 2],
        };
        TRACE_ROWS
    ];
    for link in state_only_copy_layout_v4()?.links {
        let producer_row = usize::from(link.producer_row);
        {
            let row = &mut rows[producer_row];
            let slot = row
                .producer_weights
                .iter()
                .position(|weight| *weight == M31::ZERO)
                .ok_or(StateOnlySemanticError::CopyEndpointOverflow {
                    row: producer_row as u16,
                })?;
            row.producer_values[slot] = crate::logup::compress_tagged_tuple(
                link.tag,
                &tuple_value(trace, link.producer),
                lambda,
            );
            row.producer_weights[slot] = M31::ONE;
        }
        let consumer_row = usize::from(link.consumer_row);
        {
            let row = &mut rows[consumer_row];
            let slot = row
                .consumer_weights
                .iter()
                .position(|weight| *weight == M31::ZERO)
                .ok_or(StateOnlySemanticError::CopyEndpointOverflow {
                    row: consumer_row as u16,
                })?;
            row.consumer_values[slot] = crate::logup::compress_tagged_tuple(
                link.tag,
                &tuple_value(trace, link.consumer),
                lambda,
            );
            row.consumer_weights[slot] = M31::ONE;
        }
    }
    Ok(build_copy_logup_helper(&rows, chi)?)
}

pub fn state_only_semantic_openings_at_point(
    trace: &StateOnlyTraceFoundation,
    h1: &[QM31],
    point: &[QM31; 10],
) -> Option<StateOnlySemanticOpenings> {
    Some(StateOnlySemanticOpenings {
        c1: state_only_poseidon_openings_at_point(&trace.c1, point)?,
        h1_z: multilinear_evaluate_qm31(h1, point)?,
    })
}

pub fn state_only_copy_helper_sum(h1: &[QM31]) -> Option<QM31> {
    (h1.len() == TRACE_ROWS).then(|| h1.iter().copied().fold(QM31::ZERO, QM31::add))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spend::{
        derive_nullifier, derive_owner_key, merkle_root, note_commitment, output_commitment,
        MerklePath, SpendWitness,
    };
    use crate::state_only_trace::{
        project_state_only_trace_v4, STATE_ONLY_PADDING_ROW_START_IN_BLOCK,
    };
    use crate::trace_v4::build_spend_trace_v4;

    fn digest(seed: u32) -> [M31; 8] {
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
            siblings: (0..20)
                .map(|level| digest(1_000 + level as u32 * 31))
                .collect(),
            index: 0x5a5a5,
        };
        let public = SpendPublic {
            anchor: merkle_root(note, &path).unwrap(),
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output_commitment(
                &output_owner_key,
                value_out,
                asset_id,
                &output_salt,
            ),
            asset_id,
            fee,
        };
        (
            public,
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

    fn boolean_point(row: usize) -> [QM31; 10] {
        core::array::from_fn(|coordinate| {
            if (row >> (9 - coordinate)) & 1 == 0 {
                QM31::ZERO
            } else {
                QM31::ONE
            }
        })
    }

    fn next_u32(state: &mut u64) -> u32 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        ((*state >> 32) as u32) % aspis_core::field::P
    }

    fn random_qm31(state: &mut u64) -> QM31 {
        QM31 {
            c0: CM31::new(M31(next_u32(state)), M31(next_u32(state))),
            c1: CM31::new(M31(next_u32(state)), M31(next_u32(state))),
        }
    }

    fn eq_reference(point: &[QM31; 10], row: usize) -> QM31 {
        point
            .iter()
            .enumerate()
            .fold(QM31::ONE, |weight, (coordinate, value)| {
                weight.mul(if (row >> (9 - coordinate)) & 1 == 0 {
                    QM31::ONE.sub(*value)
                } else {
                    *value
                })
            })
    }

    fn reference_copy_terminal(
        prepared: &StateOnlySemanticPrepared,
        openings: &[QM31; 16],
        point: &[QM31; 10],
        lambda: QM31,
    ) -> CopyRowExtension {
        let mut powers = [QM31::ZERO; 16];
        let mut power = lambda;
        for value in &mut powers {
            *value = power;
            power = power.mul(lambda);
        }
        let mut result = CopyRowExtension {
            producer_values: [QM31::ZERO; 2],
            producer_weights: [QM31::ZERO; 2],
            consumer_values: [QM31::ZERO; 2],
            consumer_weights: [QM31::ZERO; 2],
        };
        let mut producer_arity = [0u8; TRACE_ROWS];
        let mut consumer_arity = [0u8; TRACE_ROWS];
        for link in &prepared.copy.links {
            let producer_row = usize::from(link.producer_row);
            let producer_slot = usize::from(producer_arity[producer_row]);
            producer_arity[producer_row] += 1;
            let selector = eq_reference(point, producer_row);
            result.producer_weights[producer_slot] =
                result.producer_weights[producer_slot].add(selector);
            let mut compressed = selector.mul_m31(link.tag);
            for (limb, power) in link.producer.limbs.into_iter().zip(powers) {
                if let TupleLimb::Cell(cell) = limb {
                    compressed =
                        compressed.add(selector.mul(openings[usize::from(cell.column)]).mul(power));
                }
            }
            result.producer_values[producer_slot] =
                result.producer_values[producer_slot].add(compressed);

            let consumer_row = usize::from(link.consumer_row);
            let consumer_slot = usize::from(consumer_arity[consumer_row]);
            consumer_arity[consumer_row] += 1;
            let selector = eq_reference(point, consumer_row);
            result.consumer_weights[consumer_slot] =
                result.consumer_weights[consumer_slot].add(selector);
            let mut compressed = selector.mul_m31(link.tag);
            for (limb, power) in link.consumer.limbs.into_iter().zip(powers) {
                if let TupleLimb::Cell(cell) = limb {
                    compressed =
                        compressed.add(selector.mul(openings[usize::from(cell.column)]).mul(power));
                }
            }
            result.consumer_values[consumer_slot] =
                result.consumer_values[consumer_slot].add(compressed);
        }
        result
    }

    fn reference_semantic_oracle(
        public: &SpendPublic,
        openings: &StateOnlySemanticOpenings,
        point: &[QM31; 10],
        lambda: QM31,
        chi: QM31,
        prepared: &StateOnlySemanticPrepared,
    ) -> StateOnlySemanticResiduals {
        let mut initial = [QM31::ZERO; STATE_ONLY_INITIAL_LANES];
        for block in 0..PERMUTATION_COUNT {
            if permutation_block_schedule(block).unwrap().chunk_index == 0 {
                let selector = eq_reference(point, block * BLOCK_ROWS);
                let expected = expected_initial_state(block);
                for lane in 0..16 {
                    initial[lane] = initial[lane]
                        .add(selector.mul(openings.c1.z[lane].sub(lift(expected[lane]))));
                }
            }
        }
        let mut absorption_zero = [QM31::ZERO; STATE_ONLY_ABSORPTION_ZERO_LANES];
        for block in 0..PERMUTATION_COUNT {
            let selector = eq_reference(point, block * 16 + 12);
            for lane in 0..16 {
                if absorption_must_be_zero(block, lane) {
                    absorption_zero[lane] =
                        absorption_zero[lane].add(selector.mul(openings.c1.z[lane]));
                }
            }
        }
        let merkle_selector = (0..20).fold(QM31::ZERO, |sum, level| {
            sum.add(eq_reference(
                point,
                784 + 16 * (level / 4) + 2 * (level % 4),
            ))
        });
        let bit = openings.c1.z[0];
        let mut merkle = [QM31::ZERO; STATE_ONLY_MERKLE_LANES];
        merkle[0] = merkle_selector.mul(bit.mul(bit.sub(QM31::ONE)));
        for limb in 0..8 {
            let current = openings.c1.z[1 + limb];
            let sibling = openings.c1.xor12_z[limb];
            let selected = bit.mul(sibling.sub(current));
            merkle[1 + limb] =
                merkle_selector.mul(openings.c1.succ_z[limb].sub(current.add(selected)));
            merkle[9 + limb] =
                merkle_selector.mul(openings.c1.succ_z[8 + limb].sub(sibling.sub(selected)));
        }
        let activation = eq_reference(point, 864).add(eq_reference(point, 866));
        let views = [&openings.c1.z, &openings.c1.succ_z, &openings.c1.xor12_z];
        let mut direct_range = [QM31::ZERO; STATE_ONLY_DIRECT_RANGE_LANES];
        for view_index in 0..3 {
            for bit in 0..10 {
                direct_range[10 * view_index + bit] = activation
                    .mul(views[view_index][bit].mul(views[view_index][bit].sub(QM31::ONE)));
            }
            let reconstructed = (0..10).fold(QM31::ZERO, |sum, bit| {
                sum.add(views[view_index][bit].mul_m31(M31(1 << bit)))
            });
            direct_range[30 + view_index] =
                activation.mul(views[view_index][10].sub(reconstructed));
        }
        let input_selector = eq_reference(point, 864);
        let output_selector = eq_reference(point, 866);
        let triple = |selector: QM31| {
            selector.mul(
                openings.c1.z[10]
                    .add(openings.c1.succ_z[10].mul_m31(M31(1 << 10)))
                    .add(openings.c1.xor12_z[10].mul_m31(M31(1 << 20))),
            )
        };
        let value = [
            input_selector
                .mul(openings.c1.z[11])
                .sub(triple(input_selector))
                .add(
                    output_selector
                        .mul(openings.c1.z[11])
                        .sub(triple(output_selector)),
                ),
            input_selector.mul(
                openings.c1.z[11]
                    .sub(openings.c1.z[12])
                    .sub(lift(M31(public.fee))),
            ),
        ];
        let mut public_digest = [QM31::ZERO; 8];
        for (block, digest) in [
            (43usize, &public.anchor),
            (45usize, &public.nullifier),
            (48usize, &public.output_commitment),
        ] {
            let selector = eq_reference(point, block * 16 + 11);
            for limb in 0..8 {
                public_digest[limb] = public_digest[limb]
                    .add(selector.mul(openings.c1.z[limb].sub(lift(digest[limb]))));
            }
        }
        let asset = |cell: TraceCell| {
            eq_reference(point, usize::from(cell.row))
                .mul(openings.c1.z[usize::from(cell.column)].sub(lift(public.asset_id)))
        };
        StateOnlySemanticResiduals {
            initial,
            absorption_zero,
            merkle,
            direct_range,
            value,
            public_digest,
            public_asset: [asset(prepared.input_asset), asset(prepared.output_asset)],
            copy: {
                let mut active = [false; TRACE_ROWS];
                for link in &prepared.copy.links {
                    active[usize::from(link.producer_row)] = true;
                    active[usize::from(link.consumer_row)] = true;
                }
                active
                    .iter()
                    .copied()
                    .enumerate()
                    .filter(|(_, active)| *active)
                    .map(|(row, _)| eq_reference(point, row))
                    .fold(QM31::ZERO, QM31::add)
                    .mul(copy_residual(
                        reference_copy_terminal(prepared, &openings.c1.z, point, lambda),
                        openings.h1_z,
                        chi,
                    ))
            },
        }
    }

    fn honest() -> (SpendPublic, StateOnlyTraceFoundation, Vec<QM31>, QM31, QM31) {
        let (public, witness) = fixture();
        let old = build_spend_trace_v4(&public, &witness).unwrap();
        let trace = project_state_only_trace_v4(&old).unwrap();
        let lambda = QM31 {
            c0: CM31::new(M31(123), M31(456)),
            c1: CM31::new(M31(789), M31(1011)),
        };
        let chi = QM31 {
            c0: CM31::new(M31(1213), M31(1415)),
            c1: CM31::new(M31(1617), M31(1819)),
        };
        let h1 = build_state_only_copy_helper_v4(&trace, lambda, chi).unwrap();
        assert_eq!(state_only_copy_helper_sum(&h1), Some(QM31::ZERO));
        (public, trace, h1, lambda, chi)
    }

    #[test]
    fn honest_boolean_trace_zeros_all_95_lanes_and_padding_is_relation_free() {
        let (public, mut trace, h1, lambda, chi) = honest();
        let prepared = prepare_state_only_semantic_oracle().unwrap();
        for row in 0..TRACE_ROWS {
            let point = boolean_point(row);
            let openings = state_only_semantic_openings_at_point(&trace, &h1, &point).unwrap();
            assert!(
                evaluate_state_only_semantic_oracle_prepared(
                    &public, &openings, &point, lambda, chi, &prepared
                )
                .unwrap()
                .all_zero(),
                "row {row}"
            );
        }
        for block in 0..PERMUTATION_COUNT {
            for row in STATE_ONLY_PADDING_ROW_START_IN_BLOCK..BLOCK_ROWS {
                for lane in 0..POSEIDON2_WIDTH {
                    trace.c1[lane][block * BLOCK_ROWS + row] = M31((lane + row + 1) as u32);
                }
                let point = boolean_point(block * BLOCK_ROWS + row);
                let openings = state_only_semantic_openings_at_point(&trace, &h1, &point).unwrap();
                assert!(evaluate_state_only_semantic_oracle_prepared(
                    &public, &openings, &point, lambda, chi, &prepared
                )
                .unwrap()
                .all_zero());
            }
        }
    }

    #[test]
    fn corruption_teeth_cover_every_relation_family() {
        let (public, trace, h1, lambda, chi) = honest();
        let prepared = prepare_state_only_semantic_oracle().unwrap();
        let checks = [
            (0usize, 0usize),  // initial
            (12, 15),          // absorption tail
            (785, 0),          // Merkle left
            (864, 0),          // direct bit
            (864, 11),         // input reconstruction
            (43 * 16 + 11, 0), // public digest
        ];
        for (row, column) in checks {
            let mut bad = trace.clone();
            bad.c1[column][row] = bad.c1[column][row].add(M31::ONE);
            let point = boolean_point(if row == 785 { 784 } else { row });
            let openings = state_only_semantic_openings_at_point(&bad, &h1, &point).unwrap();
            assert!(
                !evaluate_state_only_semantic_oracle_prepared(
                    &public, &openings, &point, lambda, chi, &prepared
                )
                .unwrap()
                .all_zero(),
                "mutation ({row},{column}) escaped"
            );
        }

        let map = build_state_only_cell_map_v4().unwrap();
        let aux = crate::trace_v4::witness_aux_layout();
        let asset = map.map(aux.input_asset_id).unwrap();
        let mut bad = trace.clone();
        bad.c1[usize::from(asset.column)][usize::from(asset.row)] =
            bad.c1[usize::from(asset.column)][usize::from(asset.row)].add(M31::ONE);
        let point = boolean_point(usize::from(asset.row));
        let openings = state_only_semantic_openings_at_point(&bad, &h1, &point).unwrap();
        assert!(!evaluate_state_only_semantic_oracle_prepared(
            &public, &openings, &point, lambda, chi, &prepared
        )
        .unwrap()
        .all_zero());

        // A surviving copy endpoint mutation is caught with the honest helper
        // locally; rebuilding the helper instead makes its required global
        // zero-sum claim nonzero.
        let link = state_only_copy_layout_v4().unwrap().links[0];
        let cell = link
            .producer
            .limbs
            .into_iter()
            .find_map(|limb| match limb {
                TupleLimb::Cell(cell) => Some(cell),
                TupleLimb::Zero => None,
            })
            .unwrap();
        let mut bad = trace;
        bad.c1[usize::from(cell.column)][usize::from(cell.row)] =
            bad.c1[usize::from(cell.column)][usize::from(cell.row)].add(M31::ONE);
        let point = boolean_point(usize::from(cell.row));
        let openings = state_only_semantic_openings_at_point(&bad, &h1, &point).unwrap();
        assert_ne!(
            evaluate_state_only_semantic_oracle_prepared(
                &public, &openings, &point, lambda, chi, &prepared
            )
            .unwrap()
            .copy,
            QM31::ZERO
        );
        let bad_h1 = build_state_only_copy_helper_v4(&bad, lambda, chi).unwrap();
        assert_ne!(state_only_copy_helper_sum(&bad_h1), Some(QM31::ZERO));
    }

    #[test]
    fn source_aliases_are_structural_and_range_rows_use_the_three_bound_points() {
        let map = build_state_only_cell_map_v4().unwrap();
        for binding in crate::trace_v4::source_relation_layout() {
            let row = (crate::trace_v4::AUX_ABSORPTION_PRODUCER_ROW_START
                + usize::from(binding.block)) as u16;
            assert_eq!(
                map.map(TraceCell {
                    row,
                    column: binding.left_column
                }),
                map.map(TraceCell {
                    row,
                    column: binding.right_column
                })
            );
        }
        assert_eq!(STATE_ONLY_STRUCTURAL_SOURCE_ALIAS_COUNT, 60);
        assert_eq!(
            STATE_ONLY_COPY_LINK_COUNT,
            state_only_copy_layout_v4().unwrap().links.len()
        );
    }

    #[test]
    fn fifty_random_off_domain_points_match_the_independent_relation_walk() {
        let (public, _) = fixture();
        let prepared = prepare_state_only_semantic_oracle().unwrap();
        let mut random = 0x243f_6a88_85a3_08d3u64;
        for sample in 0..50 {
            let point = core::array::from_fn(|_| random_qm31(&mut random));
            let openings = StateOnlySemanticOpenings {
                c1: StateOnlyPoseidonOpenings {
                    z: core::array::from_fn(|_| random_qm31(&mut random)),
                    succ_z: core::array::from_fn(|_| random_qm31(&mut random)),
                    xor12_z: core::array::from_fn(|_| random_qm31(&mut random)),
                },
                h1_z: random_qm31(&mut random),
            };
            let lambda = match sample {
                0 => QM31::ZERO,
                1 => QM31::ONE,
                _ => random_qm31(&mut random),
            };
            let chi = random_qm31(&mut random);
            assert_eq!(
                evaluate_state_only_semantic_oracle_prepared(
                    &public, &openings, &point, lambda, chi, &prepared,
                )
                .unwrap(),
                reference_semantic_oracle(&public, &openings, &point, lambda, chi, &prepared,),
                "off-domain sample {sample}"
            );
        }
    }

    #[test]
    fn every_surviving_copy_endpoint_has_a_local_corruption_tooth() {
        let (public, trace, h1, lambda, chi) = honest();
        let prepared = prepare_state_only_semantic_oracle().unwrap();
        for link in &prepared.copy.links {
            for (tuple, row) in [
                (link.producer, usize::from(link.producer_row)),
                (link.consumer, usize::from(link.consumer_row)),
            ] {
                let cell = tuple
                    .limbs
                    .into_iter()
                    .find_map(|limb| match limb {
                        TupleLimb::Cell(cell) => Some(cell),
                        TupleLimb::Zero => None,
                    })
                    .expect("every surviving endpoint has a committed limb");
                let mut bad = trace.clone();
                bad.c1[usize::from(cell.column)][usize::from(cell.row)] =
                    bad.c1[usize::from(cell.column)][usize::from(cell.row)].add(M31::ONE);
                let point = boolean_point(row);
                let openings = state_only_semantic_openings_at_point(&bad, &h1, &point).unwrap();
                assert_ne!(
                    evaluate_state_only_semantic_oracle_prepared(
                        &public, &openings, &point, lambda, chi, &prepared,
                    )
                    .unwrap()
                    .copy,
                    QM31::ZERO,
                    "copy link {} endpoint row {} escaped",
                    link.id,
                    row,
                );
            }
        }
    }
}
