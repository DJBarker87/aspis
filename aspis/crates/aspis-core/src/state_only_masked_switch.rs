//! Read-only profile-21 masked-switch PCS diagnostic.
//!
//! This module verifies the new commitment objects and the exact causal
//! switch schedule: X/F are committed before the target challenge and the
//! dedicated source-round work witness, delta follows that work witness, U
//! and the translated root precede both OOD samples, and final work precedes
//! q16. It authenticates both X/F and U at the same without-replacement query
//! positions and checks `F(q) + delta X(q) = U(q)` plus the natural-line
//! evaluation of the disclosed U coefficients.
//!
//! It deliberately does not bind `tX` to the production round-zero relation
//! or splice the translated root into the production FRI continuation. Those
//! are profile-21 integration obligations, so this module is diagnostic and
//! cannot authorize a state transition.

use alloc::vec::Vec;

use crate::circle::double_x;
use crate::circle_fri::{line_domain_x_for_circle, CircleFriError};
use crate::field::{qm31_m31_dot4, CM31, M31, QM31};
use crate::merkle::{leaf_hash, verify_radix4_binary_cap_minimal_subtree_bytes};
use crate::state_only_masked_switch_basis::{
    masked_switch_logical_to_natural, MASKED_SWITCH_UNIVERSAL_DIMENSION,
    MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION, MASKED_SWITCH_UNIVERSAL_RANDOMNESS_DIMENSION,
};
use crate::sumcheck::{TensorWeightError, WeightAccumulator};
use crate::transcript::{
    label, ChallengeSampleExhausted, OodSampleError, QuerySampleError, Transcript,
};
use crate::HashFn;

pub const MASKED_SWITCH_VERSION: u8 = 1;
pub const MASKED_SWITCH_COEFFICIENTS: usize = 35;
pub const MASKED_SWITCH_MESSAGE_COEFFICIENTS: usize = 19;
pub const MASKED_SWITCH_QUERY_COUNT: usize = 16;
pub const MASKED_SWITCH_LINE_DOMAIN_LOG: u32 = 17;
/// Production root-one leaves contain four consecutive line symbols, so the
/// Merkle tree has 2^15 leaves even though the line code has 2^17 symbols.
pub const MASKED_SWITCH_LEAF_DOMAIN_LOG: u32 = MASKED_SWITCH_LINE_DOMAIN_LOG - 2;
pub const MASKED_SWITCH_CIRCLE_DOMAIN_LOG: u32 = 19;
/// Conservative production normalization.  The atomic soundness ledger uses
/// g38 at pre-gamma, source/pre-delta, and final/pre-q; predicates cost the
/// verifier the same CU as the earlier g36 diagnostic.
pub const MASKED_SWITCH_SOURCE_WORK_BITS: u8 = 38;
pub const MASKED_SWITCH_FINAL_WORK_BITS: u8 = 38;
pub const MASKED_SWITCH_QUERY_MAX_DRAWS: usize = 128;
pub const MASKED_SWITCH_XF_LEAF_TAG: u8 = 0x60;
pub const MASKED_SWITCH_U_LEAF_TAG: u8 = 0x61;
pub const MASKED_SWITCH_LINE_VALUES_PER_LEAF: usize = 4;
pub const MASKED_SWITCH_XF_LEAF_BYTES: usize = 2 * MASKED_SWITCH_LINE_VALUES_PER_LEAF * 16;
pub const MASKED_SWITCH_U_LEAF_BYTES: usize = MASKED_SWITCH_LINE_VALUES_PER_LEAF * 16;
pub const MASKED_SWITCH_MAX_FRONTIER_NODES: usize = 512;
pub const MASKED_SWITCH_PROFILE_DOMAIN: &[u8] = b"aspis/state-only/profile21/masked-switch/v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MaskedSwitchVerifyError {
    UnexpectedEnd,
    TrailingBytes,
    Version,
    NonCanonicalField,
    SourceWork,
    FinalWork,
    Challenge,
    DeltaZeroExhausted,
    Ood,
    Query,
    QueryCount,
    FrontierCount,
    MerkleXf,
    MerkleU,
    AffineQuery,
    UQueryEvaluation,
    UBetaEvaluation { sample: u8 },
    LineDomain,
    Weight,
    LengthOverflow,
}

impl From<ChallengeSampleExhausted> for MaskedSwitchVerifyError {
    fn from(_: ChallengeSampleExhausted) -> Self {
        Self::Challenge
    }
}

impl From<OodSampleError> for MaskedSwitchVerifyError {
    fn from(_: OodSampleError) -> Self {
        Self::Ood
    }
}

impl From<QuerySampleError> for MaskedSwitchVerifyError {
    fn from(_: QuerySampleError) -> Self {
        Self::Query
    }
}

impl From<CircleFriError> for MaskedSwitchVerifyError {
    fn from(_: CircleFriError) -> Self {
        Self::LineDomain
    }
}

impl From<TensorWeightError> for MaskedSwitchVerifyError {
    fn from(_: TensorWeightError) -> Self {
        Self::Weight
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MaskedSwitchSchedule {
    pub target_challenge: QM31,
    pub delta: QM31,
    pub beta: [QM31; 2],
    pub queries: [u32; MASKED_SWITCH_QUERY_COUNT],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MaskedSwitchTraceEvent {
    HeaderParsed,
    TranscriptAndPrefixDone,
    QueryEquationsDone,
    XfMerkleDone,
    UMerkleDone,
}

pub type MaskedSwitchTrace = fn(MaskedSwitchTraceEvent);

struct Cursor<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8], MaskedSwitchVerifyError> {
        let end = self
            .position
            .checked_add(len)
            .ok_or(MaskedSwitchVerifyError::LengthOverflow)?;
        let result = self
            .bytes
            .get(self.position..end)
            .ok_or(MaskedSwitchVerifyError::UnexpectedEnd)?;
        self.position = end;
        Ok(result)
    }

    fn u8(&mut self) -> Result<u8, MaskedSwitchVerifyError> {
        Ok(self.take(1)?[0])
    }

    fn u16(&mut self) -> Result<u16, MaskedSwitchVerifyError> {
        Ok(u16::from_le_bytes(self.take(2)?.try_into().unwrap()))
    }

    fn u32(&mut self) -> Result<u32, MaskedSwitchVerifyError> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }

    fn u64(&mut self) -> Result<u64, MaskedSwitchVerifyError> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }

    fn root(&mut self) -> Result<[u8; 32], MaskedSwitchVerifyError> {
        Ok(self.take(32)?.try_into().unwrap())
    }

    fn qm31(&mut self) -> Result<QM31, MaskedSwitchVerifyError> {
        QM31::from_le_bytes(self.take(16)?).ok_or(MaskedSwitchVerifyError::NonCanonicalField)
    }
}

fn absorb_qm31_pair(transcript: &mut Transcript, label: u8, first: QM31, second: QM31) {
    let mut bytes = [0u8; 32];
    first.write_le_bytes(&mut bytes[..16]);
    second.write_le_bytes(&mut bytes[16..]);
    transcript.absorb(label, &bytes);
}

fn sample_nonzero_delta(transcript: &mut Transcript) -> Result<QM31, MaskedSwitchVerifyError> {
    // Zero has probability |QM31|^-1. Three exact-uniform attempts put this
    // explicit completeness abort below 2^-372.
    for _ in 0..3 {
        let candidate = transcript.challenge_qm31()?;
        if candidate != QM31::ZERO {
            return Ok(candidate);
        }
    }
    Err(MaskedSwitchVerifyError::DeltaZeroExhausted)
}

/// Natural line-tensor evaluation of 35 disclosed coefficients, with the
/// remaining coordinates of the fixed log-8 coefficient table equal to zero.
pub fn evaluate_masked_switch_line(
    coefficients: &[QM31; MASKED_SWITCH_COEFFICIENTS],
    mut point: QM31,
) -> Result<QM31, MaskedSwitchVerifyError> {
    // The fixed table has 256 positions but only the natural prefix 0..35 is
    // nonzero. Fold that sparse prefix from its low bit upward. An odd final
    // item is paired with an implicit zero, so it copies without a field
    // multiplication. This is exactly the tensor dot but takes 34
    // coefficient multiplications instead of 35 calls to weight_at(log8).
    let mut level = coefficients.to_vec();
    for _ in 0..8 {
        if level.len() == 1 {
            break;
        }
        let mut next = Vec::with_capacity((level.len() + 1) / 2);
        let mut chunks = level.chunks_exact(2);
        for pair in &mut chunks {
            next.push(pair[0].add(point.mul(pair[1])));
        }
        if let Some(&last) = chunks.remainder().first() {
            next.push(last);
        }
        level = next;
        point = double_x(point);
    }
    level
        .first()
        .copied()
        .ok_or(MaskedSwitchVerifyError::Weight)
}

/// Deliberately slower exact reference retained for random-point identity
/// tests of the sparse evaluator.
pub fn evaluate_masked_switch_line_reference(
    coefficients: &[QM31; MASKED_SWITCH_COEFFICIENTS],
    point: QM31,
) -> Result<QM31, MaskedSwitchVerifyError> {
    let mut weights = WeightAccumulator::empty(8);
    weights.add_line_tensor(QM31::ONE, point)?;
    Ok(coefficients
        .iter()
        .enumerate()
        .fold(QM31::ZERO, |sum, (index, coefficient)| {
            sum.add(coefficient.mul(weights.weight_at(index as u32)))
        }))
}

pub fn masked_switch_query_point(index: u32) -> Result<QM31, MaskedSwitchVerifyError> {
    let x = line_domain_x_for_circle(MASKED_SWITCH_CIRCLE_DOMAIN_LOG, 1, index as usize)?;
    Ok(QM31::from_cm31(CM31::from_m31(x)))
}

pub fn masked_switch_query_x(index: u32) -> Result<M31, MaskedSwitchVerifyError> {
    Ok(line_domain_x_for_circle(
        MASKED_SWITCH_CIRCLE_DOMAIN_LOG,
        1,
        index as usize,
    )?)
}

/// Exact q-only evaluator. Every sampled line-domain coordinate lies in M31,
/// so all 34 nontrivial sparse-fold products use `QM31 x M31`; generic beta
/// OOD points continue to use the extension-field evaluator above.
pub fn evaluate_masked_switch_line_at_m31(
    coefficients: &[QM31; MASKED_SWITCH_COEFFICIENTS],
    mut point: M31,
) -> Result<QM31, MaskedSwitchVerifyError> {
    let mut level = coefficients.to_vec();
    for _ in 0..8 {
        if level.len() == 1 {
            break;
        }
        let mut next = Vec::with_capacity((level.len() + 1) / 2);
        let mut chunks = level.chunks_exact(2);
        for pair in &mut chunks {
            next.push(pair[0].add(pair[1].mul_m31(point)));
        }
        if let Some(&last) = chunks.remainder().first() {
            next.push(last);
        }
        level = next;
        point = point.mul(point).double().sub(M31::ONE);
    }
    level
        .first()
        .copied()
        .ok_or(MaskedSwitchVerifyError::Weight)
}

/// Generate the natural line-tensor covector `[1, T_1(x), ...]` up to the
/// disclosed 35-coordinate prefix.  Each nonzero index reuses the product at
/// `index` with its least-significant set bit removed, so this takes exactly
/// 34 M31 products and no heap allocation.
fn masked_switch_line_weights_m31(mut point: M31) -> [M31; MASKED_SWITCH_COEFFICIENTS] {
    let mut factors = [M31::ZERO; 8];
    for factor in &mut factors {
        *factor = point;
        point = point.mul(point).double().sub(M31::ONE);
    }
    let mut weights = [M31::ZERO; MASKED_SWITCH_COEFFICIENTS];
    weights[0] = M31::ONE;
    for index in 1..MASKED_SWITCH_COEFFICIENTS {
        let bit = index.trailing_zeros() as usize;
        weights[index] = weights[index ^ (1usize << bit)].mul(factors[bit]);
    }
    weights
}

/// Four exact M31-point evaluations with one traversal of the disclosed U
/// coefficients.  This has the same polynomial as four calls to
/// `evaluate_masked_switch_line_at_m31`; it trades some raw M31 products for
/// fewer canonical reductions and shared coefficient loads on SBF.
pub fn evaluate_masked_switch_line_at_m31_four(
    coefficients: &[QM31; MASKED_SWITCH_COEFFICIENTS],
    points: [M31; 4],
) -> [QM31; 4] {
    let weights = points.map(masked_switch_line_weights_m31);
    qm31_m31_dot4(
        coefficients,
        [&weights[0], &weights[1], &weights[2], &weights[3]],
    )
}

/// Evaluate the profile-21 disclosed logical coordinates as the frozen
/// ordinary polynomial
///
/// `u0*x + u1 + sum_{i=2..18} u_i*x^(16+i)
///   + (x^2+1) sum_{j=0..15} u_{19+j}*x^j`.
///
/// This is the production beta/OOD evaluator for the logical-U wire.  It is
/// algebraically identical to converting through the pinned natural basis,
/// but avoids materializing that 35-by-35 transform.
pub fn evaluate_masked_switch_logical(
    logical: &[QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION],
    point: QM31,
) -> QM31 {
    let mut high = logical[MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION - 1];
    for coefficient in logical[2..MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION - 1]
        .iter()
        .rev()
    {
        high = high.mul(point).add(*coefficient);
    }
    let mut randomness = logical[MASKED_SWITCH_UNIVERSAL_DIMENSION - 1];
    for coefficient in logical
        [MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION..MASKED_SWITCH_UNIVERSAL_DIMENSION - 1]
        .iter()
        .rev()
    {
        randomness = randomness.mul(point).add(*coefficient);
    }
    logical[0]
        .mul(point)
        .add(logical[1])
        .add(high.mul(point.pow(18)))
        .add(randomness.mul(point.square().add(QM31::ONE)))
}

fn masked_switch_logical_weights_m31(point: M31) -> [M31; MASKED_SWITCH_UNIVERSAL_DIMENSION] {
    let mut powers = [M31::ZERO; MASKED_SWITCH_UNIVERSAL_DIMENSION];
    powers[0] = M31::ONE;
    for exponent in 1..MASKED_SWITCH_UNIVERSAL_DIMENSION {
        powers[exponent] = powers[exponent - 1].mul(point);
    }
    let mut weights = [M31::ZERO; MASKED_SWITCH_UNIVERSAL_DIMENSION];
    weights[0] = point;
    weights[1] = M31::ONE;
    for logical in 2..MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION {
        weights[logical] = powers[16 + logical];
    }
    let quadratic = point.mul(point).add(M31::ONE);
    for randomness in 0..MASKED_SWITCH_UNIVERSAL_RANDOMNESS_DIMENSION {
        weights[MASKED_SWITCH_UNIVERSAL_MESSAGE_DIMENSION + randomness] =
            quadratic.mul(powers[randomness]);
    }
    weights
}

/// Four exact production q evaluations of logical U. All public abscissae
/// lie in M31, so the fused dot uses only QM31-by-M31 products and traverses
/// the 35 disclosed coefficients once.
pub fn evaluate_masked_switch_logical_at_m31_four(
    logical: &[QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION],
    points: [M31; 4],
) -> [QM31; 4] {
    let weights = points.map(masked_switch_logical_weights_m31);
    qm31_m31_dot4(
        logical,
        [&weights[0], &weights[1], &weights[2], &weights[3]],
    )
}

/// Independent transform-through-natural reference for logical-U identity
/// guards. This is intentionally not used by the production verifier.
pub fn evaluate_masked_switch_logical_natural_reference(
    logical: &[QM31; MASKED_SWITCH_UNIVERSAL_DIMENSION],
    point: QM31,
) -> Result<QM31, MaskedSwitchVerifyError> {
    evaluate_masked_switch_line(&masked_switch_logical_to_natural(logical), point)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum UQueryBinding {
    /// Reference path: independently evaluate all 35 coefficients at q16.
    LiteralGeneric,
    /// Exact scalar reference specialized to the M31 line coordinate.
    LiteralM31Sparse,
    /// Production candidate: four exact M31-point evaluations fused into one
    /// coefficient traversal.
    LiteralM31Dot4,
}

fn verify_state_only_masked_switch_inner(
    proof: &[u8],
    statement_digest: &[u8; 32],
    hash: HashFn,
    diagnostic_unmined: bool,
    u_query_binding: UQueryBinding,
    trace: Option<MaskedSwitchTrace>,
) -> Result<MaskedSwitchSchedule, MaskedSwitchVerifyError> {
    let mut cursor = Cursor::new(proof);
    if cursor.u8()? != MASKED_SWITCH_VERSION {
        return Err(MaskedSwitchVerifyError::Version);
    }
    let xf_root = cursor.root()?;
    let t_x = cursor.qm31()?;
    let mu_f = cursor.qm31()?;
    if let Some(trace) = trace {
        trace(MaskedSwitchTraceEvent::HeaderParsed);
    }

    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, MASKED_SWITCH_PROFILE_DOMAIN);
    transcript.absorb(label::STATEMENT, statement_digest);
    transcript.absorb(label::M31_STATE_ONLY_SWITCH_XF_ROOT, &xf_root);
    let target_challenge = transcript.challenge_qm31()?;
    absorb_qm31_pair(
        &mut transcript,
        label::M31_STATE_ONLY_SWITCH_TARGETS,
        t_x,
        mu_f,
    );

    let source_work_nonce = cursor.u64()?;
    let source_work_ok = transcript.grinding_ok(source_work_nonce, MASKED_SWITCH_SOURCE_WORK_BITS);
    if !source_work_ok && !diagnostic_unmined {
        return Err(MaskedSwitchVerifyError::SourceWork);
    }
    transcript.absorb(
        label::M31_STATE_ONLY_SWITCH_SOURCE_POW_NONCE,
        &source_work_nonce.to_le_bytes(),
    );
    let delta = sample_nonzero_delta(&mut transcript)?;

    let mut u = [QM31::ZERO; MASKED_SWITCH_COEFFICIENTS];
    let u_start = cursor.position;
    for coefficient in &mut u {
        *coefficient = cursor.qm31()?;
    }
    transcript.absorb(
        label::M31_STATE_ONLY_SWITCH_U,
        &proof[u_start..cursor.position],
    );
    let translated_root = cursor.root()?;
    transcript.absorb(
        label::M31_STATE_ONLY_SWITCH_TRANSLATED_ROOT,
        &translated_root,
    );

    let beta = [
        transcript.challenge_ood_qm31()?,
        transcript.challenge_ood_qm31()?,
    ];
    for (sample, point) in beta.iter().enumerate() {
        let claimed = cursor.qm31()?;
        if claimed != evaluate_masked_switch_line(&u, *point)? {
            return Err(MaskedSwitchVerifyError::UBetaEvaluation {
                sample: sample as u8,
            });
        }
    }

    let final_work_nonce = cursor.u64()?;
    let final_work_ok = transcript.grinding_ok(final_work_nonce, MASKED_SWITCH_FINAL_WORK_BITS);
    if !final_work_ok && !diagnostic_unmined {
        return Err(MaskedSwitchVerifyError::FinalWork);
    }
    transcript.absorb(
        label::M31_STATE_ONLY_SWITCH_FINAL_POW_NONCE,
        &final_work_nonce.to_le_bytes(),
    );
    let query_vec = transcript.challenge_queries_without_replacement(
        MASKED_SWITCH_QUERY_COUNT,
        1u32 << MASKED_SWITCH_LINE_DOMAIN_LOG,
        MASKED_SWITCH_QUERY_MAX_DRAWS,
    )?;
    let queries: [u32; MASKED_SWITCH_QUERY_COUNT] = query_vec
        .try_into()
        .map_err(|_| MaskedSwitchVerifyError::QueryCount)?;
    let mut sorted_queries = queries;
    sorted_queries.sort_unstable();
    if let Some(trace) = trace {
        trace(MaskedSwitchTraceEvent::TranscriptAndPrefixDone);
    }
    let mut fused_direct = [QM31::ZERO; MASKED_SWITCH_QUERY_COUNT];
    if u_query_binding == UQueryBinding::LiteralM31Dot4 {
        for (chunk, output) in sorted_queries
            .chunks_exact(4)
            .zip(fused_direct.chunks_exact_mut(4))
        {
            let points = [
                masked_switch_query_x(chunk[0])?,
                masked_switch_query_x(chunk[1])?,
                masked_switch_query_x(chunk[2])?,
                masked_switch_query_x(chunk[3])?,
            ];
            output.copy_from_slice(&evaluate_masked_switch_line_at_m31_four(&u, points));
        }
    }
    let mut leaf_indices = sorted_queries.map(|query| query >> 2).to_vec();
    leaf_indices.dedup();
    if usize::from(cursor.u16()?) != leaf_indices.len() {
        return Err(MaskedSwitchVerifyError::QueryCount);
    }
    let mut xf_entries = Vec::with_capacity(leaf_indices.len());
    let mut u_entries = Vec::with_capacity(leaf_indices.len());
    let mut opened_leaves = Vec::with_capacity(leaf_indices.len());
    for &leaf_index in &leaf_indices {
        let xf_leaf = cursor.take(MASKED_SWITCH_XF_LEAF_BYTES)?;
        let u_leaf = cursor.take(MASKED_SWITCH_U_LEAF_BYTES)?;
        let mut x = [QM31::ZERO; MASKED_SWITCH_LINE_VALUES_PER_LEAF];
        let mut f = [QM31::ZERO; MASKED_SWITCH_LINE_VALUES_PER_LEAF];
        let mut u_values = [QM31::ZERO; MASKED_SWITCH_LINE_VALUES_PER_LEAF];
        for slot in 0..MASKED_SWITCH_LINE_VALUES_PER_LEAF {
            x[slot] = QM31::from_le_bytes(&xf_leaf[16 * slot..16 * (slot + 1)])
                .ok_or(MaskedSwitchVerifyError::NonCanonicalField)?;
            let f_start = 16 * (MASKED_SWITCH_LINE_VALUES_PER_LEAF + slot);
            f[slot] = QM31::from_le_bytes(&xf_leaf[f_start..f_start + 16])
                .ok_or(MaskedSwitchVerifyError::NonCanonicalField)?;
            u_values[slot] = QM31::from_le_bytes(&u_leaf[16 * slot..16 * (slot + 1)])
                .ok_or(MaskedSwitchVerifyError::NonCanonicalField)?;
        }
        opened_leaves.push((leaf_index, x, f, u_values));
        xf_entries.push((
            leaf_index,
            leaf_hash(hash, MASKED_SWITCH_XF_LEAF_TAG, xf_leaf),
        ));
        u_entries.push((
            leaf_index,
            leaf_hash(hash, MASKED_SWITCH_U_LEAF_TAG, u_leaf),
        ));
    }
    let mut leaf_ordinal = 0usize;
    for (query_ordinal, &query) in sorted_queries.iter().enumerate() {
        let wanted = query >> 2;
        while opened_leaves[leaf_ordinal].0 < wanted {
            leaf_ordinal += 1;
        }
        if opened_leaves[leaf_ordinal].0 != wanted {
            return Err(MaskedSwitchVerifyError::QueryCount);
        }
        let slot = (query & 3) as usize;
        let (_, x, f, u_values) = opened_leaves[leaf_ordinal];
        let x_value = x[slot];
        let f_value = f[slot];
        let u_value = u_values[slot];
        if f_value.add(delta.mul(x_value)) != u_value {
            return Err(MaskedSwitchVerifyError::AffineQuery);
        }
        let direct = match u_query_binding {
            UQueryBinding::LiteralGeneric => {
                evaluate_masked_switch_line(&u, masked_switch_query_point(query)?)?
            }
            UQueryBinding::LiteralM31Sparse => {
                evaluate_masked_switch_line_at_m31(&u, masked_switch_query_x(query)?)?
            }
            UQueryBinding::LiteralM31Dot4 => fused_direct[query_ordinal],
        };
        if direct != u_value {
            return Err(MaskedSwitchVerifyError::UQueryEvaluation);
        }
    }

    let xf_frontier_count = cursor.u32()? as usize;
    if xf_frontier_count > MASKED_SWITCH_MAX_FRONTIER_NODES {
        return Err(MaskedSwitchVerifyError::FrontierCount);
    }
    let xf_frontier = cursor.take(
        xf_frontier_count
            .checked_mul(32)
            .ok_or(MaskedSwitchVerifyError::LengthOverflow)?,
    )?;
    let u_frontier_count = cursor.u32()? as usize;
    if u_frontier_count > MASKED_SWITCH_MAX_FRONTIER_NODES {
        return Err(MaskedSwitchVerifyError::FrontierCount);
    }
    let u_frontier = cursor.take(
        u_frontier_count
            .checked_mul(32)
            .ok_or(MaskedSwitchVerifyError::LengthOverflow)?,
    )?;
    if cursor.position != proof.len() {
        return Err(MaskedSwitchVerifyError::TrailingBytes);
    }
    if let Some(trace) = trace {
        trace(MaskedSwitchTraceEvent::QueryEquationsDone);
    }

    let mut level = Vec::with_capacity(MASKED_SWITCH_QUERY_COUNT);
    let mut next = Vec::with_capacity(MASKED_SWITCH_QUERY_COUNT);
    if !verify_radix4_binary_cap_minimal_subtree_bytes(
        hash,
        &xf_root,
        MASKED_SWITCH_LEAF_DOMAIN_LOG,
        &xf_entries,
        xf_frontier,
        &mut level,
        &mut next,
    ) {
        return Err(MaskedSwitchVerifyError::MerkleXf);
    }
    if let Some(trace) = trace {
        trace(MaskedSwitchTraceEvent::XfMerkleDone);
    }
    if !verify_radix4_binary_cap_minimal_subtree_bytes(
        hash,
        &translated_root,
        MASKED_SWITCH_LEAF_DOMAIN_LOG,
        &u_entries,
        u_frontier,
        &mut level,
        &mut next,
    ) {
        return Err(MaskedSwitchVerifyError::MerkleU);
    }
    if let Some(trace) = trace {
        trace(MaskedSwitchTraceEvent::UMerkleDone);
    }

    Ok(MaskedSwitchSchedule {
        target_challenge,
        delta,
        beta,
        queries,
    })
}

/// Verify the standalone commitment/schedule/query slice with both positioned
/// g36 predicates enforced. A future production composition may call only
/// this no-bypass API.
pub fn verify_state_only_masked_switch(
    proof: &[u8],
    statement_digest: &[u8; 32],
    hash: HashFn,
) -> Result<MaskedSwitchSchedule, MaskedSwitchVerifyError> {
    verify_state_only_masked_switch_inner(
        proof,
        statement_digest,
        hash,
        false,
        UQueryBinding::LiteralM31Dot4,
        None,
    )
}

/// Read-only measurement API. It executes both grinding hashes and preserves
/// nonce absorption byte-for-byte, but permits unmined fixture nonces. The
/// tag-45 diagnostic is the only on-chain caller; no acceptance path may call
/// this function.
pub fn verify_state_only_masked_switch_diagnostic_unmined(
    proof: &[u8],
    statement_digest: &[u8; 32],
    hash: HashFn,
) -> Result<MaskedSwitchSchedule, MaskedSwitchVerifyError> {
    verify_state_only_masked_switch_inner(
        proof,
        statement_digest,
        hash,
        true,
        UQueryBinding::LiteralM31Dot4,
        None,
    )
}

/// Tag-45 phase-instrumented variant of the unmined diagnostic. It has the
/// same acceptance predicate as `verify_state_only_masked_switch_diagnostic_unmined`.
pub fn verify_state_only_masked_switch_diagnostic_unmined_traced(
    proof: &[u8],
    statement_digest: &[u8; 32],
    hash: HashFn,
    trace: MaskedSwitchTrace,
) -> Result<MaskedSwitchSchedule, MaskedSwitchVerifyError> {
    verify_state_only_masked_switch_inner(
        proof,
        statement_digest,
        hash,
        true,
        UQueryBinding::LiteralGeneric,
        Some(trace),
    )
}

/// Direct-binding production-cost candidate. It checks every disclosed U
/// coefficient evaluation literally, specializing only the public q point
/// from generic QM31 to its exact M31 line-domain representation.
pub fn verify_state_only_masked_switch_production_equivalent_unmined_traced(
    proof: &[u8],
    statement_digest: &[u8; 32],
    hash: HashFn,
    trace: MaskedSwitchTrace,
) -> Result<MaskedSwitchSchedule, MaskedSwitchVerifyError> {
    verify_state_only_masked_switch_inner(
        proof,
        statement_digest,
        hash,
        true,
        UQueryBinding::LiteralM31Dot4,
        Some(trace),
    )
}

/// Scalar M31 sparse-fold reference for the four-query fused evaluator.
pub fn verify_state_only_masked_switch_m31_sparse_unmined_traced(
    proof: &[u8],
    statement_digest: &[u8; 32],
    hash: HashFn,
    trace: MaskedSwitchTrace,
) -> Result<MaskedSwitchSchedule, MaskedSwitchVerifyError> {
    verify_state_only_masked_switch_inner(
        proof,
        statement_digest,
        hash,
        true,
        UQueryBinding::LiteralM31Sparse,
        Some(trace),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{CM31, M31, P};

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31 {
                a: M31(seed.wrapping_mul(0x9e37_79b9) & P),
                b: M31(seed.rotate_left(7).wrapping_add(17) & P),
            },
            c1: CM31 {
                a: M31(seed.rotate_left(13).wrapping_add(29) & P),
                b: M31(seed.rotate_left(19).wrapping_add(43) & P),
            },
        }
    }

    #[test]
    fn sparse_line_evaluator_matches_weight_accumulator_at_64_points() {
        let coefficients = core::array::from_fn(|index| q(index as u32 + 101));
        for sample in 0..64u32 {
            let point = q(10_003 + 97 * sample);
            assert_eq!(
                evaluate_masked_switch_line(&coefficients, point).unwrap(),
                evaluate_masked_switch_line_reference(&coefficients, point).unwrap(),
                "sample={sample}",
            );
        }
    }

    #[test]
    fn m31_query_evaluator_matches_independent_tensor_reference() {
        // This is the exact q16 schedule of the profile-21 fixture.  The
        // reference side deliberately goes through WeightAccumulator, not
        // either sparse-fold implementation, so a shared indexing or
        // Chebyshev-recurrence defect cannot make the guard vacuous.
        const QUERIES: [u32; MASKED_SWITCH_QUERY_COUNT] = [
            48_161, 73_579, 237, 70_782, 36_889, 127_428, 844, 12_677, 57_425, 17_807, 55_970,
            43_725, 27_037, 54_052, 55_238, 37_750,
        ];

        for vector in 0..16u32 {
            let coefficients =
                core::array::from_fn(|index| q(50_003 + 4_099 * vector + 193 * index as u32));
            for &query in &QUERIES {
                let x = masked_switch_query_x(query).unwrap();
                let point = QM31::from_cm31(CM31::from_m31(x));
                let optimized = evaluate_masked_switch_line_at_m31(&coefficients, x).unwrap();
                let generic = evaluate_masked_switch_line(&coefficients, point).unwrap();
                let reference =
                    evaluate_masked_switch_line_reference(&coefficients, point).unwrap();
                assert_eq!(optimized, reference, "vector={vector}, query={query}");
                assert_eq!(generic, reference, "vector={vector}, query={query}");
            }
        }

        // Exercise ordinary random M31 coordinates too, so the test does not
        // depend only on one transcript schedule or on circle-domain points.
        for sample in 0..128u32 {
            let coefficients =
                core::array::from_fn(|index| q(90_011 + 5_003 * sample + 271 * index as u32));
            let x = M31(sample.wrapping_mul(0x9e37_79b9) & P);
            let point = QM31::from_cm31(CM31::from_m31(x));
            assert_eq!(
                evaluate_masked_switch_line_at_m31(&coefficients, x).unwrap(),
                evaluate_masked_switch_line_reference(&coefficients, point).unwrap(),
                "sample={sample}",
            );
        }
    }

    #[test]
    fn fused_four_query_evaluator_matches_sparse_and_tensor_reference() {
        const QUERIES: [u32; MASKED_SWITCH_QUERY_COUNT] = [
            48_161, 73_579, 237, 70_782, 36_889, 127_428, 844, 12_677, 57_425, 17_807, 55_970,
            43_725, 27_037, 54_052, 55_238, 37_750,
        ];
        let mut sorted = QUERIES;
        sorted.sort_unstable();
        for vector in 0..32u32 {
            let coefficients =
                core::array::from_fn(|index| q(130_003 + 6_001 * vector + 307 * index as u32));
            for queries in sorted.chunks_exact(4) {
                let points =
                    core::array::from_fn(|slot| masked_switch_query_x(queries[slot]).unwrap());
                let fused = evaluate_masked_switch_line_at_m31_four(&coefficients, points);
                for slot in 0..4 {
                    let point = QM31::from_cm31(CM31::from_m31(points[slot]));
                    assert_eq!(
                        fused[slot],
                        evaluate_masked_switch_line_at_m31(&coefficients, points[slot]).unwrap(),
                        "vector={vector}, query={}",
                        queries[slot],
                    );
                    assert_eq!(
                        fused[slot],
                        evaluate_masked_switch_line_reference(&coefficients, point).unwrap(),
                        "vector={vector}, query={}",
                        queries[slot],
                    );
                }
            }
        }

        for sample in 0..64u32 {
            let coefficients =
                core::array::from_fn(|index| q(190_027 + 7_001 * sample + 331 * index as u32));
            let points = core::array::from_fn(|slot| {
                M31(sample
                    .wrapping_mul(0x9e37_79b9)
                    .wrapping_add(0x7f4a_7c15u32.wrapping_mul(slot as u32 + 1))
                    & P)
            });
            let fused = evaluate_masked_switch_line_at_m31_four(&coefficients, points);
            for slot in 0..4 {
                let point = QM31::from_cm31(CM31::from_m31(points[slot]));
                assert_eq!(
                    fused[slot],
                    evaluate_masked_switch_line_reference(&coefficients, point).unwrap(),
                    "sample={sample}, slot={slot}",
                );
            }
        }
    }

    #[test]
    fn logical_u_generic_and_fused_m31_evaluators_match_natural_reference() {
        for sample in 0..64u32 {
            let logical =
                core::array::from_fn(|index| q(240_007 + 7_919 * sample + 359 * index as u32));
            let generic_point = q(310_019 + 401 * sample);
            assert_eq!(
                evaluate_masked_switch_logical(&logical, generic_point),
                evaluate_masked_switch_logical_natural_reference(&logical, generic_point).unwrap(),
                "generic sample={sample}",
            );

            let points = core::array::from_fn(|slot| {
                M31(sample
                    .wrapping_mul(0x9e37_79b9)
                    .wrapping_add(0x6a09_e667u32.wrapping_mul(slot as u32 + 1))
                    & P)
            });
            let fused = evaluate_masked_switch_logical_at_m31_four(&logical, points);
            for slot in 0..4 {
                let point = QM31::from_cm31(CM31::from_m31(points[slot]));
                assert_eq!(
                    fused[slot],
                    evaluate_masked_switch_logical_natural_reference(&logical, point).unwrap(),
                    "fused sample={sample}, slot={slot}",
                );
            }
        }
    }
}
