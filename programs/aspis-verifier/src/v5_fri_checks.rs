//! Isolated arithmetic checker for the v5 private PCS opening forest.
//!
//! The five Merkle sections are authenticated by `v5_private_openings`.  This
//! module consumes that authenticated view and checks the unchanged four-round
//! rate-1/512 circle-FRI chain.  It deliberately owns no transcript prefix:
//! production callers must derive `gamma`, the four fold challenges, and the
//! pre-query transcript state from the complete v5 Fiat--Shamir schedule.

use aspis_core::circle_fri::{
    derive_query_fold_inverses_for_circle,
    normalized_circle_to_line_arity4_prepared_polynomial_refs, CircleFriError,
};
use aspis_core::circle_hiding_prefix::PAYMENT_HIDING_QUERY_DRAW_LIMIT;
use aspis_core::circle_line_merkle::CIRCLE_LINE_TAGS;
use aspis_core::circle_merkle::{CIRCLE_C1_LAYER0_TAG, CIRCLE_C2_LAYER0_TAG};
use aspis_core::circle_pcs_shape::{CirclePcsDecodeError, CirclePcsPreparedClaims, CirclePcsShape};
use aspis_core::circle_query::{
    check_fixed_line_transition_prepared_polynomial_powers,
    check_fixed_terminal_transition_prepared_polynomial_refs, CircleQueryError,
};
use aspis_core::field::{
    qm31_m31_dot4_prepared_limbs_4b_bytes, qm31_sum_products3_prepared, PreparedQm31Multiplier,
    CM31, M31, P, QM31,
};
use aspis_core::state_only_prefix::{
    STATE_ONLY_SPEND_GRINDING_BITS, STATE_ONLY_SPEND_QUERY_CANDIDATE_COUNT,
    STATE_ONLY_SPEND_QUERY_COUNT,
};
use aspis_core::transcript::{label, QuerySampleError, Transcript};

use super::private_openings::{
    VerifiedV5PrivateOpenings, V5_PRIVATE_LAYER0_LEAVES, V5_PRIVATE_VALUE_WIDTHS,
};

pub const V5_FRI_QUERY_COUNT: usize = STATE_ONLY_SPEND_QUERY_COUNT as usize;
pub const V5_FRI_ROUNDS: usize = 4;
pub const V5_FRI_OPENING_POINTS: usize = 4;
pub const V5_FRI_TOTAL_COLUMNS: usize = 19;
pub const V5_FRI_FINAL_COEFFICIENTS: usize = 4;
pub const V5_FRI_FINAL_BYTES: usize = V5_FRI_FINAL_COEFFICIENTS * 16;
const V5_FRI_C1_COLUMNS: usize = 16;
const V5_FRI_C2_COLUMNS: usize = 3;

/// The exact additive PCS shape authenticated by the v5 private suffix.
pub const V5_FRI_PCS_SHAPE: CirclePcsShape = CirclePcsShape {
    trace_log_size: 10,
    domain_log_size: 19,
    query_count: STATE_ONLY_SPEND_QUERY_COUNT,
    opening_points: V5_FRI_OPENING_POINTS as u8,
    c1_columns: 16,
    c2_columns: 3,
    c1_layer0_tag: CIRCLE_C1_LAYER0_TAG,
    c2_layer0_tag: CIRCLE_C2_LAYER0_TAG,
    later_layer_tags: CIRCLE_LINE_TAGS,
};

const _: () = assert!(V5_FRI_QUERY_COUNT == 18);
const _: () = assert!(V5_FRI_TOTAL_COLUMNS == V5_FRI_C1_COLUMNS + V5_FRI_C2_COLUMNS);
const _: () = assert!(V5_FRI_PCS_SHAPE.opening_points as usize == V5_FRI_OPENING_POINTS);
const _: () = assert!(V5_FRI_PCS_SHAPE.total_columns() == V5_FRI_TOTAL_COLUMNS);
const _: () = assert!(V5_PRIVATE_LAYER0_LEAVES == 1 << 17);
const _: () = assert!(V5_PRIVATE_VALUE_WIDTHS[0] == 256);
const _: () = assert!(V5_PRIVATE_VALUE_WIDTHS[1] == 192);
// The exact fused kernels defer reductions only within these bounds.  Every
// multiplicand is a canonical M31 value, so neither u64 accumulator can
// overflow.  Four products bound each full PCS-claim block and each C1 slot
// dot; three bound the final claim block and the C2 Karatsuba-channel dot.
const M31_MAX_PRODUCT: u128 = (P as u128 - 1) * (P as u128 - 1);
const _: () = assert!(4 * M31_MAX_PRODUCT < (1u128 << 64));
const _: () = assert!(3 * M31_MAX_PRODUCT < (1u128 << 64));

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V5QueryBindingError {
    NonCanonicalFinal { coefficient: usize },
    GrindingRejected,
    QuerySelectorOutOfRange { selector: u8 },
    Query(QuerySampleError),
}

impl From<QuerySampleError> for V5QueryBindingError {
    fn from(error: QuerySampleError) -> Self {
        Self::Query(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V5FriCheckError {
    Decode(CirclePcsDecodeError),
    Fold(CircleFriError),
    Query(CircleQueryError),
    QueryCountMismatch { expected: usize, actual: usize },
    PreparedShape,
    MissingOpening { layer: u8, index: u32 },
    FirstFoldMismatch { query: u32 },
    NonCanonicalLater { layer: u8, offset: usize },
}

impl From<CirclePcsDecodeError> for V5FriCheckError {
    fn from(error: CirclePcsDecodeError) -> Self {
        Self::Decode(error)
    }
}

impl From<CircleFriError> for V5FriCheckError {
    fn from(error: CircleFriError) -> Self {
        Self::Fold(error)
    }
}

impl From<CircleQueryError> for V5FriCheckError {
    fn from(error: CircleQueryError) -> Self {
        Self::Query(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V5FriCheckSink {
    /// Sum of the already-computed layer-zero fold results.  Returning it
    /// gives the CU probe a cheap value sink without repeating later folds.
    pub folded_layer0_sum: QM31,
}

/// Canonically decoded fixed-shape v5 PCS claims and their shared gamma-power
/// table.  The inner representation is deliberately private: relation code
/// may reuse the four point-major aggregates only when they came from the
/// same fixed-shape decoder used by the FRI layer-zero checker.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5PreparedPcsClaims {
    inner: CirclePcsPreparedClaims,
    c1_weight_limbs: [[u32; 4]; V5_FRI_C1_COLUMNS],
    c2_multipliers: [PreparedQm31Multiplier; V5_FRI_C2_COLUMNS],
}

impl V5PreparedPcsClaims {
    pub fn point_claims(&self) -> &[QM31; V5_FRI_OPENING_POINTS] {
        self.inner
            .claims
            .as_slice()
            .try_into()
            .expect("fixed v5 claim count established by constructor")
    }
}

/// Build every power `gamma^0 .. gamma^18` with the minimum seventeen new
/// field elements.  Even exponents use the exact quadratic-extension square
/// (seven M31 products); odd exponents multiply the preceding even power by
/// `gamma`.  This is the same natural power basis as the generic PCS decoder.
#[inline(always)]
fn v5_gamma_powers(gamma: QM31) -> [QM31; V5_FRI_TOTAL_COLUMNS] {
    let mut powers = [QM31::ZERO; V5_FRI_TOTAL_COLUMNS];
    powers[0] = QM31::ONE;
    powers[1] = gamma;
    let mut exponent = 2;
    while exponent < V5_FRI_TOTAL_COLUMNS {
        powers[exponent] = if exponent & 1 == 0 {
            powers[exponent / 2].square()
        } else {
            powers[exponent - 1].mul(gamma)
        };
        exponent += 1;
    }
    powers
}

#[inline(never)]
fn v5_claim_dot_block(
    powers: &[QM31; V5_FRI_TOTAL_COLUMNS],
    values: &[QM31; V5_FRI_TOTAL_COLUMNS],
    start: usize,
    count: usize,
) -> QM31 {
    debug_assert!(count == 3 || count == 4);
    let mut sums = [[0u64; 3]; 3];
    let mut index = 0;
    while index < count {
        let left = powers[start + index];
        let right = values[start + index];
        let left_sum = left.c0.add(left.c1);
        let right_sum = right.c0.add(right.c1);
        let left_components = [
            [left.c0.a, left.c0.b, left.c0.a.add(left.c0.b)],
            [left.c1.a, left.c1.b, left.c1.a.add(left.c1.b)],
            [left_sum.a, left_sum.b, left_sum.a.add(left_sum.b)],
        ];
        let right_components = [
            [right.c0.a, right.c0.b, right.c0.a.add(right.c0.b)],
            [right.c1.a, right.c1.b, right.c1.a.add(right.c1.b)],
            [right_sum.a, right_sum.b, right_sum.a.add(right_sum.b)],
        ];
        let mut component = 0;
        while component < 3 {
            let mut channel = 0;
            while channel < 3 {
                sums[component][channel] += left_components[component][channel].0 as u64
                    * right_components[component][channel].0 as u64;
                channel += 1;
            }
            component += 1;
        }
        index += 1;
    }

    let reconstruct = |channels: [u64; 3]| {
        let m0 = M31::reduce_u64(channels[0]);
        let m1 = M31::reduce_u64(channels[1]);
        let m2 = M31::reduce_u64(channels[2]);
        CM31 {
            a: m0.sub(m1),
            b: m2.sub(m0).sub(m1),
        }
    };
    let m0 = reconstruct(sums[0]);
    let m1 = reconstruct(sums[1]);
    let m2 = reconstruct(sums[2]);
    let r_m1 = CM31 {
        a: m1.a.double().sub(m1.b),
        b: m1.a.add(m1.b.double()),
    };
    QM31 {
        c0: m0.add(r_m1),
        c1: m2.sub(m0).sub(m1),
    }
}

/// Decode the point-major `4 * 19` claim table and prepare the one generator
/// power table shared by the relation and all layer-zero queries.
///
/// Each point claim is the exact five-block sum `4 + 4 + 4 + 4 + 3` in
/// canonical slot order.  Karatsuba product channels are reduced once per
/// block rather than once per scalar product; reconstruction is M31-linear,
/// so the result is mathematically identical to the literal nineteen-product
/// dot.  The same power table serves all four points; its final three weights
/// are then prepared once for the layer-zero helper combiner.
pub fn prepare_v5_pcs_claims(
    gamma: QM31,
    point_major_claim_bytes: &[u8],
) -> Result<V5PreparedPcsClaims, V5FriCheckError> {
    let shape = V5_FRI_PCS_SHAPE
        .validate()
        .map_err(CirclePcsDecodeError::from)?;
    let expected = shape.evaluation_bytes();
    if point_major_claim_bytes.len() != expected {
        return Err(CirclePcsDecodeError::EvaluationLength {
            expected,
            actual: point_major_claim_bytes.len(),
        }
        .into());
    }

    let powers = v5_gamma_powers(gamma);
    let c1_weight_limbs = core::array::from_fn(|column| {
        let weight = powers[column];
        [weight.c0.a.0, weight.c0.b.0, weight.c1.a.0, weight.c1.b.0]
    });
    let c2_multipliers = core::array::from_fn(|helper| {
        PreparedQm31Multiplier::new(powers[V5_FRI_C1_COLUMNS + helper])
    });
    let mut claims = [QM31::ZERO; V5_FRI_OPENING_POINTS];
    for (point, claim) in claims.iter_mut().enumerate() {
        let mut values = [QM31::ZERO; V5_FRI_TOTAL_COLUMNS];
        for (column, value) in values.iter_mut().enumerate() {
            let index = point * V5_FRI_TOTAL_COLUMNS + column;
            let offset = index * 16;
            *value = QM31::from_le_bytes(&point_major_claim_bytes[offset..offset + 16])
                .ok_or(CirclePcsDecodeError::NonCanonicalEvaluation { index })?;
        }
        *claim = v5_claim_dot_block(&powers, &values, 0, 4)
            .add(v5_claim_dot_block(&powers, &values, 4, 4))
            .add(v5_claim_dot_block(&powers, &values, 8, 4))
            .add(v5_claim_dot_block(&powers, &values, 12, 4))
            .add(v5_claim_dot_block(&powers, &values, 16, 3));
    }
    let inner = CirclePcsPreparedClaims {
        claims: claims.to_vec(),
        powers: powers.to_vec(),
    };
    Ok(V5PreparedPcsClaims {
        inner,
        c1_weight_limbs,
        c2_multipliers,
    })
}

/// Continue an already-verified v5 transcript at the exact frozen Spend tail:
/// bind the final polynomial, check and absorb final work, bind the q18
/// candidate selector, then sample without replacement from the log-17 fibre
/// universe.  The caller must supply the transcript after all roots, OOD
/// values, relation sumchecks, fold-work records, and fold challenges have
/// been processed.  A proof-carried transcript state is not sufficient.
pub fn bind_final_and_derive_v5_queries(
    transcript: &mut Transcript,
    final_polynomial_bytes: &[u8; V5_FRI_FINAL_BYTES],
    final_nonce: u64,
    query_selector: u8,
    check_pow: bool,
) -> Result<([QM31; V5_FRI_FINAL_COEFFICIENTS], [u32; V5_FRI_QUERY_COUNT]), V5QueryBindingError> {
    let mut final_polynomial = [QM31::ZERO; V5_FRI_FINAL_COEFFICIENTS];
    for (coefficient, output) in final_polynomial.iter_mut().enumerate() {
        let start = coefficient * 16;
        *output = QM31::from_le_bytes(&final_polynomial_bytes[start..start + 16])
            .ok_or(V5QueryBindingError::NonCanonicalFinal { coefficient })?;
    }

    transcript.absorb(label::M31_CIRCLE_FINAL_TENSOR_POLY, final_polynomial_bytes);
    if check_pow && !transcript.grinding_ok(final_nonce, STATE_ONLY_SPEND_GRINDING_BITS) {
        return Err(V5QueryBindingError::GrindingRejected);
    }
    transcript.absorb(label::GRIND_NONCE, &final_nonce.to_le_bytes());
    if query_selector >= STATE_ONLY_SPEND_QUERY_CANDIDATE_COUNT {
        return Err(V5QueryBindingError::QuerySelectorOutOfRange {
            selector: query_selector,
        });
    }
    transcript.absorb(label::M31_STATE_ONLY_QUERY_CANDIDATE, &[query_selector]);
    let queries = transcript.challenge_queries_without_replacement(
        V5_FRI_QUERY_COUNT,
        V5_PRIVATE_LAYER0_LEAVES as u32,
        PAYMENT_HIDING_QUERY_DRAW_LIMIT,
    )?;
    Ok((
        final_polynomial,
        queries
            .try_into()
            .expect("successful fixed-count transcript sampling"),
    ))
}

fn opening_value_for_monotone_index<'a>(
    opening: &aspis_core::state_only_private_openings::StateOnlyPrivateOpening<'a>,
    indices: &[u32],
    ordinal: &mut usize,
    index: u32,
    layer: u8,
) -> Result<&'a [u8], V5FriCheckError> {
    while *ordinal < indices.len() && indices[*ordinal] < index {
        *ordinal += 1;
    }
    if indices.get(*ordinal).copied() != Some(index) {
        return Err(V5FriCheckError::MissingOpening { layer, index });
    }
    opening
        .value(*ordinal)
        .ok_or(V5FriCheckError::MissingOpening { layer, index })
}

#[inline(always)]
fn first_noncanonical_m31_offset(bytes: &[u8]) -> usize {
    bytes
        .chunks_exact(4)
        .position(|encoded| {
            u32::from_le_bytes([encoded[0], encoded[1], encoded[2], encoded[3]]) >= P
        })
        .map_or(0, |index| index * 4)
}

/// Exact fixed-width specialization of `gamma_combine_circle_pcs_layer0` for
/// v5's 16 M31 columns followed by three QM31 helper columns.
///
/// It retains all 19 products in the same slot-major/helper-major wire order.
/// The only arithmetic change is to reduce four C1 products and the three C2
/// Karatsuba products in bounded u64 accumulators instead of reducing each
/// product separately.  Field linearity and the compile-time overflow bounds
/// above make this exactly equal in QM31, not an approximation.
fn gamma_combine_v5_layer0_exact(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    prepared: &V5PreparedPcsClaims,
) -> Result<[QM31; 4], CirclePcsDecodeError> {
    let c1_expected = V5_PRIVATE_VALUE_WIDTHS[0];
    let c2_expected = V5_PRIVATE_VALUE_WIDTHS[1];
    if c1_leaf.len() != c1_expected {
        return Err(CirclePcsDecodeError::C1LeafLength {
            expected: c1_expected,
            actual: c1_leaf.len(),
        });
    }
    if c2_leaf.len() != c2_expected {
        return Err(CirclePcsDecodeError::C2LeafLength {
            expected: c2_expected,
            actual: c2_leaf.len(),
        });
    }

    let mut combined = qm31_m31_dot4_prepared_limbs_4b_bytes::<V5_FRI_C1_COLUMNS>(
        &prepared.c1_weight_limbs,
        c1_leaf,
    )
    .ok_or_else(|| CirclePcsDecodeError::NonCanonicalC1 {
        offset: first_noncanonical_m31_offset(c1_leaf),
    })?;

    let mut helper_values = [[QM31::ZERO; V5_FRI_C2_COLUMNS]; 4];
    for helper in 0..V5_FRI_C2_COLUMNS {
        for (slot, values) in helper_values.iter_mut().enumerate() {
            let offset = (helper * 4 + slot) * 16;
            values[helper] = QM31::from_le_bytes(&c2_leaf[offset..offset + 16])
                .ok_or(CirclePcsDecodeError::NonCanonicalC2 { offset })?;
        }
    }
    for (slot, output) in combined.iter_mut().enumerate() {
        *output = output.add(qm31_sum_products3_prepared(
            &prepared.c2_multipliers,
            &helper_values[slot],
        ));
    }
    Ok(combined)
}

/// Check every layer0 -> line1, line1 -> line2, line2 -> line3, and
/// line3 -> final transition against one authenticated private opening forest.
/// The returned sink adds no arithmetic beyond the checked layer-zero folds.
pub fn check_v5_fri_queries(
    openings: &VerifiedV5PrivateOpenings<'_>,
    prepared: &V5PreparedPcsClaims,
    alphas: [QM31; V5_FRI_ROUNDS],
    final_polynomial: [QM31; V5_FRI_FINAL_COEFFICIENTS],
    inverse: fn(M31) -> M31,
) -> Result<V5FriCheckSink, V5FriCheckError> {
    let shape = V5_FRI_PCS_SHAPE
        .validate()
        .map_err(CirclePcsDecodeError::from)?;
    let queries = &openings.indices.layer0;
    if queries.len() != V5_FRI_QUERY_COUNT {
        return Err(V5FriCheckError::QueryCountMismatch {
            expected: V5_FRI_QUERY_COUNT,
            actual: queries.len(),
        });
    }
    if prepared.inner.powers.len() != shape.total_columns()
        || prepared.inner.claims.len() != V5_FRI_OPENING_POINTS
    {
        return Err(V5FriCheckError::PreparedShape);
    }
    let coordinates = derive_query_fold_inverses_for_circle(
        u32::from(shape.domain_log_size),
        queries,
        [
            &openings.indices.later[0],
            &openings.indices.later[1],
            &openings.indices.later[2],
        ],
        inverse,
    )?;

    let alpha_powers = alphas.map(|alpha| {
        let alpha_squared = alpha.square();
        [
            PreparedQm31Multiplier::new(alpha),
            PreparedQm31Multiplier::new(alpha_squared),
            PreparedQm31Multiplier::new(alpha_squared.mul(alpha)),
        ]
    });

    let mut folded_layer0_sum = QM31::ZERO;
    let mut layer1_ordinal = 0;
    for (ordinal, &query) in queries.iter().enumerate() {
        let c1 = openings
            .c1
            .value(ordinal)
            .ok_or(V5FriCheckError::MissingOpening {
                layer: 0,
                index: query,
            })?;
        let c2 = openings
            .c2
            .value(ordinal)
            .ok_or(V5FriCheckError::MissingOpening {
                layer: 0,
                index: query,
            })?;
        let combined = gamma_combine_v5_layer0_exact(c1, c2, prepared)?;
        let [inv_2x, inv_2y] =
            *coordinates
                .circle
                .get(ordinal)
                .ok_or(V5FriCheckError::MissingOpening {
                    layer: 0,
                    index: query,
                })?;
        let folded = normalized_circle_to_line_arity4_prepared_polynomial_refs(
            &combined,
            &alpha_powers[0],
            inv_2x,
            inv_2y,
        );
        let parent = query >> 2;
        let parent_leaf = opening_value_for_monotone_index(
            &openings.later[0],
            &openings.indices.later[0],
            &mut layer1_ordinal,
            parent,
            1,
        )?;
        let offset = (query & 3) as usize * 16;
        let expected = QM31::from_le_bytes(&parent_leaf[offset..offset + 16])
            .ok_or(V5FriCheckError::NonCanonicalLater { layer: 1, offset })?;
        if folded != expected {
            return Err(V5FriCheckError::FirstFoldMismatch { query });
        }
        folded_layer0_sum = folded_layer0_sum.add(folded);
    }

    for layer in 0..3 {
        let mut outgoing_ordinal = 0;
        for (ordinal, &index) in openings.indices.later[layer].iter().enumerate() {
            let incoming =
                openings.later[layer]
                    .value(ordinal)
                    .ok_or(V5FriCheckError::MissingOpening {
                        layer: layer as u8 + 1,
                        index,
                    })?;
            let inverses =
                *coordinates.later[layer]
                    .get(ordinal)
                    .ok_or(V5FriCheckError::MissingOpening {
                        layer: layer as u8 + 1,
                        index,
                    })?;
            if layer < 2 {
                let parent = index >> 2;
                let outgoing = opening_value_for_monotone_index(
                    &openings.later[layer + 1],
                    &openings.indices.later[layer + 1],
                    &mut outgoing_ordinal,
                    parent,
                    layer as u8 + 2,
                )?;
                check_fixed_line_transition_prepared_polynomial_powers(
                    incoming,
                    outgoing,
                    index as usize,
                    layer as u8 + 1,
                    inverses,
                    &alpha_powers[layer + 1],
                )?;
            } else {
                let final_x = *coordinates
                    .final_x
                    .get(ordinal)
                    .ok_or(V5FriCheckError::MissingOpening { layer: 4, index })?;
                check_fixed_terminal_transition_prepared_polynomial_refs(
                    incoming,
                    &final_polynomial,
                    index as usize,
                    inverses,
                    final_x,
                    &alpha_powers[3],
                )?;
            }
        }
    }

    Ok(V5FriCheckSink { folded_layer0_sum })
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::circle_pcs_shape::{
        gamma_combine_circle_pcs_layer0, prepare_circle_pcs_claims,
    };
    use aspis_core::field::CM31;
    use aspis_core::state_only_private_openings::{
        StateOnlyPrivateOpening, StateOnlyPrivateOpeningOffsets,
    };

    fn hashv(inputs: &[&[u8]]) -> [u8; 32] {
        solana_program::hash::hashv(inputs).to_bytes()
    }

    #[test]
    fn v5_shape_pins_every_authenticated_width_and_depth() {
        let shape = V5_FRI_PCS_SHAPE.validate().unwrap();
        assert_eq!(shape.c1_leaf_bytes_checked(), Ok(256));
        assert_eq!(shape.c2_leaf_bytes_checked(), Ok(192));
        assert_eq!(shape.opening_points, 4);
        assert_eq!(shape.total_columns(), 19);
        assert_eq!(shape.opening_geometry().unwrap().layer0_binary_depth, 17);
        assert_eq!(
            shape.opening_geometry().unwrap().later_binary_depths,
            [15, 13, 11]
        );
    }

    #[test]
    fn monotone_opening_lookup_preserves_hits_and_fails_closed() {
        let mut records = [0u8; 3 * 33];
        records[0] = 11;
        records[33] = 22;
        records[66] = 33;
        let opening = StateOnlyPrivateOpening {
            count: 3,
            value_width: 1,
            records: &records,
            frontier: &[],
            offsets: StateOnlyPrivateOpeningOffsets {
                count: 0,
                records: 0,
                frontier_count: 0,
                frontier: 0,
                end: 0,
            },
        };
        let indices = [1, 3, 7];
        let mut ordinal = 0;
        assert_eq!(
            opening_value_for_monotone_index(&opening, &indices, &mut ordinal, 1, 2),
            Ok(&records[0..1])
        );
        assert_eq!(
            opening_value_for_monotone_index(&opening, &indices, &mut ordinal, 1, 2),
            Ok(&records[0..1])
        );
        assert_eq!(
            opening_value_for_monotone_index(&opening, &indices, &mut ordinal, 7, 2),
            Ok(&records[66..67])
        );
        assert_eq!(
            opening_value_for_monotone_index(&opening, &indices, &mut ordinal, 3, 2),
            Err(V5FriCheckError::MissingOpening { layer: 2, index: 3 })
        );

        let mut gap_ordinal = 0;
        assert_eq!(
            opening_value_for_monotone_index(&opening, &indices, &mut gap_ordinal, 2, 2),
            Err(V5FriCheckError::MissingOpening { layer: 2, index: 2 })
        );
    }

    fn q(a: u32, b: u32, c: u32, d: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(a), M31(b)),
            c1: CM31::new(M31(c), M31(d)),
        }
    }

    fn prepared_for_combiner_test() -> V5PreparedPcsClaims {
        prepare_v5_pcs_claims(
            q(3, 5, 7, 11),
            &vec![0u8; V5_FRI_PCS_SHAPE.evaluation_bytes()],
        )
        .unwrap()
    }

    fn reference_combine(
        c1: &[u8],
        c2: &[u8],
        prepared: &V5PreparedPcsClaims,
    ) -> Result<[QM31; 4], CirclePcsDecodeError> {
        gamma_combine_circle_pcs_layer0(V5_FRI_PCS_SHAPE, c1, c2, &prepared.inner.powers)
    }

    fn canonical_value(case: u32, index: usize) -> u32 {
        match case {
            0 => 0,
            1 => P - 1,
            _ => {
                ((u64::from(case) * 1_103_515_245 + index as u64 * 2_654_435_761 + 12_345)
                    % u64::from(P)) as u32
            }
        }
    }

    fn claim_table(case: u32) -> Vec<u8> {
        let mut bytes = vec![0u8; V5_FRI_PCS_SHAPE.evaluation_bytes()];
        for (index, encoded) in bytes.chunks_exact_mut(4).enumerate() {
            encoded.copy_from_slice(&canonical_value(case, index).to_le_bytes());
        }
        bytes
    }

    fn reference_prepare(
        gamma: QM31,
        bytes: &[u8],
    ) -> Result<CirclePcsPreparedClaims, V5FriCheckError> {
        prepare_circle_pcs_claims(V5_FRI_PCS_SHAPE, gamma, bytes).map_err(Into::into)
    }

    #[test]
    fn fixed_v5_claim_preparation_matches_literal_nineteen_product_dots() {
        let gammas = [
            QM31::ZERO,
            QM31::ONE,
            q(P - 1, P - 2, P - 3, P - 4),
            q(3, 5, 7, 11),
            q(1_234_567, 765_432_100, 1_987_654_321, 42),
        ];
        for (gamma_index, gamma) in gammas.into_iter().enumerate() {
            for case in 0..34 {
                let bytes = claim_table(case);
                let optimized = prepare_v5_pcs_claims(gamma, &bytes).map(|value| value.inner);
                assert_eq!(
                    optimized,
                    reference_prepare(gamma, &bytes),
                    "gamma {gamma_index}, case {case}"
                );
            }
        }
    }

    #[test]
    fn fixed_v5_claim_preparation_pins_all_seventy_six_slots_and_errors() {
        let gamma = q(3, 5, 7, 11);
        let zero = vec![0u8; V5_FRI_PCS_SHAPE.evaluation_bytes()];
        let baseline = prepare_v5_pcs_claims(gamma, &zero).unwrap();
        for index in 0..V5_FRI_OPENING_POINTS * V5_FRI_TOTAL_COLUMNS {
            let point = index / V5_FRI_TOTAL_COLUMNS;
            let column = index % V5_FRI_TOTAL_COLUMNS;

            let mut singleton = zero.clone();
            singleton[index * 16..index * 16 + 4].copy_from_slice(&1u32.to_le_bytes());
            let prepared = prepare_v5_pcs_claims(gamma, &singleton).unwrap();
            for actual_point in 0..V5_FRI_OPENING_POINTS {
                assert_eq!(
                    prepared.inner.claims[actual_point],
                    if actual_point == point {
                        baseline.inner.powers[column]
                    } else {
                        QM31::ZERO
                    },
                    "canonical slot {index}"
                );
            }

            let mut malformed = zero.clone();
            let limb = index % 4;
            let offset = index * 16 + limb * 4;
            malformed[offset..offset + 4].copy_from_slice(&P.to_le_bytes());
            let expected =
                V5FriCheckError::Decode(CirclePcsDecodeError::NonCanonicalEvaluation { index });
            assert_eq!(
                prepare_v5_pcs_claims(gamma, &malformed).unwrap_err(),
                expected
            );
            assert_eq!(reference_prepare(gamma, &malformed).unwrap_err(), expected);
        }

        // Preserve the generic decoder's first-error order when more than one
        // point-major slot is malformed. The later mutation is written first
        // deliberately; decoding must still report the lower canonical slot.
        let mut multiple_malformed = zero;
        multiple_malformed[57 * 16..57 * 16 + 4].copy_from_slice(&P.to_le_bytes());
        multiple_malformed[3 * 16..3 * 16 + 4].copy_from_slice(&P.to_le_bytes());
        let expected =
            V5FriCheckError::Decode(CirclePcsDecodeError::NonCanonicalEvaluation { index: 3 });
        assert_eq!(
            prepare_v5_pcs_claims(gamma, &multiple_malformed).unwrap_err(),
            expected
        );
        assert_eq!(
            reference_prepare(gamma, &multiple_malformed).unwrap_err(),
            expected
        );
    }

    #[test]
    fn fixed_v5_claim_preparation_preserves_every_length_error() {
        let gamma = q(3, 5, 7, 11);
        let expected = V5_FRI_PCS_SHAPE.evaluation_bytes();
        for actual in [0, 1, 15, 16, expected - 1, expected + 1, expected + 16] {
            let bytes = vec![0u8; actual];
            assert_eq!(
                prepare_v5_pcs_claims(gamma, &bytes).map(|value| value.inner),
                reference_prepare(gamma, &bytes),
                "length {actual}"
            );
        }
    }

    fn combiner_leaves(case: u32) -> (Vec<u8>, Vec<u8>) {
        let mut c1 = vec![0u8; V5_PRIVATE_VALUE_WIDTHS[0]];
        for (index, encoded) in c1.chunks_exact_mut(4).enumerate() {
            encoded.copy_from_slice(&canonical_value(case, index).to_le_bytes());
        }
        let mut c2 = vec![0u8; V5_PRIVATE_VALUE_WIDTHS[1]];
        let c2_case = if case < 2 { case } else { case + 37 };
        for (index, encoded) in c2.chunks_exact_mut(4).enumerate() {
            encoded.copy_from_slice(&canonical_value(c2_case, index).to_le_bytes());
        }
        (c1, c2)
    }

    #[test]
    fn fused_v5_layer0_is_exactly_the_literal_16_plus_3_combiner() {
        let prepared = prepared_for_combiner_test();
        // Cases 0 and 1 exercise the additive identities and the maximum
        // canonical limbs; the remaining cases exercise every slot and lane
        // with unrelated deterministic extension-field values.
        for case in 0..66 {
            let (c1, c2) = combiner_leaves(case);
            assert_eq!(
                gamma_combine_v5_layer0_exact(&c1, &c2, &prepared),
                reference_combine(&c1, &c2, &prepared),
                "case {case}"
            );
        }
    }

    #[test]
    fn fused_v5_layer0_preserves_length_and_canonical_errors_exactly() {
        let prepared = prepared_for_combiner_test();
        let (c1, c2) = combiner_leaves(9);

        for (shorter, longer) in [(&c1[..c1.len() - 1], {
            let mut value = c1.clone();
            value.push(0);
            value
        })] {
            assert_eq!(
                gamma_combine_v5_layer0_exact(shorter, &c2, &prepared),
                reference_combine(shorter, &c2, &prepared)
            );
            assert_eq!(
                gamma_combine_v5_layer0_exact(&longer, &c2, &prepared),
                reference_combine(&longer, &c2, &prepared)
            );
        }
        let mut c2_longer = c2.clone();
        c2_longer.push(0);
        assert_eq!(
            gamma_combine_v5_layer0_exact(&c1, &c2[..c2.len() - 1], &prepared),
            reference_combine(&c1, &c2[..c2.len() - 1], &prepared)
        );
        assert_eq!(
            gamma_combine_v5_layer0_exact(&c1, &c2_longer, &prepared),
            reference_combine(&c1, &c2_longer, &prepared)
        );

        for offset in [
            0,
            V5_PRIVATE_VALUE_WIDTHS[0] / 2,
            V5_PRIVATE_VALUE_WIDTHS[0] - 4,
        ] {
            let mut malformed = c1.clone();
            malformed[offset..offset + 4].copy_from_slice(&P.to_le_bytes());
            assert_eq!(
                gamma_combine_v5_layer0_exact(&malformed, &c2, &prepared),
                reference_combine(&malformed, &c2, &prepared)
            );
        }
        for offset in [
            0,
            V5_PRIVATE_VALUE_WIDTHS[1] / 2,
            V5_PRIVATE_VALUE_WIDTHS[1] - 16,
        ] {
            let mut malformed = c2.clone();
            malformed[offset..offset + 4].copy_from_slice(&P.to_le_bytes());
            assert_eq!(
                gamma_combine_v5_layer0_exact(&c1, &malformed, &prepared),
                reference_combine(&c1, &malformed, &prepared)
            );
        }
    }

    #[test]
    fn query_tail_is_without_replacement_and_binds_final_bytes() {
        let mut transcript = Transcript::new(hashv);
        transcript.absorb(label::PROFILE, b"aspis-v5-fri-check-test");
        let final_bytes = [0u8; V5_FRI_FINAL_BYTES];
        let (_, first) =
            bind_final_and_derive_v5_queries(&mut transcript, &final_bytes, 7, 0, false).unwrap();
        let mut sorted = first;
        sorted.sort_unstable();
        assert!(sorted.windows(2).all(|pair| pair[0] < pair[1]));
        assert!(sorted
            .iter()
            .all(|query| *query < V5_PRIVATE_LAYER0_LEAVES as u32));

        let mut changed = Transcript::new(hashv);
        changed.absorb(label::PROFILE, b"aspis-v5-fri-check-test");
        let mut changed_final = final_bytes;
        changed_final[0] = 1;
        let (_, second) =
            bind_final_and_derive_v5_queries(&mut changed, &changed_final, 7, 0, false).unwrap();
        assert_ne!(first, second);
    }
}
