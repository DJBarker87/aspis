//! Rejected host-reference candidate for the compact V7 successor.
//!
//! This module preserves the measured 216-bit/omitted-`D` research branch. It
//! is **not** the selected production V7 wire. Production V7 lives in
//! `v7_onefold`: 208-bit digests and every complete C2 fibre disclosed. The
//! rejected candidate remains archived here so its reconstruction experiment
//! and negative design evidence are reproducible.
//!
//! Omitting that value does not omit a check.  Once `gamma`, the fold
//! challenge, the final codeword value and the other eleven C2 values are
//! known, the fold equation has one unique solution for a deterministically
//! selected `D` slot.  The verifier reconstructs that value before hashing the
//! complete logical C2 leaf, so the Merkle commitment still binds all twelve
//! C2 values.

use alloc::vec::Vec;

use crate::circle_fri::{
    normalized_circle_to_line_arity4_prepared,
    normalized_circle_to_line_arity4_prepared_polynomial_refs,
};
use crate::field::{qm31_power_table, PreparedQm31Multiplier, M31, P, QM31};
use crate::state_only_spend_query::{
    StateOnlySpendQueryPowers, SPEND_D_GENERATOR_INDEX, SPEND_TOTAL_COLUMNS,
};
use crate::transcript::{label, Transcript};
use crate::v6_onefold::{
    gamma_combine_v6_packed_layer0, packed_qm31_at, validate_packed_m31, V6OneFoldCoordinates,
    V6WireError, V6_C1_LIMBS_PER_QUERY, V6_C1_PACKED_BYTES_PER_QUERY, V6_C2_PACKED_BYTES_PER_QUERY,
    V6_FIXED_M31_LIMBS, V6_FIXED_PACKED_FIELD_BYTES, V6_QUERY_COUNT, V6_WORK_NONCE_BYTES,
};
use crate::v7_merkle::{
    private_leaf_hash216, verify_two_minimal_subtrees216_bytes, V7Digest, V7_C1_TREE_TAG,
    V7_C2_TREE_TAG,
};
use crate::HashFn;

pub const V7_COMPACT_DIGEST_BYTES: usize = 27;
pub const V7_COMPACT_DIGEST_BITS: usize = 8 * V7_COMPACT_DIGEST_BYTES;
pub const V7_COMPACT_CLASSICAL_COLLISION_BITS: usize = V7_COMPACT_DIGEST_BITS / 2;
pub const V7_COMPACT_FRONTIER_CAP_PER_TREE: usize = 203;
pub const V7_COMPACT_QUERY_CANDIDATES: usize = 64;
pub const V7_COMPACT_SELECTOR_STREAMS: usize = 1;
pub const V7_COMPACT_BATCH_WORK_BITS: u8 = 35;
pub const V7_COMPACT_FOLD_WORK_BITS: u8 = 31;
pub const V7_COMPACT_FINAL_WORK_BITS: u8 = 34;

/// Byte-level V7 profile record absorbed before deployment, statement, roots,
/// or challenges.  It commits the unchanged 26+3 arithmetic together with
/// the compact wire's digest width, frontier cap, first-success schedule,
/// work allocation, tree tags, and revision.
pub const V7_COMPACT_PROFILE_BINDING: [u8; 32] = [
    b'A', b'V', b'7', b'C', b'F', b'0', b'0', b'1', // magic/version
    26, 3, 10, 16, 0xcb, 0x00, 27, 32, // widths, q, cap203, digest/salt bytes
    27, 4, 6, 35, 31, 34, 0x71, 0xf1, // transcript widths, work, tree tags
    0x81, 0x02, 8, 20, 18, 1, 64, 0, // 641 fields, final log, logs, stream/cap/rev
];

pub const V7_COMPACT_C2_QM31_PER_QUERY: usize = 11;
pub const V7_COMPACT_C2_LIMBS_PER_QUERY: usize = 4 * V7_COMPACT_C2_QM31_PER_QUERY;
pub const V7_COMPACT_PRIVATE_SALT_BYTES: usize = 32;
pub const V7_COMPACT_PRODUCTION_LIMIT_BYTES: usize = 30 * 1024;

pub const fn packed_m31_bytes(limbs: usize) -> usize {
    (31 * limbs + 7) / 8
}

pub const V7_COMPACT_C1_BYTES_PER_QUERY: usize = packed_m31_bytes(V6_C1_LIMBS_PER_QUERY);
pub const V7_COMPACT_C2_BYTES_PER_QUERY: usize = packed_m31_bytes(V7_COMPACT_C2_LIMBS_PER_QUERY);
pub const V7_COMPACT_QUERY_BYTES: usize =
    V7_COMPACT_C1_BYTES_PER_QUERY + V7_COMPACT_C2_BYTES_PER_QUERY + V7_COMPACT_PRIVATE_SALT_BYTES;
pub const V7_COMPACT_QUERY_SECTION_BYTES: usize = V6_QUERY_COUNT * V7_COMPACT_QUERY_BYTES;
pub const V7_COMPACT_ROOT_BYTES: usize = 2 * V7_COMPACT_DIGEST_BYTES;
pub const V7_COMPACT_BODY_WITHOUT_FRONTIERS: usize = V6_FIXED_PACKED_FIELD_BYTES
    + V7_COMPACT_ROOT_BYTES
    + V6_WORK_NONCE_BYTES
    + V7_COMPACT_QUERY_SECTION_BYTES;
pub const V7_COMPACT_MAX_BODY_BYTES: usize = V7_COMPACT_BODY_WITHOUT_FRONTIERS
    + 2 * V7_COMPACT_FRONTIER_CAP_PER_TREE * V7_COMPACT_DIGEST_BYTES;
pub const V7_COMPACT_BODY_HEADROOM_BYTES: usize =
    V7_COMPACT_PRODUCTION_LIMIT_BYTES - V7_COMPACT_MAX_BODY_BYTES;

#[derive(Clone)]
pub struct V7CompactQuerySchedule {
    pub queries: [u32; V6_QUERY_COUNT],
    pub counter: u8,
    pub frontier_nodes: usize,
    pub transcript_state: [u8; 32],
    pub accepted_transcript: Transcript,
}

/// Derive the first cap-203 query schedule in the sole V7 counter stream.
/// The counter is not proof-carried and no later acceptable schedule may be
/// selected by the prover.
pub fn derive_first_v7_compact_queries(
    transcript: &Transcript,
) -> Result<V7CompactQuerySchedule, V6WireError> {
    for counter in 0..V7_COMPACT_QUERY_CANDIDATES as u8 {
        let mut candidate_transcript = transcript.clone();
        candidate_transcript.absorb(label::V7_QUERY_CANDIDATE, &[counter]);
        let candidate = candidate_transcript
            .challenge_queries_without_replacement(V6_QUERY_COUNT, 1 << 18, 64)
            .map_err(|_| V6WireError::InvalidQuerySchedule)?;
        let queries: [u32; V6_QUERY_COUNT] = candidate
            .try_into()
            .map_err(|_| V6WireError::InvalidQuerySchedule)?;
        let frontier_nodes = crate::v6_onefold::binary_frontier_nodes(queries, 18)?;
        if frontier_nodes <= V7_COMPACT_FRONTIER_CAP_PER_TREE {
            return Ok(V7CompactQuerySchedule {
                queries,
                counter,
                frontier_nodes,
                transcript_state: candidate_transcript.diagnostic_state(),
                accepted_transcript: candidate_transcript,
            });
        }
    }
    Err(V6WireError::InvalidQuerySchedule)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V7CompactQueryRecord<'a> {
    pub c1_packed: &'a [u8],
    pub c2_compact_packed: &'a [u8],
    pub salt: &'a [u8; V7_COMPACT_PRIVATE_SALT_BYTES],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V7CompactOneFoldWire<'a> {
    pub fixed_fields_packed: &'a [u8],
    pub c1_root: &'a V7Digest,
    pub c2_root: &'a V7Digest,
    pub work_nonces: &'a [u8; V6_WORK_NONCE_BYTES],
    query_section: &'a [u8],
    pub c1_frontier: &'a [u8],
    pub c2_frontier: &'a [u8],
}

impl<'a> V7CompactOneFoldWire<'a> {
    pub fn parse(bytes: &'a [u8], frontier_nodes: usize) -> Result<Self, V6WireError> {
        let wire = Self::parse_deferred_canonicality(bytes, frontier_nodes)?;
        validate_packed_m31(wire.fixed_fields_packed, V6_FIXED_M31_LIMBS)?;
        for ordinal in 0..V6_QUERY_COUNT {
            let query = wire
                .query(ordinal)
                .ok_or(V6WireError::InvalidQuerySchedule)?;
            validate_packed_m31(query.c1_packed, V6_C1_LIMBS_PER_QUERY)?;
            validate_packed_m31(query.c2_compact_packed, V7_COMPACT_C2_LIMBS_PER_QUERY)?;
        }
        Ok(wire)
    }

    /// Parse section boundaries while leaving canonical field checks to the
    /// exact consumers. Fixed-section padding is still rejected here so no
    /// proof byte can remain semantically ignored.
    pub fn parse_deferred_canonicality(
        bytes: &'a [u8],
        frontier_nodes: usize,
    ) -> Result<Self, V6WireError> {
        if frontier_nodes > V7_COMPACT_FRONTIER_CAP_PER_TREE {
            return Err(V6WireError::FrontierTooLarge);
        }
        let frontier_bytes = frontier_nodes
            .checked_mul(V7_COMPACT_DIGEST_BYTES)
            .ok_or(V6WireError::WrongLength)?;
        let expected = V7_COMPACT_BODY_WITHOUT_FRONTIERS
            .checked_add(2 * frontier_bytes)
            .ok_or(V6WireError::WrongLength)?;
        if bytes.len() != expected || bytes.len() > V7_COMPACT_PRODUCTION_LIMIT_BYTES {
            return Err(V6WireError::WrongLength);
        }
        let (fixed_fields_packed, rest) = bytes.split_at(V6_FIXED_PACKED_FIELD_BYTES);
        if fixed_fields_packed.last().copied().unwrap_or_default() & 0xf0 != 0 {
            return Err(V6WireError::NonCanonicalM31);
        }
        let (c1_root, rest) = rest.split_at(V7_COMPACT_DIGEST_BYTES);
        let (c2_root, rest) = rest.split_at(V7_COMPACT_DIGEST_BYTES);
        let (work_nonces, rest) = rest.split_at(V6_WORK_NONCE_BYTES);
        let (query_section, rest) = rest.split_at(V7_COMPACT_QUERY_SECTION_BYTES);
        let (c1_frontier, c2_frontier) = rest.split_at(frontier_bytes);
        debug_assert_eq!(c2_frontier.len(), frontier_bytes);
        Ok(Self {
            fixed_fields_packed,
            c1_root: c1_root.try_into().map_err(|_| V6WireError::WrongLength)?,
            c2_root: c2_root.try_into().map_err(|_| V6WireError::WrongLength)?,
            work_nonces: work_nonces
                .try_into()
                .map_err(|_| V6WireError::WrongLength)?,
            query_section,
            c1_frontier,
            c2_frontier,
        })
    }

    pub fn query(&self, ordinal: usize) -> Option<V7CompactQueryRecord<'a>> {
        if ordinal >= V6_QUERY_COUNT {
            return None;
        }
        let start = ordinal * V7_COMPACT_QUERY_BYTES;
        let c1_end = start + V7_COMPACT_C1_BYTES_PER_QUERY;
        let c2_end = c1_end + V7_COMPACT_C2_BYTES_PER_QUERY;
        let end = c2_end + V7_COMPACT_PRIVATE_SALT_BYTES;
        Some(V7CompactQueryRecord {
            c1_packed: &self.query_section[start..c1_end],
            c2_compact_packed: &self.query_section[c1_end..c2_end],
            salt: self.query_section[c2_end..end].try_into().ok()?,
        })
    }
}

/// Return the four coefficients of the exact V6 circle-to-line fold.
///
/// This is the direct expansion of the maintained two-butterfly evaluator.
/// Computing it once per query replaces four full basis-vector folds while
/// preserving the identical cubic in `alpha`.
pub fn fold_coefficients(alpha: QM31, inv_2x: M31, inv_2y: M31) -> [QM31; 4] {
    let alpha_squared = alpha.square();
    fold_coefficients_from_powers(
        alpha,
        alpha_squared,
        alpha_squared.mul(alpha),
        inv_2x,
        inv_2y,
    )
}

#[inline(always)]
fn fold_coefficients_from_powers(
    alpha: QM31,
    alpha_squared: QM31,
    alpha_cubed: QM31,
    inv_2x: M31,
    inv_2y: M31,
) -> [QM31; 4] {
    let quarter = QM31::ONE.half().half();
    let linear = alpha.mul_m31(inv_2y).half();
    let quadratic = alpha_squared.mul_m31(inv_2x).half();
    let cubic = alpha_cubed.mul_m31(inv_2x.mul(inv_2y));
    [
        quarter.add(linear).add(quadratic).add(cubic),
        quarter.sub(linear).add(quadratic).sub(cubic),
        quarter.sub(linear).sub(quadratic).add(cubic),
        quarter.add(linear).sub(quadratic).sub(cubic),
    ]
}

#[cfg(test)]
fn fold_coefficients_basis_reference(alpha: QM31, inv_2x: M31, inv_2y: M31) -> [QM31; 4] {
    core::array::from_fn(|slot| {
        let mut basis = [QM31::ZERO; 4];
        basis[slot] = QM31::ONE;
        normalized_circle_to_line_arity4_prepared(basis, alpha, inv_2x, inv_2y)
    })
}

/// The fold is an affine interpolation, so its four coefficients sum to one
/// and at least one is nonzero.  Selecting the first nonzero coefficient is
/// deterministic and needs no proof-carried selector bits.
pub fn first_reconstructible_slot(coefficients: &[QM31; 4]) -> Option<usize> {
    coefficients
        .iter()
        .position(|coefficient| !coefficient.is_zero())
}

/// Reconstruct the one omitted `D` value from the authenticated fold equation.
///
/// `partial_combined` contains the gamma-combination of all disclosed values,
/// with the missing D contribution left out at `omitted_slot`.  The returned
/// value is inserted into the complete logical C2 leaf before its 216-bit leaf
/// digest is computed.
pub fn reconstruct_omitted_d(
    partial_combined: [QM31; 4],
    expected_fold: QM31,
    gamma: QM31,
    alpha: QM31,
    inv_2x: M31,
    inv_2y: M31,
) -> Option<(usize, QM31)> {
    if gamma.is_zero() {
        return None;
    }
    let coefficients = fold_coefficients(alpha, inv_2x, inv_2y);
    let omitted_slot = first_reconstructible_slot(&coefficients)?;
    let current =
        normalized_circle_to_line_arity4_prepared(partial_combined, alpha, inv_2x, inv_2y);
    let powers = qm31_power_table::<SPEND_TOTAL_COLUMNS>(gamma);
    let denominator = coefficients[omitted_slot].mul(powers[SPEND_D_GENERATOR_INDEX]);
    let omitted_d = expected_fold.sub(current).mul(denominator.try_inv()?);
    Some((omitted_slot, omitted_d))
}

fn write_packed_m31(output: &mut [u8], limb: usize, value: M31) -> Result<(), V6WireError> {
    if value.0 >= P {
        return Err(V6WireError::NonCanonicalM31);
    }
    let bit_start = limb.checked_mul(31).ok_or(V6WireError::WrongLength)?;
    if bit_start + 31 > output.len() * 8 {
        return Err(V6WireError::WrongLength);
    }
    for bit in 0..31 {
        if (value.0 >> bit) & 1 != 0 {
            let output_bit = bit_start + bit;
            output[output_bit / 8] |= 1 << (output_bit % 8);
        }
    }
    Ok(())
}

fn write_packed_qm31(
    output: &mut [u8],
    value_index: usize,
    value: QM31,
) -> Result<(), V6WireError> {
    let first_limb = value_index.checked_mul(4).ok_or(V6WireError::WrongLength)?;
    for (offset, limb) in [value.c0.a, value.c0.b, value.c1.a, value.c1.b]
        .into_iter()
        .enumerate()
    {
        write_packed_m31(output, first_limb + offset, limb)?;
    }
    Ok(())
}

/// Encode the compact C2 query record in logical `H[4] || G[4] || D[3]`
/// order, skipping the verifier-determined D slot.
pub fn encode_compact_c2_query(
    helpers: &[[QM31; 4]; 3],
    omitted_d_slot: usize,
) -> Result<[u8; V7_COMPACT_C2_BYTES_PER_QUERY], V6WireError> {
    if omitted_d_slot >= 4 {
        return Err(V6WireError::InvalidQuerySchedule);
    }
    let mut output = [0u8; V7_COMPACT_C2_BYTES_PER_QUERY];
    let mut next = 0usize;
    for helper in helpers.iter().take(2) {
        for value in helper {
            write_packed_qm31(&mut output, next, *value)?;
            next += 1;
        }
    }
    for (slot, value) in helpers[2].iter().copied().enumerate() {
        if slot != omitted_d_slot {
            write_packed_qm31(&mut output, next, value)?;
            next += 1;
        }
    }
    debug_assert_eq!(next, V7_COMPACT_C2_QM31_PER_QUERY);
    Ok(output)
}

/// Decode the compact record and insert zero at the one omitted D slot.  The
/// caller reconstructs that slot before hashing the complete logical leaf.
pub fn decode_compact_c2_query(
    packed: &[u8],
    omitted_d_slot: usize,
) -> Result<[[QM31; 4]; 3], V6WireError> {
    if omitted_d_slot >= 4 || packed.len() != V7_COMPACT_C2_BYTES_PER_QUERY {
        return Err(V6WireError::WrongLength);
    }
    validate_packed_m31(packed, V7_COMPACT_C2_LIMBS_PER_QUERY)?;
    let mut helpers = [[QM31::ZERO; 4]; 3];
    let mut next = 0usize;
    for helper in helpers.iter_mut().take(2) {
        for value in helper {
            *value = packed_qm31_at(packed, next).ok_or(V6WireError::WrongLength)?;
            next += 1;
        }
    }
    for slot in 0..4 {
        if slot != omitted_d_slot {
            helpers[2][slot] = packed_qm31_at(packed, next).ok_or(V6WireError::WrongLength)?;
            next += 1;
        }
    }
    debug_assert_eq!(next, V7_COMPACT_C2_QM31_PER_QUERY);
    Ok(helpers)
}

/// Serialize the complete logical C2 leaf in the exact V6 packed order used
/// by the commitment.  This output, not the 171-byte transport record, is the
/// typed leaf-hash preimage.
pub fn encode_full_c2_leaf(
    helpers: &[[QM31; 4]; 3],
) -> Result<[u8; V6_C2_PACKED_BYTES_PER_QUERY], V6WireError> {
    let mut output = [0u8; V6_C2_PACKED_BYTES_PER_QUERY];
    for (helper, values) in helpers.iter().enumerate() {
        for (slot, value) in values.iter().copied().enumerate() {
            write_packed_qm31(&mut output, helper * 4 + slot, value)?;
        }
    }
    Ok(output)
}

/// Reconstruct one compact C2 record, restore the complete committed leaf,
/// and return its exact gamma-combined fibre.  Authentication hashes
/// `full_c2_leaf`; the caller must never hash `compact_c2_packed` directly.
#[allow(clippy::too_many_arguments)]
pub fn reconstruct_compact_c2_query(
    c1_packed: &[u8],
    compact_c2_packed: &[u8],
    expected_fold: QM31,
    gamma: QM31,
    alpha: QM31,
    inv_2x: M31,
    inv_2y: M31,
) -> Result<([u8; V6_C2_PACKED_BYTES_PER_QUERY], [QM31; 4], usize), V6WireError> {
    if c1_packed.len() != V6_C1_PACKED_BYTES_PER_QUERY || gamma.is_zero() {
        return Err(V6WireError::WrongLength);
    }
    let coefficients = fold_coefficients(alpha, inv_2x, inv_2y);
    let omitted_slot = first_reconstructible_slot(&coefficients).ok_or(V6WireError::FriMismatch)?;
    let mut helpers = decode_compact_c2_query(compact_c2_packed, omitted_slot)?;
    let partial_leaf = encode_full_c2_leaf(&helpers)?;
    let powers = StateOnlySpendQueryPowers::new(gamma);
    let mut combined = gamma_combine_v6_packed_layer0(c1_packed, &partial_leaf, &powers)?;
    let current = normalized_circle_to_line_arity4_prepared(combined, alpha, inv_2x, inv_2y);
    let d_power = qm31_power_table::<SPEND_TOTAL_COLUMNS>(gamma)[SPEND_D_GENERATOR_INDEX];
    let denominator = coefficients[omitted_slot].mul(d_power);
    let omitted_d = expected_fold
        .sub(current)
        .mul(denominator.try_inv().ok_or(V6WireError::FriMismatch)?);
    helpers[2][omitted_slot] = omitted_d;
    combined[omitted_slot] = combined[omitted_slot].add(d_power.mul(omitted_d));
    if normalized_circle_to_line_arity4_prepared(combined, alpha, inv_2x, inv_2y) != expected_fold {
        return Err(V6WireError::FriMismatch);
    }
    Ok((encode_full_c2_leaf(&helpers)?, combined, omitted_slot))
}

/// Montgomery batch inversion for the sixteen nonzero QM31 reconstruction
/// denominators.  It performs one extension-field inversion and the usual
/// prefix/suffix multiplications, replacing sixteen independent inversions in
/// the verifier hot path.
fn qm31_batch_inverse_16(values: &[QM31; V6_QUERY_COUNT]) -> Option<[QM31; V6_QUERY_COUNT]> {
    let mut prefixes = [QM31::ONE; V6_QUERY_COUNT];
    let mut accumulator = QM31::ONE;
    for (index, value) in values.iter().copied().enumerate() {
        if value.is_zero() {
            return None;
        }
        prefixes[index] = accumulator;
        accumulator = accumulator.mul(value);
    }
    let mut suffix_inverse = accumulator.try_inv()?;
    let mut inverses = [QM31::ZERO; V6_QUERY_COUNT];
    for index in (0..V6_QUERY_COUNT).rev() {
        inverses[index] = prefixes[index].mul(suffix_inverse);
        suffix_inverse = suffix_inverse.mul(values[index]);
    }
    Some(inverses)
}

#[derive(Clone, Copy)]
struct V7CompactReconstructionPlan {
    omitted_slots: [u8; V6_QUERY_COUNT],
    denominator_inverses: [QM31; V6_QUERY_COUNT],
}

fn prepare_v7_compact_reconstruction(
    d_power: QM31,
    alpha: QM31,
    coordinates: &V6OneFoldCoordinates,
) -> Result<([PreparedQm31Multiplier; 3], V7CompactReconstructionPlan), V6WireError> {
    if d_power.is_zero() {
        return Err(V6WireError::FriMismatch);
    }

    let alpha_squared = alpha.square();
    let alpha_cubed = alpha_squared.mul(alpha);
    let alpha_multipliers = [
        PreparedQm31Multiplier::new(alpha),
        PreparedQm31Multiplier::new(alpha_squared),
        PreparedQm31Multiplier::new(alpha_cubed),
    ];
    let mut omitted_slots = [0u8; V6_QUERY_COUNT];
    let mut denominators = [QM31::ZERO; V6_QUERY_COUNT];
    for ordinal in 0..V6_QUERY_COUNT {
        let coefficients = fold_coefficients_from_powers(
            alpha,
            alpha_squared,
            alpha_cubed,
            coordinates.inv_2x[ordinal],
            coordinates.inv_2y[ordinal],
        );
        let omitted_slot =
            first_reconstructible_slot(&coefficients).ok_or(V6WireError::FriMismatch)?;
        omitted_slots[ordinal] = omitted_slot as u8;
        denominators[ordinal] = coefficients[omitted_slot].mul(d_power);
    }
    let denominator_inverses =
        qm31_batch_inverse_16(&denominators).ok_or(V6WireError::FriMismatch)?;
    Ok((
        alpha_multipliers,
        V7CompactReconstructionPlan {
            omitted_slots,
            denominator_inverses,
        },
    ))
}

#[allow(clippy::too_many_arguments)]
fn reconstruct_compact_c2_query_prepared(
    c1_packed: &[u8],
    compact_c2_packed: &[u8],
    expected_fold: QM31,
    inv_2x: M31,
    inv_2y: M31,
    powers: &StateOnlySpendQueryPowers,
    d_power: QM31,
    alpha_multipliers: &[PreparedQm31Multiplier; 3],
    omitted_slot: usize,
    denominator_inverse: QM31,
) -> Result<([u8; V6_C2_PACKED_BYTES_PER_QUERY], [QM31; 4]), V6WireError> {
    if c1_packed.len() != V6_C1_PACKED_BYTES_PER_QUERY || omitted_slot >= 4 {
        return Err(V6WireError::WrongLength);
    }
    let mut helpers = decode_compact_c2_query(compact_c2_packed, omitted_slot)?;
    let partial_leaf = encode_full_c2_leaf(&helpers)?;
    let mut combined = gamma_combine_v6_packed_layer0(c1_packed, &partial_leaf, powers)?;
    let current = normalized_circle_to_line_arity4_prepared_polynomial_refs(
        &combined,
        alpha_multipliers,
        inv_2x,
        inv_2y,
    );
    let omitted_d = expected_fold.sub(current).mul(denominator_inverse);
    helpers[2][omitted_slot] = omitted_d;
    combined[omitted_slot] = combined[omitted_slot].add(d_power.mul(omitted_d));
    Ok((encode_full_c2_leaf(&helpers)?, combined))
}

/// Reconstruct, authenticate and gamma-combine every compact V7 query. The
/// complete C2 leaf is restored before its typed leaf hash is computed.
#[allow(clippy::too_many_arguments)]
pub fn verify_reconstruct_and_gamma_combine_v7_openings(
    hash: HashFn,
    wire: &V7CompactOneFoldWire<'_>,
    queries: [u32; V6_QUERY_COUNT],
    expected_folds: [QM31; V6_QUERY_COUNT],
    powers: &StateOnlySpendQueryPowers,
    d_power: QM31,
    alpha: QM31,
    coordinates: &V6OneFoldCoordinates,
) -> Result<[[QM31; 4]; V6_QUERY_COUNT], V6WireError> {
    let mut order: [(u32, usize); V6_QUERY_COUNT] =
        core::array::from_fn(|ordinal| (queries[ordinal], ordinal));
    order.sort_unstable_by_key(|entry| entry.0);
    if order[V6_QUERY_COUNT - 1].0 >= 1 << 18 || order.windows(2).any(|pair| pair[0].0 == pair[1].0)
    {
        return Err(V6WireError::InvalidQuerySchedule);
    }

    let (alpha_multipliers, reconstruction) =
        prepare_v7_compact_reconstruction(d_power, alpha, coordinates)?;

    let mut combined = [[QM31::ZERO; 4]; V6_QUERY_COUNT];
    let mut entries = Vec::with_capacity(V6_QUERY_COUNT);
    for (query, ordinal) in order {
        let record = wire
            .query(ordinal)
            .ok_or(V6WireError::InvalidQuerySchedule)?;
        let omitted_slot = usize::from(reconstruction.omitted_slots[ordinal]);
        let (full_c2_leaf, query_combined) = reconstruct_compact_c2_query_prepared(
            record.c1_packed,
            record.c2_compact_packed,
            expected_folds[ordinal],
            coordinates.inv_2x[ordinal],
            coordinates.inv_2y[ordinal],
            powers,
            d_power,
            &alpha_multipliers,
            omitted_slot,
            reconstruction.denominator_inverses[ordinal],
        )?;
        combined[ordinal] = query_combined;
        entries.push((
            query,
            private_leaf_hash216(hash, V7_C1_TREE_TAG, record.c1_packed, record.salt),
            private_leaf_hash216(hash, V7_C2_TREE_TAG, &full_c2_leaf, record.salt),
        ));
    }

    let mut level = Vec::with_capacity(V6_QUERY_COUNT);
    let mut next = Vec::with_capacity(V6_QUERY_COUNT);
    if !verify_two_minimal_subtrees216_bytes(
        hash,
        (wire.c1_root, wire.c2_root),
        18,
        &entries,
        (wire.c1_frontier, wire.c2_frontier),
        &mut level,
        &mut next,
    ) {
        return Err(V6WireError::MerkleMismatch);
    }
    Ok(combined)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{CM31, P};
    use crate::v6_onefold::{binary_frontier_nodes, prepare_v6_onefold_coordinates};
    use crate::v7_merkle::node_hash216;
    use alloc::vec;
    use sha2::{Digest, Sha256};

    fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        for input in inputs {
            hasher.update(input);
        }
        hasher.finalize().into()
    }

    fn minimal_root216(entries: &[(u32, V7Digest)], depth: u32, frontier: &[V7Digest]) -> V7Digest {
        let mut level = entries.to_vec();
        let mut node_pos = 0usize;
        for _ in 0..depth {
            let mut next = Vec::new();
            let mut index = 0usize;
            while index < level.len() {
                let (position, value) = level[index];
                let parent = if position & 1 == 0
                    && index + 1 < level.len()
                    && level[index + 1].0 == position + 1
                {
                    let right = level[index + 1].1;
                    index += 2;
                    node_hash216(test_hash, &value, &right)
                } else {
                    let sibling = frontier[node_pos];
                    node_pos += 1;
                    index += 1;
                    if position & 1 == 0 {
                        node_hash216(test_hash, &value, &sibling)
                    } else {
                        node_hash216(test_hash, &sibling, &value)
                    }
                };
                next.push((position >> 1, parent));
            }
            level = next;
        }
        assert_eq!(node_pos, frontier.len());
        assert_eq!(level.len(), 1);
        level[0].1
    }

    fn next_m31(state: &mut u64) -> M31 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        M31((*state % u64::from(P)) as u32)
    }

    fn next_qm31(state: &mut u64) -> QM31 {
        QM31 {
            c0: CM31::new(next_m31(state), next_m31(state)),
            c1: CM31::new(next_m31(state), next_m31(state)),
        }
    }

    #[test]
    fn selected_profile_is_below_thirty_kib_without_shortening_salts() {
        assert_eq!(&V7_COMPACT_PROFILE_BINDING[..8], b"AV7CF001");
        assert_eq!(V7_COMPACT_PROFILE_BINDING[12], 203);
        assert_eq!(V7_COMPACT_PROFILE_BINDING[14], 27);
        assert_eq!(V7_COMPACT_PROFILE_BINDING[15], 32);
        assert_eq!(V7_COMPACT_PROFILE_BINDING[19..22], [35, 31, 34]);
        assert_eq!(V7_COMPACT_PROFILE_BINDING[29..31], [1, 64]);
        assert_eq!(V7_COMPACT_DIGEST_BITS, 216);
        assert_eq!(V7_COMPACT_CLASSICAL_COLLISION_BITS, 108);
        assert_eq!(V7_COMPACT_C1_BYTES_PER_QUERY, 403);
        assert_eq!(V7_COMPACT_C2_BYTES_PER_QUERY, 171);
        assert_eq!(V7_COMPACT_QUERY_BYTES, 606);
        assert_eq!(V7_COMPACT_QUERY_SECTION_BYTES, 9_696);
        assert_eq!(V7_COMPACT_BODY_WITHOUT_FRONTIERS, 19_710);
        assert_eq!(V7_COMPACT_MAX_BODY_BYTES, 30_672);
        assert_eq!(V7_COMPACT_BODY_HEADROOM_BYTES, 48);
    }

    #[test]
    fn compact_wire_parser_freezes_exact_cap203_layout() {
        let mut body = vec![0u8; V7_COMPACT_MAX_BODY_BYTES];
        let wire = V7CompactOneFoldWire::parse(&body, V7_COMPACT_FRONTIER_CAP_PER_TREE).unwrap();
        assert_eq!(wire.fixed_fields_packed.len(), 9_936);
        assert_eq!(wire.c1_frontier.len(), 203 * 27);
        assert_eq!(wire.c2_frontier.len(), 203 * 27);
        assert_eq!(wire.query(0).unwrap().c1_packed.len(), 403);
        assert_eq!(wire.query(0).unwrap().c2_compact_packed.len(), 171);
        assert_eq!(wire.query(15).unwrap().salt.len(), 32);
        assert!(wire.query(16).is_none());

        body.push(0);
        assert_eq!(
            V7CompactOneFoldWire::parse(&body, V7_COMPACT_FRONTIER_CAP_PER_TREE),
            Err(V6WireError::WrongLength)
        );
        assert_eq!(
            V7CompactOneFoldWire::parse(&body[..V7_COMPACT_MAX_BODY_BYTES], 204),
            Err(V6WireError::FrontierTooLarge)
        );
    }

    #[test]
    fn compact_wire_parser_rejects_fixed_and_query_padding_malleability() {
        let mut body = vec![0u8; V7_COMPACT_BODY_WITHOUT_FRONTIERS];
        body[V6_FIXED_PACKED_FIELD_BYTES - 1] = 0x80;
        assert_eq!(
            V7CompactOneFoldWire::parse(&body, 0),
            Err(V6WireError::NonCanonicalM31)
        );
        body[V6_FIXED_PACKED_FIELD_BYTES - 1] = 0;
        let first_c2_last = V6_FIXED_PACKED_FIELD_BYTES
            + V7_COMPACT_ROOT_BYTES
            + V6_WORK_NONCE_BYTES
            + V7_COMPACT_C1_BYTES_PER_QUERY
            + V7_COMPACT_C2_BYTES_PER_QUERY
            - 1;
        body[first_c2_last] = 0x80;
        assert_eq!(
            V7CompactOneFoldWire::parse(&body, 0),
            Err(V6WireError::NonCanonicalM31)
        );
    }

    #[test]
    fn compact_query_schedule_is_the_first_in_one_stream() {
        let mut transcript = Transcript::new(test_hash);
        transcript.absorb(label::PROFILE, b"aspis-v7-compact-query-kat-r0");
        transcript.absorb(label::STATEMENT, &[0x7a; 32]);
        let selected = derive_first_v7_compact_queries(&transcript).unwrap();
        assert!(selected.frontier_nodes <= V7_COMPACT_FRONTIER_CAP_PER_TREE);
        assert_eq!(
            selected.transcript_state,
            selected.accepted_transcript.diagnostic_state()
        );
        for counter in 0..selected.counter {
            let mut earlier = transcript.clone();
            earlier.absorb(label::V7_QUERY_CANDIDATE, &[counter]);
            let queries: [u32; V6_QUERY_COUNT] = earlier
                .challenge_queries_without_replacement(V6_QUERY_COUNT, 1 << 18, 64)
                .unwrap()
                .try_into()
                .unwrap();
            assert!(binary_frontier_nodes(queries, 18).unwrap() > V7_COMPACT_FRONTIER_CAP_PER_TREE);
        }
    }

    #[test]
    fn fold_coefficients_sum_to_one_and_have_a_reconstructible_slot() {
        let mut state = 0x7630_0f17_c0de_0001;
        for _ in 0..64 {
            let alpha = next_qm31(&mut state);
            let x = next_m31(&mut state);
            let y = next_m31(&mut state);
            if x.is_zero() || y.is_zero() {
                continue;
            }
            let coefficients = fold_coefficients(alpha, x.inv(), y.inv());
            assert_eq!(
                coefficients,
                fold_coefficients_basis_reference(alpha, x.inv(), y.inv())
            );
            assert_eq!(
                coefficients.into_iter().fold(QM31::ZERO, QM31::add),
                QM31::ONE
            );
            assert!(first_reconstructible_slot(&coefficients).is_some());
        }
    }

    #[test]
    fn qm31_batch_inverse_matches_all_sixteen_individual_inverses() {
        let mut state = 0x7630_ba7c_1a10_0001;
        for _ in 0..16 {
            let values: [QM31; V6_QUERY_COUNT] = core::array::from_fn(|_| {
                let candidate = next_qm31(&mut state);
                if candidate.is_zero() {
                    QM31::ONE
                } else {
                    candidate
                }
            });
            let inverses = qm31_batch_inverse_16(&values).unwrap();
            for ordinal in 0..V6_QUERY_COUNT {
                assert_eq!(inverses[ordinal], values[ordinal].inv());
                assert_eq!(values[ordinal].mul(inverses[ordinal]), QM31::ONE);
            }
        }
        let mut with_zero = [QM31::ONE; V6_QUERY_COUNT];
        with_zero[7] = QM31::ZERO;
        assert!(qm31_batch_inverse_16(&with_zero).is_none());
    }

    #[test]
    fn omitted_d_reconstruction_restores_the_exact_fold() {
        let mut state = 0x7630_d00d_f01d_0001;
        for _ in 0..64 {
            let mut gamma = next_qm31(&mut state);
            if gamma.is_zero() {
                gamma = QM31::ONE;
            }
            let alpha = next_qm31(&mut state);
            let x = next_m31(&mut state);
            let y = next_m31(&mut state);
            if x.is_zero() || y.is_zero() {
                continue;
            }
            let inv_2x = x.inv();
            let inv_2y = y.inv();
            let coefficients = fold_coefficients(alpha, inv_2x, inv_2y);
            let omitted_slot = first_reconstructible_slot(&coefficients).unwrap();
            let d_power = qm31_power_table::<SPEND_TOTAL_COLUMNS>(gamma)[SPEND_D_GENERATOR_INDEX];
            let d = next_qm31(&mut state);
            let mut partial = core::array::from_fn(|_| next_qm31(&mut state));
            let mut complete = partial;
            complete[omitted_slot] = complete[omitted_slot].add(d_power.mul(d));
            let expected =
                normalized_circle_to_line_arity4_prepared(complete, alpha, inv_2x, inv_2y);
            let (reconstructed_slot, reconstructed_d) =
                reconstruct_omitted_d(partial, expected, gamma, alpha, inv_2x, inv_2y).unwrap();
            assert_eq!(reconstructed_slot, omitted_slot);
            assert_eq!(reconstructed_d, d);
            partial[reconstructed_slot] =
                partial[reconstructed_slot].add(d_power.mul(reconstructed_d));
            assert_eq!(
                normalized_circle_to_line_arity4_prepared(partial, alpha, inv_2x, inv_2y,),
                expected
            );
        }
    }

    #[test]
    fn compact_c2_roundtrip_reconstructs_the_committed_leaf() {
        let mut state = 0x7630_c2c2_f01d_0001;
        let c1 = [0u8; V6_C1_PACKED_BYTES_PER_QUERY];
        for _ in 0..64 {
            let mut gamma = next_qm31(&mut state);
            if gamma.is_zero() {
                gamma = QM31::ONE;
            }
            let alpha = next_qm31(&mut state);
            let x = next_m31(&mut state);
            let y = next_m31(&mut state);
            if x.is_zero() || y.is_zero() {
                continue;
            }
            let inv_2x = x.inv();
            let inv_2y = y.inv();
            let helpers = core::array::from_fn(|_| core::array::from_fn(|_| next_qm31(&mut state)));
            let full = encode_full_c2_leaf(&helpers).unwrap();
            let powers = StateOnlySpendQueryPowers::new(gamma);
            let combined = gamma_combine_v6_packed_layer0(&c1, &full, &powers).unwrap();
            let expected =
                normalized_circle_to_line_arity4_prepared(combined, alpha, inv_2x, inv_2y);
            let coefficients = fold_coefficients(alpha, inv_2x, inv_2y);
            let omitted_slot = first_reconstructible_slot(&coefficients).unwrap();
            let compact = encode_compact_c2_query(&helpers, omitted_slot).unwrap();
            let (reconstructed, reconstructed_combined, selected_slot) =
                reconstruct_compact_c2_query(&c1, &compact, expected, gamma, alpha, inv_2x, inv_2y)
                    .unwrap();
            assert_eq!(selected_slot, omitted_slot);
            assert_eq!(reconstructed, full);
            assert_eq!(reconstructed_combined, combined);
        }
    }

    #[test]
    fn composed_compact_opening_reconstructs_before_merkle_authentication() {
        let queries: [u32; V6_QUERY_COUNT] = core::array::from_fn(|ordinal| ordinal as u32);
        let frontier_nodes = binary_frontier_nodes(queries, 18).unwrap();
        let coordinates = prepare_v6_onefold_coordinates(queries).unwrap();
        let gamma = QM31 {
            c0: CM31::new(M31(17), M31(19)),
            c1: CM31::new(M31(23), M31(29)),
        };
        let alpha = QM31 {
            c0: CM31::new(M31(31), M31(37)),
            c1: CM31::new(M31(41), M31(43)),
        };
        let gamma_powers = qm31_power_table::<SPEND_TOTAL_COLUMNS>(gamma);
        let d_power = gamma_powers[SPEND_D_GENERATOR_INDEX];
        let powers = StateOnlySpendQueryPowers::from_full_table(&gamma_powers);
        let mut state = 0x7630_2160_c2c2_0001;
        let mut expected_folds = [QM31::ZERO; V6_QUERY_COUNT];
        let mut expected_combined = [[QM31::ZERO; 4]; V6_QUERY_COUNT];
        let mut c1_entries = Vec::new();
        let mut c2_entries = Vec::new();
        let mut body = vec![
            0u8;
            V7_COMPACT_BODY_WITHOUT_FRONTIERS
                + 2 * frontier_nodes * V7_COMPACT_DIGEST_BYTES
        ];
        let query_section_offset =
            V6_FIXED_PACKED_FIELD_BYTES + V7_COMPACT_ROOT_BYTES + V6_WORK_NONCE_BYTES;

        for ordinal in 0..V6_QUERY_COUNT {
            let helpers = core::array::from_fn(|_| core::array::from_fn(|_| next_qm31(&mut state)));
            let full_c2 = encode_full_c2_leaf(&helpers).unwrap();
            let c1 = [0u8; V6_C1_PACKED_BYTES_PER_QUERY];
            let combined = gamma_combine_v6_packed_layer0(&c1, &full_c2, &powers).unwrap();
            expected_combined[ordinal] = combined;
            expected_folds[ordinal] = normalized_circle_to_line_arity4_prepared(
                combined,
                alpha,
                coordinates.inv_2x[ordinal],
                coordinates.inv_2y[ordinal],
            );
            let coefficients = fold_coefficients(
                alpha,
                coordinates.inv_2x[ordinal],
                coordinates.inv_2y[ordinal],
            );
            let omitted_slot = first_reconstructible_slot(&coefficients).unwrap();
            let compact_c2 = encode_compact_c2_query(&helpers, omitted_slot).unwrap();
            let salt: [u8; 32] =
                core::array::from_fn(|byte| (ordinal as u8).wrapping_mul(17) ^ byte as u8);
            let record_offset = query_section_offset + ordinal * V7_COMPACT_QUERY_BYTES;
            body[record_offset..record_offset + V7_COMPACT_C1_BYTES_PER_QUERY].copy_from_slice(&c1);
            let c2_offset = record_offset + V7_COMPACT_C1_BYTES_PER_QUERY;
            body[c2_offset..c2_offset + V7_COMPACT_C2_BYTES_PER_QUERY].copy_from_slice(&compact_c2);
            body[c2_offset + V7_COMPACT_C2_BYTES_PER_QUERY
                ..c2_offset + V7_COMPACT_C2_BYTES_PER_QUERY + 32]
                .copy_from_slice(&salt);
            c1_entries.push((
                queries[ordinal],
                private_leaf_hash216(test_hash, V7_C1_TREE_TAG, &c1, &salt),
            ));
            c2_entries.push((
                queries[ordinal],
                private_leaf_hash216(test_hash, V7_C2_TREE_TAG, &full_c2, &salt),
            ));
        }

        let zero_frontier = vec![[0u8; V7_COMPACT_DIGEST_BYTES]; frontier_nodes];
        let c1_root = minimal_root216(&c1_entries, 18, &zero_frontier);
        let c2_root = minimal_root216(&c2_entries, 18, &zero_frontier);
        body[V6_FIXED_PACKED_FIELD_BYTES..V6_FIXED_PACKED_FIELD_BYTES + V7_COMPACT_DIGEST_BYTES]
            .copy_from_slice(&c1_root);
        body[V6_FIXED_PACKED_FIELD_BYTES + V7_COMPACT_DIGEST_BYTES
            ..V6_FIXED_PACKED_FIELD_BYTES + V7_COMPACT_ROOT_BYTES]
            .copy_from_slice(&c2_root);

        let wire = V7CompactOneFoldWire::parse(&body, frontier_nodes).unwrap();
        let actual = verify_reconstruct_and_gamma_combine_v7_openings(
            test_hash,
            &wire,
            queries,
            expected_folds,
            &powers,
            d_power,
            alpha,
            &coordinates,
        )
        .unwrap();
        assert_eq!(actual, expected_combined);

        let first_c2_offset = query_section_offset + V7_COMPACT_C1_BYTES_PER_QUERY;
        body[first_c2_offset] ^= 1;
        let changed = V7CompactOneFoldWire::parse(&body, frontier_nodes).unwrap();
        assert_eq!(
            verify_reconstruct_and_gamma_combine_v7_openings(
                test_hash,
                &changed,
                queries,
                expected_folds,
                &powers,
                d_power,
                alpha,
                &coordinates,
            ),
            Err(V6WireError::MerkleMismatch)
        );
    }

    #[test]
    fn zero_gamma_is_rejected_before_reconstruction() {
        assert_eq!(
            reconstruct_omitted_d(
                [QM31::ZERO; 4],
                QM31::ZERO,
                QM31::ZERO,
                QM31::ZERO,
                M31::ONE,
                M31::ONE,
            ),
            None
        );
    }
}
