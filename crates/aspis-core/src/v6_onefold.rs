//! Host/SBF-neutral wire prototype for the selected V6 one-fold profile.
//!
//! This is deliberately isolated from every deployed instruction. It fixes
//! the 26-C1 + 3-C2 byte arithmetic, rejects non-canonical packed M31 limbs,
//! derives the exact body length from the two public frontier counts, and
//! exposes borrowed sections without allocating.

use alloc::vec::Vec;

use crate::circle_fri::line_domain_x_for_circle;
use crate::field::{CM31, M31, P, QM31};

pub const V6_C1_COLUMNS: usize = 26;
pub const V6_C2_COLUMNS: usize = 3;
pub const V6_QUERY_COUNT: usize = 16;
pub const V6_FRONTIER_CAP_PER_TREE: usize = 209;
pub const V6_FIXED_QM31_VALUES: usize = 670;
pub const V6_FINAL_QM31_OFFSET: usize =
    1 + 10 * 27 + 4 * (V6_C1_COLUMNS + V6_C2_COLUMNS) + 1 + 2 + 4 * 6;
pub const V6_FINAL_QM31_VALUES: usize = 256;
pub const V6_FIXED_M31_LIMBS: usize = 4 * V6_FIXED_QM31_VALUES;
pub const V6_FIXED_PACKED_FIELD_BYTES: usize = packed_bytes(V6_FIXED_M31_LIMBS);
pub const V6_ROOT_BYTES: usize = 2 * 32;
pub const V6_WORK_NONCE_BYTES: usize = 3 * 8;
pub const V6_FIXED_BYTES: usize = V6_FIXED_PACKED_FIELD_BYTES + V6_ROOT_BYTES + V6_WORK_NONCE_BYTES;

pub const V6_C1_LIMBS_PER_QUERY: usize = 4 * V6_C1_COLUMNS;
pub const V6_C2_LIMBS_PER_QUERY: usize = 4 * 4 * V6_C2_COLUMNS;
pub const V6_C1_PACKED_BYTES_PER_QUERY: usize = packed_bytes(V6_C1_LIMBS_PER_QUERY);
pub const V6_C2_PACKED_BYTES_PER_QUERY: usize = packed_bytes(V6_C2_LIMBS_PER_QUERY);
pub const V6_PRIVATE_SALT_BYTES: usize = 32;
pub const V6_QUERY_BYTES: usize =
    V6_C1_PACKED_BYTES_PER_QUERY + V6_C2_PACKED_BYTES_PER_QUERY + V6_PRIVATE_SALT_BYTES;
pub const V6_QUERY_SECTION_BYTES: usize = V6_QUERY_COUNT * V6_QUERY_BYTES;
pub const V6_BODY_WITHOUT_FRONTIERS: usize = V6_FIXED_BYTES + V6_QUERY_SECTION_BYTES;
pub const V6_MAX_BODY_BYTES: usize = V6_BODY_WITHOUT_FRONTIERS + 2 * V6_FRONTIER_CAP_PER_TREE * 32;
pub const V6_HARD_BODY_LIMIT: usize = 40 * 1024;

const fn packed_bytes(limbs: usize) -> usize {
    (limbs * 31 + 7) / 8
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V6WireError {
    FrontierTooLarge,
    WrongLength,
    NonCanonicalM31,
    InvalidQuerySchedule,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V6QueryRecord<'a> {
    pub c1_packed: &'a [u8],
    pub c2_packed: &'a [u8],
    pub salt: &'a [u8; V6_PRIVATE_SALT_BYTES],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V6OneFoldWire<'a> {
    pub fixed_fields_packed: &'a [u8],
    pub c1_root: &'a [u8; 32],
    pub c2_root: &'a [u8; 32],
    pub work_nonces: &'a [u8; V6_WORK_NONCE_BYTES],
    query_section: &'a [u8],
    pub c1_frontier: &'a [u8],
    pub c2_frontier: &'a [u8],
}

impl<'a> V6OneFoldWire<'a> {
    pub fn parse(
        bytes: &'a [u8],
        c1_frontier_nodes: usize,
        c2_frontier_nodes: usize,
    ) -> Result<Self, V6WireError> {
        Self::parse_inner(bytes, c1_frontier_nodes, c2_frontier_nodes, true)
    }

    /// Parse exact section boundaries while deferring field canonicality to
    /// the consumers that already decode each section.
    ///
    /// A complete verifier must consume and canonically decode every field.
    /// This avoids a redundant whole-proof scan; it does not permit any field
    /// to remain unchecked.
    pub fn parse_deferred_canonicality(
        bytes: &'a [u8],
        c1_frontier_nodes: usize,
        c2_frontier_nodes: usize,
    ) -> Result<Self, V6WireError> {
        Self::parse_inner(bytes, c1_frontier_nodes, c2_frontier_nodes, false)
    }

    fn parse_inner(
        bytes: &'a [u8],
        c1_frontier_nodes: usize,
        c2_frontier_nodes: usize,
        validate_fields: bool,
    ) -> Result<Self, V6WireError> {
        if c1_frontier_nodes > V6_FRONTIER_CAP_PER_TREE
            || c2_frontier_nodes > V6_FRONTIER_CAP_PER_TREE
        {
            return Err(V6WireError::FrontierTooLarge);
        }
        let c1_frontier_bytes = c1_frontier_nodes
            .checked_mul(32)
            .ok_or(V6WireError::WrongLength)?;
        let c2_frontier_bytes = c2_frontier_nodes
            .checked_mul(32)
            .ok_or(V6WireError::WrongLength)?;
        let expected = V6_BODY_WITHOUT_FRONTIERS
            .checked_add(c1_frontier_bytes)
            .and_then(|n| n.checked_add(c2_frontier_bytes))
            .ok_or(V6WireError::WrongLength)?;
        if bytes.len() != expected || bytes.len() > V6_HARD_BODY_LIMIT {
            return Err(V6WireError::WrongLength);
        }

        let (fixed_fields_packed, rest) = bytes.split_at(V6_FIXED_PACKED_FIELD_BYTES);
        if validate_fields {
            validate_packed_m31(fixed_fields_packed, V6_FIXED_M31_LIMBS)?;
        }
        let (c1_root_bytes, rest) = rest.split_at(32);
        let (c2_root_bytes, rest) = rest.split_at(32);
        let (nonce_bytes, rest) = rest.split_at(V6_WORK_NONCE_BYTES);
        let (query_section, rest) = rest.split_at(V6_QUERY_SECTION_BYTES);

        if validate_fields {
            for query in 0..V6_QUERY_COUNT {
                let start = query * V6_QUERY_BYTES;
                let c1_end = start + V6_C1_PACKED_BYTES_PER_QUERY;
                let c2_end = c1_end + V6_C2_PACKED_BYTES_PER_QUERY;
                validate_packed_m31(&query_section[start..c1_end], V6_C1_LIMBS_PER_QUERY)?;
                validate_packed_m31(&query_section[c1_end..c2_end], V6_C2_LIMBS_PER_QUERY)?;
            }
        }

        let (c1_frontier, c2_frontier) = rest.split_at(c1_frontier_bytes);
        debug_assert_eq!(c2_frontier.len(), c2_frontier_bytes);
        Ok(Self {
            fixed_fields_packed,
            c1_root: c1_root_bytes
                .try_into()
                .map_err(|_| V6WireError::WrongLength)?,
            c2_root: c2_root_bytes
                .try_into()
                .map_err(|_| V6WireError::WrongLength)?,
            work_nonces: nonce_bytes
                .try_into()
                .map_err(|_| V6WireError::WrongLength)?,
            query_section,
            c1_frontier,
            c2_frontier,
        })
    }

    pub fn query(&self, index: usize) -> Option<V6QueryRecord<'a>> {
        if index >= V6_QUERY_COUNT {
            return None;
        }
        let start = index * V6_QUERY_BYTES;
        let c1_end = start + V6_C1_PACKED_BYTES_PER_QUERY;
        let c2_end = c1_end + V6_C2_PACKED_BYTES_PER_QUERY;
        let end = c2_end + V6_PRIVATE_SALT_BYTES;
        Some(V6QueryRecord {
            c1_packed: &self.query_section[start..c1_end],
            c2_packed: &self.query_section[c1_end..c2_end],
            salt: self.query_section[c2_end..end].try_into().ok()?,
        })
    }
}

pub fn packed_m31_at(bytes: &[u8], index: usize) -> Option<u32> {
    let bit_start = index.checked_mul(31)?;
    if bit_start.checked_add(31)? > bytes.len().checked_mul(8)? {
        return None;
    }
    let byte_start = bit_start / 8;
    let shift = bit_start % 8;
    let mut window = 0u64;
    let available = core::cmp::min(5, bytes.len() - byte_start);
    for offset in 0..available {
        window |= u64::from(bytes[byte_start + offset]) << (8 * offset);
    }
    Some(((window >> shift) & 0x7fff_ffff) as u32)
}

pub fn packed_qm31_at(bytes: &[u8], index: usize) -> Option<QM31> {
    let limb = index.checked_mul(4)?;
    Some(QM31 {
        c0: CM31::new(
            M31(packed_m31_at(bytes, limb)?),
            M31(packed_m31_at(bytes, limb + 1)?),
        ),
        c1: CM31::new(
            M31(packed_m31_at(bytes, limb + 2)?),
            M31(packed_m31_at(bytes, limb + 3)?),
        ),
    })
}

pub fn validate_packed_m31(bytes: &[u8], limbs: usize) -> Result<(), V6WireError> {
    if bytes.len() != packed_bytes(limbs) {
        return Err(V6WireError::WrongLength);
    }
    for index in 0..limbs {
        let value = packed_m31_at(bytes, index).ok_or(V6WireError::WrongLength)?;
        if value >= P {
            return Err(V6WireError::NonCanonicalM31);
        }
    }
    let used_bits = limbs * 31;
    for bit in used_bits..bytes.len() * 8 {
        if ((bytes[bit / 8] >> (bit % 8)) & 1) != 0 {
            return Err(V6WireError::NonCanonicalM31);
        }
    }
    Ok(())
}

/// Number of sibling hashes in the minimal binary authentication frontier.
///
/// The input may arrive in any order. Duplicates and indices outside the
/// depth-`depth` tree are rejected. The implementation uses a fixed stack
/// array and is suitable for the verifier's sixteen-query schedule.
pub fn binary_frontier_nodes<const Q: usize>(
    mut queries: [u32; Q],
    depth: u8,
) -> Result<usize, V6WireError> {
    if Q == 0 || depth >= 32 {
        return Err(V6WireError::InvalidQuerySchedule);
    }
    let leaf_count = 1u32
        .checked_shl(u32::from(depth))
        .ok_or(V6WireError::InvalidQuerySchedule)?;

    for index in 1..Q {
        let value = queries[index];
        let mut cursor = index;
        while cursor > 0 && value < queries[cursor - 1] {
            queries[cursor] = queries[cursor - 1];
            cursor -= 1;
        }
        queries[cursor] = value;
    }
    if queries[Q - 1] >= leaf_count {
        return Err(V6WireError::InvalidQuerySchedule);
    }
    for index in 1..Q {
        if queries[index - 1] == queries[index] {
            return Err(V6WireError::InvalidQuerySchedule);
        }
    }

    let mut active = Q;
    let mut frontier = 0usize;
    for _ in 0..depth {
        let mut read = 0usize;
        let mut write = 0usize;
        while read < active {
            let node = queries[read];
            let parent = node >> 1;
            let has_sibling = read + 1 < active && queries[read + 1] >> 1 == parent;
            if has_sibling {
                read += 2;
            } else {
                frontier += 1;
                read += 1;
            }
            queries[write] = parent;
            write += 1;
        }
        active = write;
    }
    if active != 1 || queries[0] != 0 {
        return Err(V6WireError::InvalidQuerySchedule);
    }
    Ok(frontier)
}

/// Return the first compact candidate and reject malformed candidate streams.
/// A future transcript driver must derive `candidates` itself; accepting a
/// proof-carried counter without checking every earlier candidate is unsafe.
pub fn first_compact_candidate<const Q: usize, const C: usize>(
    candidates: &[[u32; Q]; C],
    depth: u8,
    frontier_cap: usize,
) -> Result<Option<(usize, usize)>, V6WireError> {
    for (index, candidate) in candidates.iter().enumerate() {
        let frontier = binary_frontier_nodes(*candidate, depth)?;
        if frontier <= frontier_cap {
            return Ok(Some((index, frontier)));
        }
    }
    Ok(None)
}

fn natural_line_weights_256(mut point: M31) -> [M31; V6_FINAL_QM31_VALUES] {
    let mut factors = [M31::ZERO; 8];
    for factor in &mut factors {
        *factor = point;
        point = point.mul(point).double().sub(M31::ONE);
    }
    let mut weights = [M31::ZERO; V6_FINAL_QM31_VALUES];
    weights[0] = M31::ONE;
    for index in 1..V6_FINAL_QM31_VALUES {
        let bit = index.trailing_zeros() as usize;
        weights[index] = weights[index ^ (1usize << bit)].mul(factors[bit]);
    }
    weights
}

/// Evaluate the disclosed 256-coefficient natural line tensor directly from
/// its packed 31-bit representation. This needs a 1-KiB M31 weight table and
/// never materializes the 4-KiB QM31 coefficient vector on the SBF stack.
pub fn evaluate_packed_final256(
    fixed_fields_packed: &[u8],
    point: M31,
) -> Result<QM31, V6WireError> {
    if fixed_fields_packed.len() != V6_FIXED_PACKED_FIELD_BYTES {
        return Err(V6WireError::WrongLength);
    }
    let weights = natural_line_weights_256(point);
    let mut result = QM31::ZERO;
    for (index, weight) in weights.iter().copied().enumerate() {
        let coefficient = packed_qm31_at(fixed_fields_packed, V6_FINAL_QM31_OFFSET + index)
            .ok_or(V6WireError::WrongLength)?;
        if coefficient.c0.a.0 >= P
            || coefficient.c0.b.0 >= P
            || coefficient.c1.a.0 >= P
            || coefficient.c1.b.0 >= P
        {
            return Err(V6WireError::NonCanonicalM31);
        }
        result = result.add(coefficient.mul_m31(weight));
    }
    Ok(result)
}

pub fn evaluate_packed_final256_at_query(
    fixed_fields_packed: &[u8],
    query: u32,
) -> Result<QM31, V6WireError> {
    if query >= 1 << 18 {
        return Err(V6WireError::InvalidQuerySchedule);
    }
    let point = line_domain_x_for_circle(20, 1, query as usize)
        .map_err(|_| V6WireError::InvalidQuerySchedule)?;
    evaluate_packed_final256(fixed_fields_packed, point)
}

fn decode_packed_final256(fixed_fields_packed: &[u8]) -> Result<Vec<QM31>, V6WireError> {
    if fixed_fields_packed.len() != V6_FIXED_PACKED_FIELD_BYTES {
        return Err(V6WireError::WrongLength);
    }
    let mut coefficients = Vec::with_capacity(V6_FINAL_QM31_VALUES);
    for index in 0..V6_FINAL_QM31_VALUES {
        let coefficient = packed_qm31_at(fixed_fields_packed, V6_FINAL_QM31_OFFSET + index)
            .ok_or(V6WireError::WrongLength)?;
        if coefficient.c0.a.0 >= P
            || coefficient.c0.b.0 >= P
            || coefficient.c1.a.0 >= P
            || coefficient.c1.b.0 >= P
        {
            return Err(V6WireError::NonCanonicalM31);
        }
        coefficients.push(coefficient);
    }
    Ok(coefficients)
}

fn evaluate_final256_coefficients(coefficients: &[QM31], point: M31) -> Result<QM31, V6WireError> {
    if coefficients.len() != V6_FINAL_QM31_VALUES {
        return Err(V6WireError::WrongLength);
    }
    let weights = natural_line_weights_256(point);
    // Each accumulator is below 256 * (P - 1)^2 < 2^70. Keeping the raw
    // 32-by-32-bit products in u128 and reducing once per output limb avoids
    // 1,024 modular reductions per query without changing the field result.
    let mut c0a = 0u128;
    let mut c0b = 0u128;
    let mut c1a = 0u128;
    let mut c1b = 0u128;
    for (coefficient, weight) in coefficients.iter().zip(weights) {
        let weight = u64::from(weight.0);
        c0a += u128::from(u64::from(coefficient.c0.a.0) * weight);
        c0b += u128::from(u64::from(coefficient.c0.b.0) * weight);
        c1a += u128::from(u64::from(coefficient.c1.a.0) * weight);
        c1b += u128::from(u64::from(coefficient.c1.b.0) * weight);
    }
    Ok(QM31 {
        c0: CM31::new(M31::reduce_u128(c0a), M31::reduce_u128(c0b)),
        c1: CM31::new(M31::reduce_u128(c1a), M31::reduce_u128(c1b)),
    })
}

/// Canonically decode the disclosed terminal vector once, then evaluate it at
/// all sixteen verifier queries. The shared heap allocation avoids sixteen
/// repeated packed-bit scans without putting the 4-KiB coefficient vector on
/// the SBF stack.
pub fn evaluate_packed_final256_at_queries(
    fixed_fields_packed: &[u8],
    queries: [u32; V6_QUERY_COUNT],
) -> Result<[QM31; V6_QUERY_COUNT], V6WireError> {
    let coefficients = decode_packed_final256(fixed_fields_packed)?;
    let mut outputs = [QM31::ZERO; V6_QUERY_COUNT];
    for (output, query) in outputs.iter_mut().zip(queries) {
        if query >= 1 << 18 {
            return Err(V6WireError::InvalidQuerySchedule);
        }
        let point = line_domain_x_for_circle(20, 1, query as usize)
            .map_err(|_| V6WireError::InvalidQuerySchedule)?;
        *output = evaluate_final256_coefficients(&coefficients, point)?;
    }
    Ok(outputs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;

    fn pack(values: &[u32]) -> Vec<u8> {
        let mut out = vec![0u8; packed_bytes(values.len())];
        for (index, value) in values.iter().copied().enumerate() {
            let bit_start = index * 31;
            for bit in 0..31 {
                if ((value >> bit) & 1) != 0 {
                    let output_bit = bit_start + bit;
                    out[output_bit / 8] |= 1 << (output_bit % 8);
                }
            }
        }
        out
    }

    fn valid_body(c1_frontier: usize, c2_frontier: usize) -> Vec<u8> {
        vec![0u8; V6_BODY_WITHOUT_FRONTIERS + 32 * (c1_frontier + c2_frontier)]
    }

    #[test]
    fn selected_profile_constants_are_exact() {
        assert_eq!(V6_FIXED_QM31_VALUES, 670);
        assert_eq!(V6_FINAL_QM31_OFFSET, 414);
        assert_eq!(V6_FINAL_QM31_OFFSET + V6_FINAL_QM31_VALUES, 670);
        assert_eq!(V6_FIXED_PACKED_FIELD_BYTES, 10_385);
        assert_eq!(V6_FIXED_BYTES, 10_473);
        assert_eq!(V6_C1_PACKED_BYTES_PER_QUERY, 403);
        assert_eq!(V6_C2_PACKED_BYTES_PER_QUERY, 186);
        assert_eq!(V6_QUERY_BYTES, 621);
        assert_eq!(V6_MAX_BODY_BYTES, 33_785);
        assert_eq!(V6_HARD_BODY_LIMIT - V6_MAX_BODY_BYTES, 7_175);
    }

    #[test]
    fn packed_limb_boundaries_and_cross_byte_positions() {
        let values = [0, 1, P - 1, 17, P - 2, 0x1234_5678];
        let encoded = pack(&values);
        validate_packed_m31(&encoded, values.len()).unwrap();
        for (index, expected) in values.iter().copied().enumerate() {
            assert_eq!(packed_m31_at(&encoded, index), Some(expected));
        }
        let invalid = pack(&[P]);
        assert_eq!(
            validate_packed_m31(&invalid, 1),
            Err(V6WireError::NonCanonicalM31)
        );
    }

    #[test]
    fn parser_accepts_exact_variable_frontiers() {
        let body = valid_body(201, 209);
        let parsed = V6OneFoldWire::parse(&body, 201, 209).unwrap();
        assert_eq!(parsed.c1_frontier.len(), 201 * 32);
        assert_eq!(parsed.c2_frontier.len(), 209 * 32);
        assert_eq!(parsed.query(0).unwrap().c1_packed.len(), 403);
        assert_eq!(parsed.query(15).unwrap().c2_packed.len(), 186);
        assert!(parsed.query(16).is_none());
    }

    #[test]
    fn parser_rejects_length_frontier_and_noncanonical_field_errors() {
        let exact = valid_body(209, 209);
        assert!(V6OneFoldWire::parse(&exact, 209, 209).is_ok());
        assert_eq!(
            V6OneFoldWire::parse(&exact[..exact.len() - 1], 209, 209),
            Err(V6WireError::WrongLength)
        );
        let mut trailing = exact.clone();
        trailing.push(0);
        assert_eq!(
            V6OneFoldWire::parse(&trailing, 209, 209),
            Err(V6WireError::WrongLength)
        );
        assert_eq!(
            V6OneFoldWire::parse(&exact, 210, 209),
            Err(V6WireError::FrontierTooLarge)
        );

        let mut noncanonical = exact;
        noncanonical[..4].copy_from_slice(&pack(&[P]));
        assert_eq!(
            V6OneFoldWire::parse(&noncanonical, 209, 209),
            Err(V6WireError::NonCanonicalM31)
        );
    }

    #[test]
    fn binary_frontier_matches_clustered_and_spread_schedules() {
        let clustered: [u32; 16] = core::array::from_fn(|index| index as u32);
        let spread: [u32; 16] = core::array::from_fn(|index| (index as u32) * (1 << 14));
        let clustered_frontier = binary_frontier_nodes(clustered, 18).unwrap();
        let spread_frontier = binary_frontier_nodes(spread, 18).unwrap();
        assert!(clustered_frontier < spread_frontier);
        assert!(clustered_frontier <= V6_FRONTIER_CAP_PER_TREE);
        assert!(spread_frontier > V6_FRONTIER_CAP_PER_TREE);
    }

    #[test]
    fn first_compact_candidate_cannot_skip_an_earlier_valid_schedule() {
        let spread: [u32; 16] = core::array::from_fn(|index| (index as u32) * (1 << 14));
        let first_compact: [u32; 16] = core::array::from_fn(|index| index as u32);
        let later_compact: [u32; 16] = core::array::from_fn(|index| 64 + index as u32);
        let candidates = [spread, first_compact, later_compact];
        let selected = first_compact_candidate(&candidates, 18, V6_FRONTIER_CAP_PER_TREE)
            .unwrap()
            .unwrap();
        assert_eq!(selected.0, 1);
        assert_eq!(
            selected.1,
            binary_frontier_nodes(first_compact, 18).unwrap()
        );
    }

    #[test]
    fn frontier_rejects_duplicates_and_out_of_range_queries() {
        let duplicate = [7u32; 16];
        assert_eq!(
            binary_frontier_nodes(duplicate, 18),
            Err(V6WireError::InvalidQuerySchedule)
        );
        let mut out_of_range: [u32; 16] = core::array::from_fn(|index| index as u32);
        out_of_range[15] = 1 << 18;
        assert_eq!(
            binary_frontier_nodes(out_of_range, 18),
            Err(V6WireError::InvalidQuerySchedule)
        );
    }

    #[test]
    fn packed_final256_evaluator_matches_in_place_tensor_contraction() {
        let mut limbs = vec![0u32; V6_FIXED_M31_LIMBS];
        for coefficient in 0..V6_FINAL_QM31_VALUES {
            let start = 4 * (V6_FINAL_QM31_OFFSET + coefficient);
            for limb in 0..4 {
                limbs[start + limb] = ((coefficient * 17 + limb * 29 + 1) as u32) % P;
            }
        }
        let packed = pack(&limbs);
        let point = M31(1_234_567);
        let actual = evaluate_packed_final256(&packed, point).unwrap();

        let mut level: Vec<QM31> = (0..V6_FINAL_QM31_VALUES)
            .map(|index| packed_qm31_at(&packed, V6_FINAL_QM31_OFFSET + index).unwrap())
            .collect();
        let mut factor = point;
        while level.len() > 1 {
            let mut next = Vec::with_capacity(level.len() / 2);
            for pair in level.chunks_exact(2) {
                next.push(pair[0].add(pair[1].mul_m31(factor)));
            }
            level = next;
            factor = factor.mul(factor).double().sub(M31::ONE);
        }
        assert_eq!(actual, level[0]);
    }

    #[test]
    fn shared_decode_matches_sixteen_independent_evaluations() {
        let mut limbs = vec![0u32; V6_FIXED_M31_LIMBS];
        for coefficient in 0..V6_FINAL_QM31_VALUES {
            let start = 4 * (V6_FINAL_QM31_OFFSET + coefficient);
            for limb in 0..4 {
                limbs[start + limb] = ((coefficient * 31 + limb * 7 + 3) as u32) % P;
            }
        }
        let packed = pack(&limbs);
        let queries: [u32; V6_QUERY_COUNT] =
            core::array::from_fn(|index| 1_001 + index as u32 * 7_919);
        let shared = evaluate_packed_final256_at_queries(&packed, queries).unwrap();
        for (index, query) in queries.into_iter().enumerate() {
            assert_eq!(
                shared[index],
                evaluate_packed_final256_at_query(&packed, query).unwrap()
            );
        }
    }

    #[test]
    fn deferred_parser_does_not_hide_noncanonical_terminal_coefficients() {
        let mut body = valid_body(209, 209);
        let limb = 4 * V6_FINAL_QM31_OFFSET;
        let bit_start = limb * 31;
        let encoded = pack(&[P]);
        for bit in 0..31 {
            let output_bit = bit_start + bit;
            let mask = 1u8 << (output_bit % 8);
            if ((encoded[bit / 8] >> (bit % 8)) & 1) != 0 {
                body[output_bit / 8] |= mask;
            } else {
                body[output_bit / 8] &= !mask;
            }
        }

        assert_eq!(
            V6OneFoldWire::parse(&body, 209, 209),
            Err(V6WireError::NonCanonicalM31)
        );
        let parsed = V6OneFoldWire::parse_deferred_canonicality(&body, 209, 209).unwrap();
        assert_eq!(
            evaluate_packed_final256_at_queries(parsed.fixed_fields_packed, [0; V6_QUERY_COUNT]),
            Err(V6WireError::NonCanonicalM31)
        );
    }
}
