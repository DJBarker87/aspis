//! Host/SBF-neutral wire prototype for the selected V6 one-fold profile.
//!
//! This is deliberately isolated from every deployed instruction. It fixes
//! the 26-C1 + 3-C2 byte arithmetic, rejects non-canonical packed M31 limbs,
//! derives the exact body length from the two public frontier counts, and
//! exposes borrowed sections without allocating.

use alloc::vec::Vec;

use crate::circle_fri::{
    line_domain_x_for_circle, normalized_circle_to_line_arity4_prepared_polynomial_refs,
    selected_circle_fiber_points_shared,
};
use crate::field::{
    m31_batch_inverse, qm31_sum_products3_prepared, PreparedQm31Multiplier, CM31, M31, P, QM31,
};
use crate::merkle::verify_minimal_subtree_bytes;
use crate::state_only_private_merkle::private_leaf_hash;
use crate::state_only_spend_query::StateOnlySpendQueryPowers;
use crate::HashFn;

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
pub const V6_C1_TREE_TAG: u8 = 0x70;
pub const V6_C2_TREE_TAG: u8 = 0xf0;

const fn packed_bytes(limbs: usize) -> usize {
    (limbs * 31 + 7) / 8
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V6WireError {
    FrontierTooLarge,
    WrongLength,
    NonCanonicalM31,
    InvalidQuerySchedule,
    MerkleMismatch,
    FriMismatch,
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

/// Sequential reader for the proof's little-endian 31-bit limb packing.
///
/// All V6 packed sections contain a multiple of eight limbs, so their final
/// limb ends on a byte boundary. Consumers check the exact byte length before
/// constructing this reader and then consume the protocol-fixed limb count.
struct PackedM31Reader<'a> {
    bytes: &'a [u8],
    byte_index: usize,
    buffer: u64,
    buffered_bits: u8,
}

impl<'a> PackedM31Reader<'a> {
    #[inline(always)]
    fn new(bytes: &'a [u8]) -> Self {
        Self {
            bytes,
            byte_index: 0,
            buffer: 0,
            buffered_bits: 0,
        }
    }

    #[inline(always)]
    fn next(&mut self) -> u32 {
        while self.buffered_bits < 31 {
            debug_assert!(self.byte_index < self.bytes.len());
            self.buffer |= u64::from(self.bytes[self.byte_index]) << self.buffered_bits;
            self.byte_index += 1;
            self.buffered_bits += 8;
        }
        let value = (self.buffer & 0x7fff_ffff) as u32;
        self.buffer >>= 31;
        self.buffered_bits -= 31;
        value
    }

    #[inline(always)]
    fn qm31(&mut self) -> QM31 {
        QM31 {
            c0: CM31::new(M31(self.next()), M31(self.next())),
            c1: CM31::new(M31(self.next()), M31(self.next())),
        }
    }
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

/// Authenticate the sixteen packed C1 and C2 records against two distinct
/// typed binary trees. Each query uses one shared hidden salt, but the tree
/// tags make a C1 leaf and a C2 leaf different hash inputs even when their
/// values happen to agree.
pub fn verify_v6_binary_openings(
    hash: HashFn,
    wire: &V6OneFoldWire<'_>,
    queries: [u32; V6_QUERY_COUNT],
) -> Result<(), V6WireError> {
    let mut order: [(u32, usize); V6_QUERY_COUNT] =
        core::array::from_fn(|ordinal| (queries[ordinal], ordinal));
    order.sort_unstable_by_key(|entry| entry.0);
    if order[V6_QUERY_COUNT - 1].0 >= 1 << 18 {
        return Err(V6WireError::InvalidQuerySchedule);
    }
    for pair in order.windows(2) {
        if pair[0].0 == pair[1].0 {
            return Err(V6WireError::InvalidQuerySchedule);
        }
    }

    let mut c1_entries = Vec::with_capacity(V6_QUERY_COUNT);
    let mut c2_entries = Vec::with_capacity(V6_QUERY_COUNT);
    for (query, ordinal) in order {
        let record = wire
            .query(ordinal)
            .ok_or(V6WireError::InvalidQuerySchedule)?;
        validate_packed_m31(record.c1_packed, V6_C1_LIMBS_PER_QUERY)?;
        validate_packed_m31(record.c2_packed, V6_C2_LIMBS_PER_QUERY)?;
        c1_entries.push((
            query,
            private_leaf_hash(hash, V6_C1_TREE_TAG, record.c1_packed, record.salt),
        ));
        c2_entries.push((
            query,
            private_leaf_hash(hash, V6_C2_TREE_TAG, record.c2_packed, record.salt),
        ));
    }

    let mut level = Vec::with_capacity(V6_QUERY_COUNT);
    let mut next = Vec::with_capacity(V6_QUERY_COUNT);
    if !verify_minimal_subtree_bytes(
        hash,
        wire.c1_root,
        18,
        &c1_entries,
        wire.c1_frontier,
        &mut level,
        &mut next,
    ) || !verify_minimal_subtree_bytes(
        hash,
        wire.c2_root,
        18,
        &c2_entries,
        wire.c2_frontier,
        &mut level,
        &mut next,
    ) {
        return Err(V6WireError::MerkleMismatch);
    }
    Ok(())
}

/// Combine one packed 26-M31-plus-3-QM31 fibre with the exact scalar-power
/// table used by the selected state-only spend profile.
pub fn gamma_combine_v6_packed_layer0(
    c1_packed: &[u8],
    c2_packed: &[u8],
    powers: &StateOnlySpendQueryPowers,
) -> Result<[QM31; 4], V6WireError> {
    if c1_packed.len() != V6_C1_PACKED_BYTES_PER_QUERY
        || c2_packed.len() != V6_C2_PACKED_BYTES_PER_QUERY
    {
        return Err(V6WireError::WrongLength);
    }

    let mut reader = PackedM31Reader::new(c1_packed);
    let mut invalid = 0u32;
    let mut combined = [QM31::ZERO; 4];
    for output in &mut combined {
        let mut sums = [0u64; 4];
        for block in 0..(V6_C1_COLUMNS / 4) {
            let mut raw = [0u64; 4];
            for column in block * 4..block * 4 + 4 {
                let value = reader.next();
                invalid |= u32::from(value >= P);
                let value = u64::from(value & P);
                let limbs = powers.base.c1_limbs[column];
                for limb in 0..4 {
                    raw[limb] += u64::from(limbs[limb]) * value;
                }
            }
            for limb in 0..4 {
                sums[limb] += u64::from(M31::reduce_u64(raw[limb]).0);
            }
        }
        let mut raw = [0u64; 4];
        for column in V6_C1_COLUMNS - 2..V6_C1_COLUMNS {
            let value = reader.next();
            invalid |= u32::from(value >= P);
            let value = u64::from(value & P);
            let limbs = powers.base.c1_limbs[column];
            for limb in 0..4 {
                raw[limb] += u64::from(limbs[limb]) * value;
            }
        }
        for limb in 0..4 {
            sums[limb] += u64::from(M31::reduce_u64(raw[limb]).0);
        }
        *output = QM31 {
            c0: CM31::new(M31::reduce_u64(sums[0]), M31::reduce_u64(sums[1])),
            c1: CM31::new(M31::reduce_u64(sums[2]), M31::reduce_u64(sums[3])),
        };
    }
    debug_assert_eq!(reader.byte_index, c1_packed.len());
    debug_assert_eq!(reader.buffered_bits, 0);

    let helper_powers = [powers.base.helpers[0], powers.base.helpers[1], powers.d];
    let mut reader = PackedM31Reader::new(c2_packed);
    let mut helpers = [[QM31::ZERO; 4]; V6_C2_COLUMNS];
    for values in &mut helpers {
        for value in values {
            *value = reader.qm31();
            invalid |= u32::from(
                value.c0.a.0 >= P || value.c0.b.0 >= P || value.c1.a.0 >= P || value.c1.b.0 >= P,
            );
        }
    }
    debug_assert_eq!(reader.byte_index, c2_packed.len());
    debug_assert_eq!(reader.buffered_bits, 0);
    for (slot, output) in combined.iter_mut().enumerate() {
        let values = [helpers[0][slot], helpers[1][slot], helpers[2][slot]];
        *output = output.add(qm31_sum_products3_prepared(&helper_powers, &values));
    }
    if invalid != 0 {
        return Err(V6WireError::NonCanonicalM31);
    }
    Ok(combined)
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V6OneFoldCoordinates {
    pub inv_2x: [M31; V6_QUERY_COUNT],
    pub inv_2y: [M31; V6_QUERY_COUNT],
}

/// Derive the two public inverse coordinates used by the sole circle fold at
/// each selected fibre. One batch inversion serves all sixteen queries.
pub fn prepare_v6_onefold_coordinates(
    queries: [u32; V6_QUERY_COUNT],
) -> Result<V6OneFoldCoordinates, V6WireError> {
    let points = selected_circle_fiber_points_shared(20, &queries)
        .map_err(|_| V6WireError::InvalidQuerySchedule)?;
    let mut denominators = [M31::ZERO; 2 * V6_QUERY_COUNT];
    for (ordinal, point) in points.iter().enumerate() {
        let x = point.x.double();
        let y = point.y.double();
        if x.is_zero() || y.is_zero() {
            return Err(V6WireError::InvalidQuerySchedule);
        }
        denominators[2 * ordinal] = x;
        denominators[2 * ordinal + 1] = y;
    }
    let mut inverses = [M31::ZERO; 2 * V6_QUERY_COUNT];
    m31_batch_inverse(&denominators, &mut inverses);
    if denominators[0].mul(inverses[0]) != M31::ONE {
        return Err(V6WireError::InvalidQuerySchedule);
    }
    Ok(V6OneFoldCoordinates {
        inv_2x: core::array::from_fn(|ordinal| inverses[2 * ordinal]),
        inv_2y: core::array::from_fn(|ordinal| inverses[2 * ordinal + 1]),
    })
}

/// Decode and gamma-combine all authenticated query records. The caller must
/// first authenticate and canonically validate these exact records with
/// [`verify_v6_binary_openings`].
pub fn gamma_combine_v6_queries(
    wire: &V6OneFoldWire<'_>,
    gamma: QM31,
) -> Result<[[QM31; 4]; V6_QUERY_COUNT], V6WireError> {
    let powers = StateOnlySpendQueryPowers::new(gamma);
    let mut combined = [[QM31::ZERO; 4]; V6_QUERY_COUNT];
    for (ordinal, output) in combined.iter_mut().enumerate() {
        let record = wire
            .query(ordinal)
            .ok_or(V6WireError::InvalidQuerySchedule)?;
        *output = gamma_combine_v6_packed_layer0(record.c1_packed, record.c2_packed, &powers)?;
    }
    Ok(combined)
}

/// Apply the sole circle-to-line fold to already gamma-combined values.
pub fn fold_v6_onefold_queries(
    combined: &[[QM31; 4]; V6_QUERY_COUNT],
    coordinates: &V6OneFoldCoordinates,
    alpha: QM31,
) -> [QM31; V6_QUERY_COUNT] {
    let alpha_squared = alpha.square();
    let alpha_powers = [
        PreparedQm31Multiplier::new(alpha),
        PreparedQm31Multiplier::new(alpha_squared),
        PreparedQm31Multiplier::new(alpha_squared.mul(alpha)),
    ];
    core::array::from_fn(|ordinal| {
        normalized_circle_to_line_arity4_prepared_polynomial_refs(
            &combined[ordinal],
            &alpha_powers,
            coordinates.inv_2x[ordinal],
            coordinates.inv_2y[ordinal],
        )
    })
}

/// Check the sole V6 circle-to-line fold at every authenticated query.
///
/// The caller must first run [`verify_v6_binary_openings`] over the same wire
/// and query schedule. This function then decodes the packed fibre values,
/// combines all 29 columns with scalar powers of `gamma`, derives and
/// batch-inverts the public circle coordinates, and compares the folded value
/// with the disclosed degree-<256 object at the corresponding line point.
pub fn check_v6_onefold_queries(
    wire: &V6OneFoldWire<'_>,
    queries: [u32; V6_QUERY_COUNT],
    gamma: QM31,
    alpha: QM31,
) -> Result<[QM31; V6_QUERY_COUNT], V6WireError> {
    let expected = evaluate_packed_final256_at_queries(wire.fixed_fields_packed, queries)?;
    let coordinates = prepare_v6_onefold_coordinates(queries)?;
    let combined = gamma_combine_v6_queries(wire, gamma)?;
    let folded = fold_v6_onefold_queries(&combined, &coordinates, alpha);
    for ordinal in 0..V6_QUERY_COUNT {
        if folded[ordinal] != expected[ordinal] {
            return Err(V6WireError::FriMismatch);
        }
    }
    Ok(folded)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::merkle::node_hash;
    use crate::state_only_spend_query::gamma_combine_state_only_spend_layer0_prepared;
    use alloc::vec;
    use alloc::vec::Vec;
    use sha2::{Digest, Sha256};

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

    fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        for input in inputs {
            hasher.update(input);
        }
        hasher.finalize().into()
    }

    fn minimal_binary_root(
        depth: u32,
        entries: &[(u32, [u8; 32])],
        frontier: &[[u8; 32]],
    ) -> [u8; 32] {
        let mut stream = frontier.iter();
        let mut level = entries.to_vec();
        for _ in 0..depth {
            let mut next = Vec::with_capacity(level.len());
            let mut index = 0usize;
            while index < level.len() {
                let (position, digest) = level[index];
                let parent = if position & 1 == 0
                    && index + 1 < level.len()
                    && level[index + 1].0 == position + 1
                {
                    let combined = node_hash(test_hash, &digest, &level[index + 1].1);
                    index += 2;
                    combined
                } else {
                    let sibling = stream.next().unwrap();
                    index += 1;
                    if position & 1 == 0 {
                        node_hash(test_hash, &digest, sibling)
                    } else {
                        node_hash(test_hash, sibling, &digest)
                    }
                };
                next.push((position >> 1, parent));
            }
            level = next;
        }
        assert!(stream.next().is_none());
        assert_eq!(level.len(), 1);
        level[0].1
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

    #[test]
    fn typed_shared_salt_binary_openings_match_both_roots() {
        let queries = [
            122_108, 40_038, 180_031, 111_504, 57_828, 27_366, 58_493, 6_257, 191_948, 128_942,
            244_032, 98_351, 184_446, 150_408, 7_983, 33_159,
        ];
        let frontier_nodes = binary_frontier_nodes(queries, 18).unwrap();
        assert_eq!(frontier_nodes, V6_FRONTIER_CAP_PER_TREE);
        let mut body = valid_body(frontier_nodes, frontier_nodes);

        let parsed = V6OneFoldWire::parse(&body, frontier_nodes, frontier_nodes).unwrap();
        let mut order: [(u32, usize); V6_QUERY_COUNT] =
            core::array::from_fn(|ordinal| (queries[ordinal], ordinal));
        order.sort_unstable_by_key(|entry| entry.0);
        let c1_entries: Vec<_> = order
            .iter()
            .map(|(query, ordinal)| {
                let record = parsed.query(*ordinal).unwrap();
                (
                    *query,
                    private_leaf_hash(test_hash, V6_C1_TREE_TAG, record.c1_packed, record.salt),
                )
            })
            .collect();
        let c2_entries: Vec<_> = order
            .iter()
            .map(|(query, ordinal)| {
                let record = parsed.query(*ordinal).unwrap();
                (
                    *query,
                    private_leaf_hash(test_hash, V6_C2_TREE_TAG, record.c2_packed, record.salt),
                )
            })
            .collect();
        assert_ne!(c1_entries[0].1, c2_entries[0].1);
        let zero_frontier = vec![[0u8; 32]; frontier_nodes];
        let c1_root = minimal_binary_root(18, &c1_entries, &zero_frontier);
        let c2_root = minimal_binary_root(18, &c2_entries, &zero_frontier);
        let c1_root_offset = V6_FIXED_PACKED_FIELD_BYTES;
        body[c1_root_offset..c1_root_offset + 32].copy_from_slice(&c1_root);
        body[c1_root_offset + 32..c1_root_offset + 64].copy_from_slice(&c2_root);

        let parsed = V6OneFoldWire::parse(&body, frontier_nodes, frontier_nodes).unwrap();
        assert_eq!(
            verify_v6_binary_openings(test_hash, &parsed, queries),
            Ok(())
        );

        let mut changed_value = body.clone();
        changed_value[V6_FIXED_BYTES] ^= 1;
        let parsed = V6OneFoldWire::parse(&changed_value, frontier_nodes, frontier_nodes).unwrap();
        assert_eq!(
            verify_v6_binary_openings(test_hash, &parsed, queries),
            Err(V6WireError::MerkleMismatch)
        );

        let mut changed_shared_salt = body;
        changed_shared_salt
            [V6_FIXED_BYTES + V6_C1_PACKED_BYTES_PER_QUERY + V6_C2_PACKED_BYTES_PER_QUERY] ^= 1;
        let parsed =
            V6OneFoldWire::parse(&changed_shared_salt, frontier_nodes, frontier_nodes).unwrap();
        assert_eq!(
            verify_v6_binary_openings(test_hash, &parsed, queries),
            Err(V6WireError::MerkleMismatch)
        );
    }

    #[test]
    fn packed_26_plus_3_combination_matches_unpacked_reference() {
        let gamma = QM31 {
            c0: CM31::new(M31(17), M31(23)),
            c1: CM31::new(M31(31), M31(47)),
        };
        let powers = StateOnlySpendQueryPowers::new(gamma);
        let c1_limbs: Vec<u32> = (0..V6_C1_LIMBS_PER_QUERY)
            .map(|index| ((index * 1_003 + 71) as u32) % P)
            .collect();
        let c1_packed = pack(&c1_limbs);
        let mut c1_unpacked = Vec::with_capacity(V6_C1_LIMBS_PER_QUERY * 4);
        for value in &c1_limbs {
            c1_unpacked.extend_from_slice(&value.to_le_bytes());
        }

        let c2_limbs: Vec<u32> = (0..V6_C2_LIMBS_PER_QUERY)
            .map(|index| ((index * 2_009 + 113) as u32) % P)
            .collect();
        let c2_packed = pack(&c2_limbs);
        let mut c2_unpacked = Vec::with_capacity(V6_C2_LIMBS_PER_QUERY * 4);
        for value in &c2_limbs {
            c2_unpacked.extend_from_slice(&value.to_le_bytes());
        }

        assert_eq!(
            gamma_combine_v6_packed_layer0(&c1_packed, &c2_packed, &powers).unwrap(),
            gamma_combine_state_only_spend_layer0_prepared(&c1_unpacked, &c2_unpacked, &powers)
                .unwrap()
        );
    }

    #[test]
    fn onefold_queries_connect_opened_fibres_to_explicit_final_vector() {
        let queries = [
            122_108, 40_038, 180_031, 111_504, 57_828, 27_366, 58_493, 6_257, 191_948, 128_942,
            244_032, 98_351, 184_446, 150_408, 7_983, 33_159,
        ];
        let frontier = binary_frontier_nodes(queries, 18).unwrap();
        let body = valid_body(frontier, frontier);
        let parsed = V6OneFoldWire::parse(&body, frontier, frontier).unwrap();
        let gamma = QM31 {
            c0: CM31::new(M31(17), M31(23)),
            c1: CM31::new(M31(31), M31(47)),
        };
        let alpha = QM31 {
            c0: CM31::new(M31(53), M31(59)),
            c1: CM31::new(M31(61), M31(67)),
        };
        assert_eq!(
            check_v6_onefold_queries(&parsed, queries, gamma, alpha).unwrap(),
            [QM31::ZERO; V6_QUERY_COUNT]
        );

        let mut changed_opening = body;
        changed_opening[V6_FIXED_BYTES] = 1;
        let parsed = V6OneFoldWire::parse(&changed_opening, frontier, frontier).unwrap();
        assert_eq!(
            check_v6_onefold_queries(&parsed, queries, gamma, alpha),
            Err(V6WireError::FriMismatch)
        );
    }
}
