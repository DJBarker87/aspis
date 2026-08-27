//! Production-inactive fixed-field codec experiments for Tag-73.
//!
//! The selected proof stores all 641 QM31 values as one continuous 31-bit
//! limb stream. These three experimental grammars independently replace the
//! 385-value pre-final segment, the 256-value final vector, or both with
//! canonical 16-byte QM31 records. Roots, work nonces, q16 records and both
//! authentication frontiers remain byte-for-byte unchanged.
//!
//! This module is compiled only by `v7-fixed-codec-experiment`. It does not
//! expose an accepted verifier route or a production profile binding.

use alloc::vec::Vec;

use crate::field::{CM31, M31, P, QM31};
use crate::v6_onefold::{
    packed_qm31_at, validate_packed_m31, V6FixedFieldReader, V6WireError, V6_C1_LIMBS_PER_QUERY,
    V6_C1_PACKED_BYTES_PER_QUERY, V6_C2_LIMBS_PER_QUERY, V6_C2_PACKED_BYTES_PER_QUERY,
    V6_FINAL_QM31_OFFSET, V6_FINAL_QM31_VALUES, V6_FIXED_M31_LIMBS, V6_FIXED_PACKED_FIELD_BYTES,
    V6_QUERY_COUNT, V6_WORK_NONCE_BYTES,
};
use crate::v7_onefold::{
    V7CompactOneFoldWire, V7_COMPACT_DIGEST_BYTES, V7_COMPACT_FRONTIER_CAP_PER_TREE,
    V7_COMPACT_PRIVATE_SALT_BYTES, V7_COMPACT_PRODUCTION_LIMIT_BYTES, V7_COMPACT_QUERY_BYTES,
    V7_COMPACT_QUERY_SECTION_BYTES,
};

pub const V7_FIXED_CODEC_PRE_FINAL_QM31: usize = V6_FINAL_QM31_OFFSET;
pub const V7_FIXED_CODEC_FINAL_QM31: usize = V6_FINAL_QM31_VALUES;
pub const V7_FIXED_CODEC_TOTAL_QM31: usize =
    V7_FIXED_CODEC_PRE_FINAL_QM31 + V7_FIXED_CODEC_FINAL_QM31;

const fn packed_bytes_for_qm31(values: usize) -> usize {
    (values * 4 * 31 + 7) / 8
}

pub const V7_FIXED_CODEC_PACKED_PRE_FINAL_BYTES: usize =
    packed_bytes_for_qm31(V7_FIXED_CODEC_PRE_FINAL_QM31);
pub const V7_FIXED_CODEC_PACKED_FINAL256_BYTES: usize =
    packed_bytes_for_qm31(V7_FIXED_CODEC_FINAL_QM31);
pub const V7_FIXED_CODEC_CANONICAL_PRE_FINAL_BYTES: usize = 16 * V7_FIXED_CODEC_PRE_FINAL_QM31;
pub const V7_FIXED_CODEC_CANONICAL_FINAL256_BYTES: usize = 16 * V7_FIXED_CODEC_FINAL_QM31;

pub const V7_FIXED_CODEC_PRE_CANONICAL_BYTES: usize =
    V7_FIXED_CODEC_CANONICAL_PRE_FINAL_BYTES + V7_FIXED_CODEC_PACKED_FINAL256_BYTES;
pub const V7_FIXED_CODEC_FINAL_CANONICAL_BYTES: usize =
    V7_FIXED_CODEC_PACKED_PRE_FINAL_BYTES + V7_FIXED_CODEC_CANONICAL_FINAL256_BYTES;
pub const V7_FIXED_CODEC_BOTH_CANONICAL_BYTES: usize =
    V7_FIXED_CODEC_CANONICAL_PRE_FINAL_BYTES + V7_FIXED_CODEC_CANONICAL_FINAL256_BYTES;

pub const V7_FIXED_CODEC_PRE_CANONICAL_DELTA: usize =
    V7_FIXED_CODEC_PRE_CANONICAL_BYTES - V6_FIXED_PACKED_FIELD_BYTES;
pub const V7_FIXED_CODEC_FINAL_CANONICAL_DELTA: usize =
    V7_FIXED_CODEC_FINAL_CANONICAL_BYTES - V6_FIXED_PACKED_FIELD_BYTES;
pub const V7_FIXED_CODEC_BOTH_CANONICAL_DELTA: usize =
    V7_FIXED_CODEC_BOTH_CANONICAL_BYTES - V6_FIXED_PACKED_FIELD_BYTES;

const V7_FIXED_CODEC_UNCHANGED_BODY_BYTES: usize =
    2 * V7_COMPACT_DIGEST_BYTES + V6_WORK_NONCE_BYTES + V7_COMPACT_QUERY_SECTION_BYTES;
const V7_FIXED_CODEC_MAX_FRONTIER_BYTES: usize =
    2 * V7_COMPACT_FRONTIER_CAP_PER_TREE * V7_COMPACT_DIGEST_BYTES;

pub const V7_FIXED_CODEC_PRE_CANONICAL_MAX_BODY_BYTES: usize = V7_FIXED_CODEC_PRE_CANONICAL_BYTES
    + V7_FIXED_CODEC_UNCHANGED_BODY_BYTES
    + V7_FIXED_CODEC_MAX_FRONTIER_BYTES;
pub const V7_FIXED_CODEC_FINAL_CANONICAL_MAX_BODY_BYTES: usize =
    V7_FIXED_CODEC_FINAL_CANONICAL_BYTES
        + V7_FIXED_CODEC_UNCHANGED_BODY_BYTES
        + V7_FIXED_CODEC_MAX_FRONTIER_BYTES;
pub const V7_FIXED_CODEC_BOTH_CANONICAL_MAX_BODY_BYTES: usize = V7_FIXED_CODEC_BOTH_CANONICAL_BYTES
    + V7_FIXED_CODEC_UNCHANGED_BODY_BYTES
    + V7_FIXED_CODEC_MAX_FRONTIER_BYTES;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum V7FixedCodecVariant {
    CanonicalPreFinal,
    CanonicalFinal256,
    CanonicalBoth,
}

impl V7FixedCodecVariant {
    pub const fn fixed_bytes(self) -> usize {
        match self {
            Self::CanonicalPreFinal => V7_FIXED_CODEC_PRE_CANONICAL_BYTES,
            Self::CanonicalFinal256 => V7_FIXED_CODEC_FINAL_CANONICAL_BYTES,
            Self::CanonicalBoth => V7_FIXED_CODEC_BOTH_CANONICAL_BYTES,
        }
    }

    pub const fn maximum_body_bytes(self) -> usize {
        match self {
            Self::CanonicalPreFinal => V7_FIXED_CODEC_PRE_CANONICAL_MAX_BODY_BYTES,
            Self::CanonicalFinal256 => V7_FIXED_CODEC_FINAL_CANONICAL_MAX_BODY_BYTES,
            Self::CanonicalBoth => V7_FIXED_CODEC_BOTH_CANONICAL_MAX_BODY_BYTES,
        }
    }

    const fn pre_final_encoding(self) -> FixedSegmentEncoding {
        match self {
            Self::CanonicalPreFinal | Self::CanonicalBoth => FixedSegmentEncoding::Canonical,
            Self::CanonicalFinal256 => FixedSegmentEncoding::Packed,
        }
    }

    const fn final256_encoding(self) -> FixedSegmentEncoding {
        match self {
            Self::CanonicalFinal256 | Self::CanonicalBoth => FixedSegmentEncoding::Canonical,
            Self::CanonicalPreFinal => FixedSegmentEncoding::Packed,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FixedSegmentEncoding {
    Packed,
    Canonical,
}

impl FixedSegmentEncoding {
    const fn bytes(self, values: usize) -> usize {
        match self {
            Self::Packed => packed_bytes_for_qm31(values),
            Self::Canonical => 16 * values,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FixedSegment<'a> {
    encoding: FixedSegmentEncoding,
    values: usize,
    bytes: &'a [u8],
}

impl FixedSegment<'_> {
    fn validate_layout(&self) -> Result<(), V6WireError> {
        if self.bytes.len() != self.encoding.bytes(self.values) {
            return Err(V6WireError::WrongLength);
        }
        if self.encoding == FixedSegmentEncoding::Packed {
            let used_bits = self.values * 4 * 31;
            let used_last = used_bits % 8;
            if used_last != 0 {
                let unused = !((1u8 << used_last) - 1);
                if self.bytes.last().copied().unwrap_or_default() & unused != 0 {
                    return Err(V6WireError::NonCanonicalM31);
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct V7ExperimentalFixedSection<'a> {
    variant: V7FixedCodecVariant,
    pre_final: FixedSegment<'a>,
    final256: FixedSegment<'a>,
}

impl<'a> V7ExperimentalFixedSection<'a> {
    pub fn parse_deferred_canonicality(
        bytes: &'a [u8],
        variant: V7FixedCodecVariant,
    ) -> Result<Self, V6WireError> {
        if bytes.len() != variant.fixed_bytes() {
            return Err(V6WireError::WrongLength);
        }
        let pre_encoding = variant.pre_final_encoding();
        let pre_bytes = pre_encoding.bytes(V7_FIXED_CODEC_PRE_FINAL_QM31);
        let (pre_final, final256) = bytes.split_at(pre_bytes);
        let section = Self {
            variant,
            pre_final: FixedSegment {
                encoding: pre_encoding,
                values: V7_FIXED_CODEC_PRE_FINAL_QM31,
                bytes: pre_final,
            },
            final256: FixedSegment {
                encoding: variant.final256_encoding(),
                values: V7_FIXED_CODEC_FINAL_QM31,
                bytes: final256,
            },
        };
        section.pre_final.validate_layout()?;
        section.final256.validate_layout()?;
        Ok(section)
    }

    pub fn parse(bytes: &'a [u8], variant: V7FixedCodecVariant) -> Result<Self, V6WireError> {
        let section = Self::parse_deferred_canonicality(bytes, variant)?;
        let mut reader = section.reader();
        for _ in 0..V7_FIXED_CODEC_TOTAL_QM31 {
            reader.next_qm31()?;
        }
        reader.finish()?;
        Ok(section)
    }

    pub fn variant(&self) -> V7FixedCodecVariant {
        self.variant
    }

    pub fn reader(&self) -> V7ExperimentalFixedFieldReader<'a> {
        V7ExperimentalFixedFieldReader {
            pre_final: SegmentReader::new(self.pre_final),
            final256: SegmentReader::new(self.final256),
            ordinal: 0,
        }
    }

    /// Decode every value and reproduce the canonical 16-byte field image
    /// absorbed by the existing transcript code.
    pub fn canonical_field_image(&self) -> Result<Vec<u8>, V6WireError> {
        let mut output = Vec::with_capacity(16 * V7_FIXED_CODEC_TOTAL_QM31);
        let mut reader = self.reader();
        for _ in 0..V7_FIXED_CODEC_TOTAL_QM31 {
            let value = reader.next_qm31()?;
            let start = output.len();
            output.resize(start + 16, 0);
            value.write_le_bytes(&mut output[start..start + 16]);
        }
        reader.finish()?;
        Ok(output)
    }
}

#[derive(Clone, Copy)]
enum SegmentReader<'a> {
    Packed(PackedSegmentReader<'a>),
    Canonical(CanonicalSegmentReader<'a>),
}

impl<'a> SegmentReader<'a> {
    fn new(segment: FixedSegment<'a>) -> Self {
        match segment.encoding {
            FixedSegmentEncoding::Packed => {
                Self::Packed(PackedSegmentReader::new(segment.bytes, segment.values))
            }
            FixedSegmentEncoding::Canonical => Self::Canonical(CanonicalSegmentReader {
                bytes: segment.bytes,
                ordinal: 0,
                values: segment.values,
            }),
        }
    }

    fn next_qm31(&mut self) -> Result<QM31, V6WireError> {
        match self {
            Self::Packed(reader) => reader.next_qm31(),
            Self::Canonical(reader) => reader.next_qm31(),
        }
    }

    fn finish(self) -> Result<(), V6WireError> {
        match self {
            Self::Packed(reader) => reader.finish(),
            Self::Canonical(reader) => reader.finish(),
        }
    }
}

#[derive(Clone, Copy)]
struct PackedSegmentReader<'a> {
    bytes: &'a [u8],
    byte_index: usize,
    buffer: u64,
    buffered_bits: u8,
    remaining_limbs: usize,
}

impl<'a> PackedSegmentReader<'a> {
    fn new(bytes: &'a [u8], values: usize) -> Self {
        Self {
            bytes,
            byte_index: 0,
            buffer: 0,
            buffered_bits: 0,
            remaining_limbs: 4 * values,
        }
    }

    fn next_limb(&mut self) -> Result<M31, V6WireError> {
        if self.remaining_limbs == 0 {
            return Err(V6WireError::WrongLength);
        }
        while self.buffered_bits < 31 {
            let byte = self
                .bytes
                .get(self.byte_index)
                .copied()
                .ok_or(V6WireError::WrongLength)?;
            self.buffer |= u64::from(byte) << self.buffered_bits;
            self.byte_index += 1;
            self.buffered_bits += 8;
        }
        let value = (self.buffer & 0x7fff_ffff) as u32;
        self.buffer >>= 31;
        self.buffered_bits -= 31;
        self.remaining_limbs -= 1;
        if value >= P {
            return Err(V6WireError::NonCanonicalM31);
        }
        Ok(M31(value))
    }

    fn next_qm31(&mut self) -> Result<QM31, V6WireError> {
        Ok(QM31 {
            c0: CM31::new(self.next_limb()?, self.next_limb()?),
            c1: CM31::new(self.next_limb()?, self.next_limb()?),
        })
    }

    fn finish(self) -> Result<(), V6WireError> {
        if self.remaining_limbs == 0 {
            Ok(())
        } else {
            Err(V6WireError::WrongLength)
        }
    }
}

#[derive(Clone, Copy)]
struct CanonicalSegmentReader<'a> {
    bytes: &'a [u8],
    ordinal: usize,
    values: usize,
}

impl CanonicalSegmentReader<'_> {
    fn next_qm31(&mut self) -> Result<QM31, V6WireError> {
        if self.ordinal >= self.values {
            return Err(V6WireError::WrongLength);
        }
        let start = 16 * self.ordinal;
        let value = QM31::from_le_bytes(&self.bytes[start..start + 16])
            .ok_or(V6WireError::NonCanonicalM31)?;
        self.ordinal += 1;
        Ok(value)
    }

    fn finish(self) -> Result<(), V6WireError> {
        if self.ordinal == self.values {
            Ok(())
        } else {
            Err(V6WireError::WrongLength)
        }
    }
}

pub struct V7ExperimentalFixedFieldReader<'a> {
    pre_final: SegmentReader<'a>,
    final256: SegmentReader<'a>,
    ordinal: usize,
}

impl V7ExperimentalFixedFieldReader<'_> {
    pub fn next_qm31(&mut self) -> Result<QM31, V6WireError> {
        if self.ordinal >= V7_FIXED_CODEC_TOTAL_QM31 {
            return Err(V6WireError::WrongLength);
        }
        let value = if self.ordinal < V7_FIXED_CODEC_PRE_FINAL_QM31 {
            self.pre_final.next_qm31()?
        } else {
            self.final256.next_qm31()?
        };
        self.ordinal += 1;
        Ok(value)
    }

    pub fn finish(self) -> Result<(), V6WireError> {
        if self.ordinal != V7_FIXED_CODEC_TOTAL_QM31 {
            return Err(V6WireError::WrongLength);
        }
        self.pre_final.finish()?;
        self.final256.finish()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct V7ExperimentalQueryRecord<'a> {
    pub c1_packed: &'a [u8],
    pub c2_packed: &'a [u8],
    pub salt: &'a [u8; V7_COMPACT_PRIVATE_SALT_BYTES],
}

/// Exact full-proof framing for one inactive fixed-codec variant.
///
/// Only the fixed section differs from Tag-73. Every tail field is parsed and
/// canonically checked with the same widths as the selected wire.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct V7ExperimentalFixedCodecWire<'a> {
    pub fixed: V7ExperimentalFixedSection<'a>,
    pub c1_root: &'a [u8; V7_COMPACT_DIGEST_BYTES],
    pub c2_root: &'a [u8; V7_COMPACT_DIGEST_BYTES],
    pub work_nonces: &'a [u8; V6_WORK_NONCE_BYTES],
    query_section: &'a [u8],
    pub c1_frontier: &'a [u8],
    pub c2_frontier: &'a [u8],
}

impl<'a> V7ExperimentalFixedCodecWire<'a> {
    pub fn parse(
        bytes: &'a [u8],
        frontier_nodes: usize,
        variant: V7FixedCodecVariant,
    ) -> Result<Self, V6WireError> {
        if frontier_nodes > V7_COMPACT_FRONTIER_CAP_PER_TREE {
            return Err(V6WireError::FrontierTooLarge);
        }
        let frontier_bytes = frontier_nodes
            .checked_mul(V7_COMPACT_DIGEST_BYTES)
            .ok_or(V6WireError::WrongLength)?;
        let expected = variant
            .fixed_bytes()
            .checked_add(V7_FIXED_CODEC_UNCHANGED_BODY_BYTES)
            .and_then(|value| value.checked_add(2 * frontier_bytes))
            .ok_or(V6WireError::WrongLength)?;
        if bytes.len() != expected || bytes.len() > V7_COMPACT_PRODUCTION_LIMIT_BYTES + 320 {
            return Err(V6WireError::WrongLength);
        }

        let (fixed_bytes, rest) = bytes.split_at(variant.fixed_bytes());
        let fixed = V7ExperimentalFixedSection::parse(fixed_bytes, variant)?;
        let (c1_root, rest) = rest.split_at(V7_COMPACT_DIGEST_BYTES);
        let (c2_root, rest) = rest.split_at(V7_COMPACT_DIGEST_BYTES);
        let (work_nonces, rest) = rest.split_at(V6_WORK_NONCE_BYTES);
        let (query_section, rest) = rest.split_at(V7_COMPACT_QUERY_SECTION_BYTES);
        let (c1_frontier, c2_frontier) = rest.split_at(frontier_bytes);
        for ordinal in 0..V6_QUERY_COUNT {
            let start = ordinal * V7_COMPACT_QUERY_BYTES;
            let c1_end = start + V6_C1_PACKED_BYTES_PER_QUERY;
            let c2_end = c1_end + V6_C2_PACKED_BYTES_PER_QUERY;
            validate_packed_m31(&query_section[start..c1_end], V6_C1_LIMBS_PER_QUERY)?;
            validate_packed_m31(&query_section[c1_end..c2_end], V6_C2_LIMBS_PER_QUERY)?;
        }
        Ok(Self {
            fixed,
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

    pub fn query(&self, ordinal: usize) -> Option<V7ExperimentalQueryRecord<'a>> {
        if ordinal >= V6_QUERY_COUNT {
            return None;
        }
        let start = ordinal * V7_COMPACT_QUERY_BYTES;
        let c1_end = start + V6_C1_PACKED_BYTES_PER_QUERY;
        let c2_end = c1_end + V6_C2_PACKED_BYTES_PER_QUERY;
        let end = c2_end + V7_COMPACT_PRIVATE_SALT_BYTES;
        Some(V7ExperimentalQueryRecord {
            c1_packed: &self.query_section[start..c1_end],
            c2_packed: &self.query_section[c1_end..c2_end],
            salt: self.query_section[c2_end..end].try_into().ok()?,
        })
    }
}

/// Re-encode the selected packed fixed section under one experimental grammar.
pub fn transcode_fixed_section_from_tag73(
    packed: &[u8],
    variant: V7FixedCodecVariant,
) -> Result<Vec<u8>, V6WireError> {
    validate_packed_m31(packed, V6_FIXED_M31_LIMBS)?;
    let mut fields = Vec::with_capacity(V7_FIXED_CODEC_TOTAL_QM31);
    for ordinal in 0..V7_FIXED_CODEC_TOTAL_QM31 {
        fields.push(packed_qm31_at(packed, ordinal).ok_or(V6WireError::WrongLength)?);
    }

    let mut output = Vec::with_capacity(variant.fixed_bytes());
    encode_segment(
        &mut output,
        &fields[..V7_FIXED_CODEC_PRE_FINAL_QM31],
        variant.pre_final_encoding(),
    );
    encode_segment(
        &mut output,
        &fields[V7_FIXED_CODEC_PRE_FINAL_QM31..],
        variant.final256_encoding(),
    );
    debug_assert_eq!(output.len(), variant.fixed_bytes());
    Ok(output)
}

/// Transcode an exact selected Tag-73 proof while preserving its complete tail.
pub fn transcode_tag73_proof_fixed_section(
    proof: &[u8],
    frontier_nodes: usize,
    variant: V7FixedCodecVariant,
) -> Result<Vec<u8>, V6WireError> {
    V7CompactOneFoldWire::parse(proof, frontier_nodes)?;
    let fixed = transcode_fixed_section_from_tag73(&proof[..V6_FIXED_PACKED_FIELD_BYTES], variant)?;
    let mut output =
        Vec::with_capacity(proof.len() + variant.fixed_bytes() - V6_FIXED_PACKED_FIELD_BYTES);
    output.extend_from_slice(&fixed);
    output.extend_from_slice(&proof[V6_FIXED_PACKED_FIELD_BYTES..]);
    V7ExperimentalFixedCodecWire::parse(&output, frontier_nodes, variant)?;
    Ok(output)
}

/// Decode all 641 values with the selected streaming packed reader and return
/// an observable algebraic checksum. This is a component-measurement kernel,
/// not a verifier or transcript replacement.
pub fn selected_packed_fixed_section_checksum(packed: &[u8]) -> Result<QM31, V6WireError> {
    let mut reader = V6FixedFieldReader::new(packed)?;
    let mut checksum = QM31::ZERO;
    for _ in 0..V7_FIXED_CODEC_TOTAL_QM31 {
        checksum = checksum.add(reader.next_qm31()?);
    }
    reader.finish()?;
    Ok(checksum)
}

/// Decode all 641 values under one inactive grammar and return the same
/// observable algebraic checksum as `selected_packed_fixed_section_checksum`.
pub fn experimental_fixed_section_checksum(
    bytes: &[u8],
    variant: V7FixedCodecVariant,
) -> Result<QM31, V6WireError> {
    let section = V7ExperimentalFixedSection::parse_deferred_canonicality(bytes, variant)?;
    let mut reader = section.reader();
    let mut checksum = QM31::ZERO;
    for _ in 0..V7_FIXED_CODEC_TOTAL_QM31 {
        checksum = checksum.add(reader.next_qm31()?);
    }
    reader.finish()?;
    Ok(checksum)
}

fn encode_segment(output: &mut Vec<u8>, fields: &[QM31], encoding: FixedSegmentEncoding) {
    match encoding {
        FixedSegmentEncoding::Canonical => {
            for value in fields {
                let start = output.len();
                output.resize(start + 16, 0);
                value.write_le_bytes(&mut output[start..start + 16]);
            }
        }
        FixedSegmentEncoding::Packed => {
            let start = output.len();
            output.resize(start + packed_bytes_for_qm31(fields.len()), 0);
            let packed = &mut output[start..];
            for (field, value) in fields.iter().enumerate() {
                for (limb, word) in [value.c0.a.0, value.c0.b.0, value.c1.a.0, value.c1.b.0]
                    .into_iter()
                    .enumerate()
                {
                    let bit_start = (4 * field + limb) * 31;
                    for bit in 0..31 {
                        packed[(bit_start + bit) / 8] |=
                            (((word >> bit) & 1) as u8) << ((bit_start + bit) % 8);
                    }
                }
            }
        }
    }
}

const _: () = assert!(V7_FIXED_CODEC_PRE_FINAL_QM31 == 385);
const _: () = assert!(V7_FIXED_CODEC_FINAL_QM31 == 256);
const _: () = assert!(V7_FIXED_CODEC_TOTAL_QM31 == 641);
const _: () = assert!(V7_FIXED_CODEC_PACKED_PRE_FINAL_BYTES == 5_968);
const _: () = assert!(V7_FIXED_CODEC_PACKED_FINAL256_BYTES == 3_968);
const _: () = assert!(V7_FIXED_CODEC_PRE_CANONICAL_BYTES == 10_128);
const _: () = assert!(V7_FIXED_CODEC_FINAL_CANONICAL_BYTES == 10_064);
const _: () = assert!(V7_FIXED_CODEC_BOTH_CANONICAL_BYTES == 10_256);
const _: () = assert!(V7_FIXED_CODEC_PRE_CANONICAL_DELTA == 192);
const _: () = assert!(V7_FIXED_CODEC_FINAL_CANONICAL_DELTA == 128);
const _: () = assert!(V7_FIXED_CODEC_BOTH_CANONICAL_DELTA == 320);
const _: () = assert!(V7_FIXED_CODEC_PRE_CANONICAL_MAX_BODY_BYTES == 30_696);
const _: () = assert!(V7_FIXED_CODEC_FINAL_CANONICAL_MAX_BODY_BYTES == 30_632);
const _: () = assert!(V7_FIXED_CODEC_BOTH_CANONICAL_MAX_BODY_BYTES == 30_824);

#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;
    use std::hint::black_box;
    use std::time::Instant;

    fn fields() -> Vec<QM31> {
        (0..V7_FIXED_CODEC_TOTAL_QM31)
            .map(|ordinal| {
                let base = (ordinal as u32).wrapping_mul(1_000_003) % P;
                QM31 {
                    c0: CM31::new(M31(base), M31((base + 1) % P)),
                    c1: CM31::new(M31((base + 2) % P), M31((base + 3) % P)),
                }
            })
            .collect()
    }

    fn packed_tag73(fields: &[QM31]) -> Vec<u8> {
        let mut output = Vec::new();
        encode_segment(&mut output, fields, FixedSegmentEncoding::Packed);
        output
    }

    fn canonical(fields: &[QM31]) -> Vec<u8> {
        let mut output = Vec::new();
        encode_segment(&mut output, fields, FixedSegmentEncoding::Canonical);
        output
    }

    #[test]
    fn exact_variant_byte_arithmetic_is_frozen() {
        assert_eq!(V6_FIXED_PACKED_FIELD_BYTES, 9_936);
        assert_eq!(V7_FIXED_CODEC_PRE_CANONICAL_DELTA, 192);
        assert_eq!(V7_FIXED_CODEC_FINAL_CANONICAL_DELTA, 128);
        assert_eq!(V7_FIXED_CODEC_BOTH_CANONICAL_DELTA, 320);
        assert_eq!(V7_FIXED_CODEC_PRE_CANONICAL_MAX_BODY_BYTES, 30_696);
        assert_eq!(V7_FIXED_CODEC_FINAL_CANONICAL_MAX_BODY_BYTES, 30_632);
        assert_eq!(V7_FIXED_CODEC_BOTH_CANONICAL_MAX_BODY_BYTES, 30_824);
    }

    #[test]
    fn every_variant_decodes_to_identical_fields_and_canonical_transcript_bytes() {
        let fields = fields();
        let packed = packed_tag73(&fields);
        let expected_canonical = canonical(&fields);
        assert_eq!(packed.len(), V6_FIXED_PACKED_FIELD_BYTES);

        for variant in [
            V7FixedCodecVariant::CanonicalPreFinal,
            V7FixedCodecVariant::CanonicalFinal256,
            V7FixedCodecVariant::CanonicalBoth,
        ] {
            let encoded = transcode_fixed_section_from_tag73(&packed, variant).unwrap();
            let section = V7ExperimentalFixedSection::parse(&encoded, variant).unwrap();
            assert_eq!(section.variant(), variant);
            assert_eq!(section.canonical_field_image().unwrap(), expected_canonical);
            let mut reader = section.reader();
            for expected in &fields {
                assert_eq!(reader.next_qm31().unwrap(), *expected);
            }
            assert_eq!(reader.finish(), Ok(()));
        }
    }

    #[test]
    fn canonical_and_packed_malleability_is_rejected_fail_closed() {
        let fields = fields();
        let packed = packed_tag73(&fields);
        for variant in [
            V7FixedCodecVariant::CanonicalPreFinal,
            V7FixedCodecVariant::CanonicalFinal256,
            V7FixedCodecVariant::CanonicalBoth,
        ] {
            let encoded = transcode_fixed_section_from_tag73(&packed, variant).unwrap();
            assert_eq!(
                V7ExperimentalFixedSection::parse(&encoded[..encoded.len() - 1], variant),
                Err(V6WireError::WrongLength)
            );
            let mut trailing = encoded.clone();
            trailing.push(0);
            assert_eq!(
                V7ExperimentalFixedSection::parse(&trailing, variant),
                Err(V6WireError::WrongLength)
            );

            let mut malformed = encoded.clone();
            let canonical_offset =
                if variant.pre_final_encoding() == FixedSegmentEncoding::Canonical {
                    0
                } else {
                    V7_FIXED_CODEC_PACKED_PRE_FINAL_BYTES
                };
            malformed[canonical_offset..canonical_offset + 4].copy_from_slice(&P.to_le_bytes());
            assert_eq!(
                V7ExperimentalFixedSection::parse(&malformed, variant),
                Err(V6WireError::NonCanonicalM31)
            );

            if variant.pre_final_encoding() == FixedSegmentEncoding::Packed {
                let mut nonzero_padding = encoded.clone();
                nonzero_padding[V7_FIXED_CODEC_PACKED_PRE_FINAL_BYTES - 1] |= 0xf0;
                assert_eq!(
                    V7ExperimentalFixedSection::parse(&nonzero_padding, variant),
                    Err(V6WireError::NonCanonicalM31)
                );
            }
        }
    }

    #[test]
    fn reader_requires_exact_complete_consumption() {
        let fields = fields();
        let packed = packed_tag73(&fields);
        let encoded =
            transcode_fixed_section_from_tag73(&packed, V7FixedCodecVariant::CanonicalBoth)
                .unwrap();
        let section = V7ExperimentalFixedSection::parse_deferred_canonicality(
            &encoded,
            V7FixedCodecVariant::CanonicalBoth,
        )
        .unwrap();
        let reader = section.reader();
        assert_eq!(reader.finish(), Err(V6WireError::WrongLength));
        let mut reader = section.reader();
        for _ in 0..V7_FIXED_CODEC_TOTAL_QM31 {
            reader.next_qm31().unwrap();
        }
        assert_eq!(reader.next_qm31(), Err(V6WireError::WrongLength));
        assert_eq!(reader.finish(), Ok(()));
    }

    /// Run explicitly with `--ignored --nocapture --release`; host timings are
    /// comparative codec-component data, never Solana CU evidence.
    #[test]
    #[ignore]
    fn host_fixed_codec_component_benchmark() {
        const ITERATIONS: usize = 20_000;
        let fields = fields();
        let packed = packed_tag73(&fields);
        let started = Instant::now();
        let mut sink = 0u32;
        for _ in 0..ITERATIONS {
            let mut reader = crate::v6_onefold::V6FixedFieldReader::new(&packed).unwrap();
            for _ in 0..V7_FIXED_CODEC_TOTAL_QM31 {
                let value = black_box(reader.next_qm31().unwrap());
                sink ^= value.c0.a.0;
            }
            reader.finish().unwrap();
        }
        let elapsed = started.elapsed();
        std::println!(
            "variant=SelectedPacked iterations={ITERATIONS} elapsed_ns={} ns_per_decode={} sink={sink}",
            elapsed.as_nanos(),
            elapsed.as_nanos() / ITERATIONS as u128,
        );
        for variant in [
            V7FixedCodecVariant::CanonicalPreFinal,
            V7FixedCodecVariant::CanonicalFinal256,
            V7FixedCodecVariant::CanonicalBoth,
        ] {
            let encoded = transcode_fixed_section_from_tag73(&packed, variant).unwrap();
            let section =
                V7ExperimentalFixedSection::parse_deferred_canonicality(&encoded, variant).unwrap();
            let started = Instant::now();
            let mut sink = 0u32;
            for _ in 0..ITERATIONS {
                let mut reader = section.reader();
                for _ in 0..V7_FIXED_CODEC_TOTAL_QM31 {
                    let value = black_box(reader.next_qm31().unwrap());
                    sink ^= value.c0.a.0;
                }
                reader.finish().unwrap();
            }
            let elapsed = started.elapsed();
            std::println!(
                "variant={variant:?} iterations={ITERATIONS} elapsed_ns={} ns_per_decode={} sink={sink}",
                elapsed.as_nanos(),
                elapsed.as_nanos() / ITERATIONS as u128,
            );
        }
    }
}
