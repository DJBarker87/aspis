//! Additive shape layer for fixed-log-10 circle PCS profiles.
//!
//! Frozen V4 wrappers retain their existing constants and byte grammars.
//! This module only describes the shared four-slot, four-round substrate so
//! later profiles can select different C1/C2 widths and Merkle tags without
//! reusing a V4 domain accidentally.

use alloc::vec::Vec;

use crate::circle_line_merkle::CircleOpeningGeometry;
use crate::field::{M31, QM31};

pub const CIRCLE_PCS_SHAPE_VERSION: u8 = 1;
pub const CIRCLE_PCS_SHAPE_BYTES: usize = 24;
pub const CIRCLE_PCS_TRACE_LOG_SIZE: u8 = 10;
pub const CIRCLE_PCS_FIBER_SLOTS: usize = 4;
pub const CIRCLE_PCS_ARITY4_ROUNDS: u8 = 4;
pub const CIRCLE_PCS_LATER_LAYERS: usize = 3;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CirclePcsShape {
    pub trace_log_size: u8,
    pub domain_log_size: u8,
    pub query_count: u16,
    pub opening_points: u8,
    pub c1_columns: u16,
    pub c2_columns: u16,
    pub c1_layer0_tag: u8,
    pub c2_layer0_tag: u8,
    pub later_layer_tags: [u8; CIRCLE_PCS_LATER_LAYERS],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CirclePcsShapeError {
    UnsupportedTraceLog { actual: u8 },
    DomainTooSmall { trace_log: u8, domain_log: u8 },
    DomainTooLarge { actual: u8 },
    EmptyQueries,
    TooManyQueries { count: u16, fibers: usize },
    EmptyOpeningPoints,
    EmptyC1,
    EmptyC2,
    WidthOverflow,
    DuplicateTreeTag { tag: u8 },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CirclePcsDecodeError {
    Shape(CirclePcsShapeError),
    EvaluationLength { expected: usize, actual: usize },
    C1LeafLength { expected: usize, actual: usize },
    C2LeafLength { expected: usize, actual: usize },
    NonCanonicalEvaluation { index: usize },
    NonCanonicalC1 { offset: usize },
    NonCanonicalC2 { offset: usize },
}

impl From<CirclePcsShapeError> for CirclePcsDecodeError {
    fn from(error: CirclePcsShapeError) -> Self {
        Self::Shape(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CirclePcsPreparedClaims {
    pub claims: Vec<QM31>,
    pub powers: Vec<QM31>,
}

impl CirclePcsShape {
    pub fn validate(self) -> Result<Self, CirclePcsShapeError> {
        if self.trace_log_size != CIRCLE_PCS_TRACE_LOG_SIZE {
            return Err(CirclePcsShapeError::UnsupportedTraceLog {
                actual: self.trace_log_size,
            });
        }
        if self.domain_log_size < self.trace_log_size + 2 {
            return Err(CirclePcsShapeError::DomainTooSmall {
                trace_log: self.trace_log_size,
                domain_log: self.domain_log_size,
            });
        }
        if self.domain_log_size > 30 {
            return Err(CirclePcsShapeError::DomainTooLarge {
                actual: self.domain_log_size,
            });
        }
        if self.query_count == 0 {
            return Err(CirclePcsShapeError::EmptyQueries);
        }
        let fibers = self.fiber_count();
        if usize::from(self.query_count) > fibers {
            return Err(CirclePcsShapeError::TooManyQueries {
                count: self.query_count,
                fibers,
            });
        }
        if self.opening_points == 0 {
            return Err(CirclePcsShapeError::EmptyOpeningPoints);
        }
        if self.c1_columns == 0 {
            return Err(CirclePcsShapeError::EmptyC1);
        }
        if self.c2_columns == 0 {
            return Err(CirclePcsShapeError::EmptyC2);
        }
        self.c1_leaf_bytes_checked()?;
        self.c2_leaf_bytes_checked()?;

        let tags = [
            self.c1_layer0_tag,
            self.c2_layer0_tag,
            self.later_layer_tags[0],
            self.later_layer_tags[1],
            self.later_layer_tags[2],
        ];
        for (index, tag) in tags.iter().copied().enumerate() {
            if tags[..index].contains(&tag) {
                return Err(CirclePcsShapeError::DuplicateTreeTag { tag });
            }
        }
        Ok(self)
    }

    pub const fn message_len(self) -> usize {
        1usize << self.trace_log_size
    }

    pub const fn codeword_len(self) -> usize {
        1usize << self.domain_log_size
    }

    pub const fn fiber_count(self) -> usize {
        1usize << (self.domain_log_size - 2)
    }

    pub const fn total_columns(self) -> usize {
        self.c1_columns as usize + self.c2_columns as usize
    }

    pub const fn opening_count(self) -> usize {
        self.total_columns() * self.opening_points as usize
    }

    pub const fn evaluation_bytes(self) -> usize {
        self.opening_count() * 16
    }

    pub fn c1_leaf_bytes_checked(self) -> Result<usize, CirclePcsShapeError> {
        usize::from(self.c1_columns)
            .checked_mul(CIRCLE_PCS_FIBER_SLOTS * 4)
            .ok_or(CirclePcsShapeError::WidthOverflow)
    }

    pub fn c2_leaf_bytes_checked(self) -> Result<usize, CirclePcsShapeError> {
        usize::from(self.c2_columns)
            .checked_mul(CIRCLE_PCS_FIBER_SLOTS * 16)
            .ok_or(CirclePcsShapeError::WidthOverflow)
    }

    pub fn opening_geometry(self) -> Result<CircleOpeningGeometry, CirclePcsShapeError> {
        self.validate()?;
        let layer0_binary_depth = u32::from(self.domain_log_size - 2);
        Ok(CircleOpeningGeometry {
            layer0_binary_depth,
            later_binary_depths: [
                layer0_binary_depth - 2,
                layer0_binary_depth - 4,
                layer0_binary_depth - 6,
            ],
        })
    }

    pub fn encode(self) -> Result<[u8; CIRCLE_PCS_SHAPE_BYTES], CirclePcsShapeError> {
        self.validate()?;
        let c1_leaf_bytes: u16 = self
            .c1_leaf_bytes_checked()?
            .try_into()
            .map_err(|_| CirclePcsShapeError::WidthOverflow)?;
        let c2_leaf_bytes: u16 = self
            .c2_leaf_bytes_checked()?
            .try_into()
            .map_err(|_| CirclePcsShapeError::WidthOverflow)?;
        let mut bytes = [0u8; CIRCLE_PCS_SHAPE_BYTES];
        bytes[0] = CIRCLE_PCS_SHAPE_VERSION;
        bytes[1] = self.trace_log_size;
        bytes[2] = self.domain_log_size;
        bytes[3] = CIRCLE_PCS_ARITY4_ROUNDS;
        bytes[4..6].copy_from_slice(&self.query_count.to_le_bytes());
        bytes[6] = self.opening_points;
        bytes[7] = CIRCLE_PCS_FIBER_SLOTS as u8;
        bytes[8..10].copy_from_slice(&self.c1_columns.to_le_bytes());
        bytes[10..12].copy_from_slice(&self.c2_columns.to_le_bytes());
        bytes[12..14].copy_from_slice(&c1_leaf_bytes.to_le_bytes());
        bytes[14..16].copy_from_slice(&c2_leaf_bytes.to_le_bytes());
        bytes[16] = self.c1_layer0_tag;
        bytes[17] = self.c2_layer0_tag;
        bytes[18..21].copy_from_slice(&self.later_layer_tags);
        Ok(bytes)
    }
}

/// Extraction-only root for checking the exact successful return value of
/// `CirclePcsShape::validate`. The production build does not enable this
/// feature, so this wrapper is absent from the deployed program.
#[cfg(feature = "formal-verification")]
pub fn formal_validate_shape(input: CirclePcsShape) -> Result<CirclePcsShape, CirclePcsShapeError> {
    input.validate()
}

pub fn prepare_circle_pcs_claims(
    shape: CirclePcsShape,
    gamma: QM31,
    evaluation_bytes: &[u8],
) -> Result<CirclePcsPreparedClaims, CirclePcsDecodeError> {
    let shape = shape.validate()?;
    let expected = shape.evaluation_bytes();
    if evaluation_bytes.len() != expected {
        return Err(CirclePcsDecodeError::EvaluationLength {
            expected,
            actual: evaluation_bytes.len(),
        });
    }
    let mut powers = Vec::with_capacity(shape.total_columns());
    let mut power = QM31::ONE;
    for column in 0..shape.total_columns() {
        powers.push(power);
        if column + 1 != shape.total_columns() {
            power = power.mul(gamma);
        }
    }
    let mut claims = Vec::with_capacity(usize::from(shape.opening_points));
    for point in 0..usize::from(shape.opening_points) {
        let mut claim = QM31::ZERO;
        for (column, power) in powers.iter().copied().enumerate() {
            let index = point * shape.total_columns() + column;
            let offset = index * 16;
            let value = QM31::from_le_bytes(&evaluation_bytes[offset..offset + 16])
                .ok_or(CirclePcsDecodeError::NonCanonicalEvaluation { index })?;
            claim = claim.add(power.mul(value));
        }
        claims.push(claim);
    }
    Ok(CirclePcsPreparedClaims { claims, powers })
}

pub fn gamma_combine_circle_pcs_layer0(
    shape: CirclePcsShape,
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    powers: &[QM31],
) -> Result<[QM31; CIRCLE_PCS_FIBER_SLOTS], CirclePcsDecodeError> {
    let shape = shape.validate()?;
    let c1_expected = shape.c1_leaf_bytes_checked()?;
    let c2_expected = shape.c2_leaf_bytes_checked()?;
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
    if powers.len() != shape.total_columns() {
        return Err(CirclePcsDecodeError::EvaluationLength {
            expected: shape.total_columns() * 16,
            actual: powers.len() * 16,
        });
    }

    let mut combined = [QM31::ZERO; CIRCLE_PCS_FIBER_SLOTS];
    for (slot, output) in combined.iter_mut().enumerate() {
        for (column, power) in powers
            .iter()
            .copied()
            .take(usize::from(shape.c1_columns))
            .enumerate()
        {
            let offset = (slot * usize::from(shape.c1_columns) + column) * 4;
            let encoded: [u8; 4] = c1_leaf[offset..offset + 4].try_into().unwrap();
            let value = M31::from_le_bytes(encoded)
                .ok_or(CirclePcsDecodeError::NonCanonicalC1 { offset })?;
            *output = output.add(power.mul_m31(value));
        }
    }
    for helper in 0..usize::from(shape.c2_columns) {
        let power = powers[usize::from(shape.c1_columns) + helper];
        for (slot, output) in combined.iter_mut().enumerate() {
            let offset = (helper * CIRCLE_PCS_FIBER_SLOTS + slot) * 16;
            let value = QM31::from_le_bytes(&c2_leaf[offset..offset + 16])
                .ok_or(CirclePcsDecodeError::NonCanonicalC2 { offset })?;
            *output = output.add(power.mul(value));
        }
    }
    Ok(combined)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::CM31;

    const PROFILE24: CirclePcsShape = CirclePcsShape {
        trace_log_size: 10,
        domain_log_size: 19,
        query_count: 20,
        opening_points: 3,
        c1_columns: 16,
        c2_columns: 1,
        c1_layer0_tag: 0x50,
        c2_layer0_tag: 0xd0,
        later_layer_tags: [0x51, 0x52, 0x53],
    };

    fn q(value: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(value), M31(value + 1)),
            c1: CM31::new(M31(value + 2), M31(value + 3)),
        }
    }

    #[test]
    fn profile24_shape_pins_widths_geometry_and_descriptor() {
        assert_eq!(PROFILE24.validate(), Ok(PROFILE24));
        assert_eq!(PROFILE24.message_len(), 1_024);
        assert_eq!(PROFILE24.codeword_len(), 1 << 19);
        assert_eq!(PROFILE24.fiber_count(), 1 << 17);
        assert_eq!(PROFILE24.total_columns(), 17);
        assert_eq!(PROFILE24.opening_count(), 51);
        assert_eq!(PROFILE24.evaluation_bytes(), 816);
        assert_eq!(PROFILE24.c1_leaf_bytes_checked(), Ok(256));
        assert_eq!(PROFILE24.c2_leaf_bytes_checked(), Ok(64));
        assert_eq!(
            PROFILE24.opening_geometry(),
            Ok(CircleOpeningGeometry {
                layer0_binary_depth: 17,
                later_binary_depths: [15, 13, 11],
            })
        );
        let encoded = PROFILE24.encode().unwrap();
        assert_eq!(&encoded[..8], &[1, 10, 19, 4, 20, 0, 3, 4]);
        assert_eq!(&encoded[12..16], &[0, 1, 64, 0]);
        assert_eq!(&encoded[16..21], &[0x50, 0xd0, 0x51, 0x52, 0x53]);
        assert_eq!(&encoded[21..], &[0, 0, 0]);
    }

    #[test]
    fn claims_and_opened_fiber_share_one_generator_order() {
        let gamma = q(5);
        let powers = prepare_circle_pcs_claims(PROFILE24, gamma, &[0u8; 816])
            .unwrap()
            .powers;
        let mut c1 = [0u8; 256];
        let mut c2 = [0u8; 64];
        let mut expected = [QM31::ZERO; 4];
        for (slot, expected_slot) in expected.iter_mut().enumerate() {
            for (column, power) in powers.iter().copied().take(16).enumerate() {
                let value = M31((slot * 19 + column + 1) as u32);
                let offset = (slot * 16 + column) * 4;
                c1[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
                *expected_slot = expected_slot.add(power.mul_m31(value));
            }
            let helper = q(100 + slot as u32 * 7);
            helper.write_le_bytes(&mut c2[slot * 16..slot * 16 + 16]);
            *expected_slot = expected_slot.add(powers[16].mul(helper));
        }
        assert_eq!(
            gamma_combine_circle_pcs_layer0(PROFILE24, &c1, &c2, &powers),
            Ok(expected)
        );
    }

    #[test]
    fn malformed_shapes_fail_before_width_or_tag_use() {
        assert_eq!(
            CirclePcsShape {
                query_count: 0,
                ..PROFILE24
            }
            .validate(),
            Err(CirclePcsShapeError::EmptyQueries)
        );
        assert_eq!(
            CirclePcsShape {
                c2_layer0_tag: 0x50,
                ..PROFILE24
            }
            .validate(),
            Err(CirclePcsShapeError::DuplicateTreeTag { tag: 0x50 })
        );
    }
}
