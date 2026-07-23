//! Offline frozen-q18 Component-C conditioned-view matrix generator.
//!
//! This host-only module emits the `76 x 1023` matrix for the four public
//! Component-C claims on one deterministic CU fixture schedule:
//! 18 authenticated layer-zero fibres times four slots, three MLE claims,
//! and one structured terminal claim.  It deliberately contains no `F` map,
//! legal-difference space, C-DEC certificate, verifier wire, or production
//! integration.

use core::fmt;

use aspis_core::circle_line_merkle::{
    derive_circle_line_query_indices_for_count, CircleLineQueryIndices,
};
use aspis_core::field::{CM31, M31, P, QM31};
use aspis_statement::atomic_state_only_terminal::{
    atomic_state_only_copy_inactive_row_masks_v3,
    PINNED_ATOMIC_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT_V3,
};
use aspis_statement::{binary_successor_point, xor12_point};

use super::component_c::{
    v5_c_inactive_functional, v5_c_pivot_row, V5ComponentCLane, V5_C_FREE_COORDINATES, V5_C_ROWS,
};
use super::real_host_proof::{
    V5RealHostArtifact, V5_REAL_HOST_QUERY_COUNT, V5_REAL_HOST_TRANSCRIPT_DOMAIN,
};
use super::spend_messages::{V5_C2_LANES, V5_FIBRE_SLOTS, V5_LAYER_ZERO_LEAVES};
use super::split_layer_zero::{v5_structured_terminal_covector, V5_RELATION_LANES};
use super::{V5_DOMAIN_LOG, V5_TRACE_ROWS};
use crate::circle_candidate::{CircleCandidateError, CircleEncoder};

pub const V5_C_EMAT_LAYER_ZERO_ROWS: usize = V5_REAL_HOST_QUERY_COUNT * V5_FIBRE_SLOTS;
pub const V5_C_EMAT_POINT_ROWS: usize = 3;
pub const V5_C_EMAT_TERMINAL_ROWS: usize = 1;
pub const V5_C_EMAT_ROWS: usize =
    V5_C_EMAT_LAYER_ZERO_ROWS + V5_C_EMAT_POINT_ROWS + V5_C_EMAT_TERMINAL_ROWS;
pub const V5_C_EMAT_COLUMNS: usize = V5_C_FREE_COORDINATES;
pub const V5_C_EMAT_QM31_BYTES: usize = 16;
pub const V5_C_EMAT_MATRIX_BYTES: usize = V5_C_EMAT_ROWS * V5_C_EMAT_COLUMNS * V5_C_EMAT_QM31_BYTES;
pub const V5_C_EMAT_SCHEDULE_BYTES: usize = 17_618 + V5_REAL_HOST_TRANSCRIPT_DOMAIN.len();

pub const V5_C_EMAT_ARTIFACT_MAGIC: [u8; 8] = *b"AV5EMT01";
pub const V5_C_EMAT_ARTIFACT_VERSION: u16 = 1;
pub const V5_C_EMAT_ARTIFACT_FLAGS: u16 = 0;
pub const V5_C_EMAT_ARTIFACT_HEADER_BYTES: usize = 128;

pub const V5_C_EMAT_KAT_BASIS_COLUMNS: [usize; 8] =
    [0, 1, 10, 137, 511, 683, 947, V5_C_EMAT_COLUMNS - 1];

const SCHEDULE_HASH_DOMAIN: &[u8] = b"aspis-v5-component-c-emat-schedule-v1";
const MATRIX_HASH_DOMAIN: &[u8] = b"aspis-v5-component-c-emat-matrix-v1";
const VECTOR_HASH_DOMAIN: &[u8] = b"aspis-v5-component-c-emat-vector-v1";

const _: () = assert!(V5_C_EMAT_LAYER_ZERO_ROWS == 72);
const _: () = assert!(V5_C_EMAT_ROWS == 76);
const _: () = assert!(V5_C_EMAT_COLUMNS == 1023);
const _: () = assert!(V5_C_EMAT_MATRIX_BYTES == 1_243_968);
const _: () = assert!(V5_C_EMAT_SCHEDULE_BYTES == 17_645);
const _: () = assert!(V5_C2_LANES == 3);
const _: () = assert!(V5_RELATION_LANES == 19);
const _: () = assert!(V5_TRACE_ROWS == V5_C_ROWS);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum V5ComponentCEmatError {
    OpeningIndexDrift,
    CollisionShape {
        layer: u8,
        expected: usize,
        actual: usize,
    },
    PointScheduleDrift,
    TerminalCovectorShape {
        expected: usize,
        actual: usize,
    },
    TerminalCovectorDrift,
    PivotOutOfRange {
        pivot: usize,
    },
    PivotNotInactive {
        pivot: usize,
    },
    FreeCoordinateRoundTrip {
        column: usize,
    },
    InactiveFunctional {
        column: usize,
    },
    MatrixShape {
        expected: usize,
        actual: usize,
    },
    ReferenceParity {
        case: &'static str,
        index: usize,
    },
    Linearity {
        case: &'static str,
    },
    ArtifactShape,
    ArtifactHash {
        section: &'static str,
    },
    Circle(CircleCandidateError),
}

impl fmt::Display for V5ComponentCEmatError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OpeningIndexDrift => write!(formatter, "frozen opening-index derivation drift"),
            Self::CollisionShape {
                layer,
                expected,
                actual,
            } => write!(
                formatter,
                "frozen q18 layer {layer} expected {expected} distinct leaves, got {actual}"
            ),
            Self::PointScheduleDrift => write!(formatter, "frozen relation-point schedule drift"),
            Self::TerminalCovectorShape { expected, actual } => write!(
                formatter,
                "terminal covector expected {expected} rows, got {actual}"
            ),
            Self::TerminalCovectorDrift => {
                write!(formatter, "frozen structured terminal covector drift")
            }
            Self::PivotOutOfRange { pivot } => {
                write!(formatter, "Component-C pivot row {pivot} is out of range")
            }
            Self::PivotNotInactive { pivot } => {
                write!(formatter, "Component-C pivot row {pivot} is not inactive")
            }
            Self::FreeCoordinateRoundTrip { column } => {
                write!(
                    formatter,
                    "free-coordinate basis column {column} did not round-trip"
                )
            }
            Self::InactiveFunctional { column } => write!(
                formatter,
                "free-coordinate basis column {column} left the inactive kernel"
            ),
            Self::MatrixShape { expected, actual } => {
                write!(
                    formatter,
                    "matrix expected {expected} entries, got {actual}"
                )
            }
            Self::ReferenceParity { case, index } => {
                write!(formatter, "{case} reference parity failed at index {index}")
            }
            Self::Linearity { case } => write!(formatter, "linearity check failed: {case}"),
            Self::ArtifactShape => write!(formatter, "non-canonical Emat artifact shape"),
            Self::ArtifactHash { section } => {
                write!(formatter, "Emat artifact {section} hash mismatch")
            }
            Self::Circle(error) => write!(formatter, "circle encoder error: {error}"),
        }
    }
}

impl std::error::Error for V5ComponentCEmatError {}

impl From<CircleCandidateError> for V5ComponentCEmatError {
    fn from(error: CircleCandidateError) -> Self {
        Self::Circle(error)
    }
}

/// Exact inputs on which the frozen conditioned-view matrix depends.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5ComponentCFrozenESchedule {
    pub statement_digest: [u8; 32],
    pub transcript_state_after_queries: [u8; 32],
    pub roots: [[u8; 32]; 5],
    pub query_selector: u8,
    pub queries: [u32; V5_REAL_HOST_QUERY_COUNT],
    pub layer0_fibres: [u32; V5_REAL_HOST_QUERY_COUNT],
    pub later_fibres: [[u32; V5_REAL_HOST_QUERY_COUNT]; 3],
    pub points: [[QM31; 10]; 3],
    pub terminal_covector: [QM31; V5_C_ROWS],
    pub inactive_masks: [u16; 64],
    pub pivot_row: usize,
}

fn fixed_array<const N: usize>(
    values: &[u32],
    layer: u8,
) -> Result<[u32; N], V5ComponentCEmatError> {
    values
        .try_into()
        .map_err(|_| V5ComponentCEmatError::CollisionShape {
            layer,
            expected: N,
            actual: values.len(),
        })
}

fn validate_query_shape(
    queries: &[u32; V5_REAL_HOST_QUERY_COUNT],
    expected: &CircleLineQueryIndices,
) -> Result<CircleLineQueryIndices, V5ComponentCEmatError> {
    let derived = derive_circle_line_query_indices_for_count(queries, V5_LAYER_ZERO_LEAVES)
        .map_err(|_| V5ComponentCEmatError::OpeningIndexDrift)?;
    if &derived != expected {
        return Err(V5ComponentCEmatError::OpeningIndexDrift);
    }
    if derived.layer0.len() != V5_REAL_HOST_QUERY_COUNT {
        return Err(V5ComponentCEmatError::CollisionShape {
            layer: 0,
            expected: V5_REAL_HOST_QUERY_COUNT,
            actual: derived.layer0.len(),
        });
    }
    for (layer, indices) in derived.later.iter().enumerate() {
        if indices.len() != V5_REAL_HOST_QUERY_COUNT {
            return Err(V5ComponentCEmatError::CollisionShape {
                layer: layer as u8 + 1,
                expected: V5_REAL_HOST_QUERY_COUNT,
                actual: indices.len(),
            });
        }
    }
    Ok(derived)
}

impl V5ComponentCFrozenESchedule {
    /// Extract the exact E-map schedule from the deterministic real-host CU
    /// artifact. Every index is rederived; collision-free q18 shape is a hard
    /// requirement rather than an assumed fixture property.
    pub fn from_real_host_artifact(
        artifact: &V5RealHostArtifact,
    ) -> Result<Self, V5ComponentCEmatError> {
        let indices = validate_query_shape(&artifact.queries, &artifact.opening_indices)?;
        let z = artifact.semantic_sumcheck.challenges;
        let points = [z, binary_successor_point(&z), xor12_point(&z)];
        if artifact.relation_claims.points != points {
            return Err(V5ComponentCEmatError::PointScheduleDrift);
        }
        let expected_terminal = v5_structured_terminal_covector(&z);
        if artifact.relation_claims.terminal_covector.len() != V5_C_ROWS {
            return Err(V5ComponentCEmatError::TerminalCovectorShape {
                expected: V5_C_ROWS,
                actual: artifact.relation_claims.terminal_covector.len(),
            });
        }
        if artifact.relation_claims.terminal_covector != expected_terminal {
            return Err(V5ComponentCEmatError::TerminalCovectorDrift);
        }
        let terminal_covector: [QM31; V5_C_ROWS] =
            expected_terminal.try_into().map_err(|values: Vec<QM31>| {
                V5ComponentCEmatError::TerminalCovectorShape {
                    expected: V5_C_ROWS,
                    actual: values.len(),
                }
            })?;

        let inactive_masks = atomic_state_only_copy_inactive_row_masks_v3();
        let pivot_row = v5_c_pivot_row();
        if pivot_row >= V5_C_ROWS {
            return Err(V5ComponentCEmatError::PivotOutOfRange { pivot: pivot_row });
        }
        if inactive_masks[pivot_row >> 4] & (1 << (pivot_row & 15)) == 0 {
            return Err(V5ComponentCEmatError::PivotNotInactive { pivot: pivot_row });
        }

        Ok(Self {
            statement_digest: artifact.statement_digest,
            transcript_state_after_queries: artifact.transcript_state_after_queries,
            roots: [
                artifact.roots.c1,
                artifact.roots.c2,
                artifact.roots.later[0],
                artifact.roots.later[1],
                artifact.roots.later[2],
            ],
            query_selector: artifact.query_selector,
            queries: artifact.queries,
            layer0_fibres: fixed_array(&indices.layer0, 0)?,
            later_fibres: [
                fixed_array(&indices.later[0], 1)?,
                fixed_array(&indices.later[1], 2)?,
                fixed_array(&indices.later[2], 3)?,
            ],
            points,
            terminal_covector,
            inactive_masks,
            pivot_row,
        })
    }

    /// Canonical schedule encoding used by the artifact hash. Redundant
    /// derived data is intentional: a reader can detect row-order or layout
    /// drift without rerunning the transcript.
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&(V5_REAL_HOST_TRANSCRIPT_DOMAIN.len() as u16).to_le_bytes());
        bytes.extend_from_slice(V5_REAL_HOST_TRANSCRIPT_DOMAIN);
        bytes.extend_from_slice(&V5_DOMAIN_LOG.to_le_bytes());
        bytes.extend_from_slice(&(V5_LAYER_ZERO_LEAVES as u32).to_le_bytes());
        bytes.extend_from_slice(&(V5_FIBRE_SLOTS as u32).to_le_bytes());
        bytes.extend_from_slice(&(V5_C2_LANES as u32).to_le_bytes());
        bytes.extend_from_slice(&(V5_RELATION_LANES as u32).to_le_bytes());
        bytes.extend_from_slice(&P.to_le_bytes());
        bytes.extend_from_slice(
            &PINNED_ATOMIC_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT_V3.to_le_bytes(),
        );
        bytes.extend_from_slice(&self.statement_digest);
        bytes.extend_from_slice(&self.transcript_state_after_queries);
        for root in self.roots {
            bytes.extend_from_slice(&root);
        }
        bytes.push(self.query_selector);
        bytes.extend_from_slice(&[0u8; 3]);
        for query in self.queries {
            bytes.extend_from_slice(&query.to_le_bytes());
        }
        for index in self.layer0_fibres {
            bytes.extend_from_slice(&index.to_le_bytes());
        }
        for layer in self.later_fibres {
            for index in layer {
                bytes.extend_from_slice(&index.to_le_bytes());
            }
        }
        for point in self.points {
            for value in point {
                let start = bytes.len();
                bytes.resize(start + V5_C_EMAT_QM31_BYTES, 0);
                value.write_le_bytes(&mut bytes[start..]);
            }
        }
        for value in self.terminal_covector {
            let start = bytes.len();
            bytes.resize(start + V5_C_EMAT_QM31_BYTES, 0);
            value.write_le_bytes(&mut bytes[start..]);
        }
        for mask in self.inactive_masks {
            bytes.extend_from_slice(&mask.to_le_bytes());
        }
        bytes.extend_from_slice(&(self.pivot_row as u32).to_le_bytes());
        bytes
    }

    pub fn sha256(&self) -> [u8; 32] {
        crate::host_hashv(&[SCHEDULE_HASH_DOMAIN, &self.canonical_bytes()])
    }
}

fn free_basis(column: usize) -> [QM31; V5_C_EMAT_COLUMNS] {
    let mut free = [QM31::ZERO; V5_C_EMAT_COLUMNS];
    free[column] = QM31::ONE;
    free
}

fn nonzero_lane_terms(lane: &V5ComponentCLane) -> Vec<(usize, QM31)> {
    lane.values()
        .iter()
        .copied()
        .enumerate()
        .filter(|(_, value)| *value != QM31::ZERO)
        .collect()
}

fn encode_sparse_value(
    encoder: &CircleEncoder,
    terms: &[(usize, QM31)],
    codeword_index: usize,
) -> Result<QM31, V5ComponentCEmatError> {
    terms
        .iter()
        .copied()
        .try_fold(QM31::ZERO, |sum, (row, coefficient)| {
            let basis = encoder.encode_c1_basis_value(row, codeword_index)?;
            Ok(sum.add(coefficient.mul_m31(basis)))
        })
}

fn evaluate_sparse_with_encoder(
    schedule: &V5ComponentCFrozenESchedule,
    encoder: &CircleEncoder,
    free: &[QM31; V5_C_EMAT_COLUMNS],
) -> Result<[QM31; V5_C_EMAT_ROWS], V5ComponentCEmatError> {
    let lane = V5ComponentCLane::encode_free_coordinates(free);
    let terms = nonzero_lane_terms(&lane);
    let mut output = [QM31::ZERO; V5_C_EMAT_ROWS];
    for (fibre_ordinal, fibre) in schedule.layer0_fibres.iter().copied().enumerate() {
        for slot in 0..V5_FIBRE_SLOTS {
            let codeword_index = V5_FIBRE_SLOTS * fibre as usize + slot;
            output[V5_FIBRE_SLOTS * fibre_ordinal + slot] =
                encode_sparse_value(encoder, &terms, codeword_index)?;
        }
    }
    let claims = lane.relation_claims(&schedule.points[0], &schedule.terminal_covector);
    output[V5_C_EMAT_LAYER_ZERO_ROWS..].copy_from_slice(&claims);
    Ok(output)
}

fn evaluate_reference_with_encoder(
    schedule: &V5ComponentCFrozenESchedule,
    encoder: &CircleEncoder,
    free: &[QM31; V5_C_EMAT_COLUMNS],
) -> Result<[QM31; V5_C_EMAT_ROWS], V5ComponentCEmatError> {
    let lane = V5ComponentCLane::encode_free_coordinates(free);
    let codeword = encoder.encode_c2_message(lane.values())?;
    let mut output = [QM31::ZERO; V5_C_EMAT_ROWS];
    for (fibre_ordinal, fibre) in schedule.layer0_fibres.iter().copied().enumerate() {
        for slot in 0..V5_FIBRE_SLOTS {
            output[V5_FIBRE_SLOTS * fibre_ordinal + slot] =
                codeword[V5_FIBRE_SLOTS * fibre as usize + slot];
        }
    }
    let claims = lane.relation_claims(&schedule.points[0], &schedule.terminal_covector);
    output[V5_C_EMAT_LAYER_ZERO_ROWS..].copy_from_slice(&claims);
    Ok(output)
}

/// Evaluate all 76 conditioned rows without materialising the rate-1/512
/// codeword. This is exact encoder-matrix arithmetic, not an approximation.
pub fn evaluate_component_c_e_sparse(
    schedule: &V5ComponentCFrozenESchedule,
    free: &[QM31; V5_C_EMAT_COLUMNS],
) -> Result<[QM31; V5_C_EMAT_ROWS], V5ComponentCEmatError> {
    let encoder = CircleEncoder::new_for_domain_log(V5_DOMAIN_LOG);
    evaluate_sparse_with_encoder(schedule, &encoder, free)
}

/// Slow reference path through the complete deployed C2 circle encoder.
pub fn evaluate_component_c_e_reference(
    schedule: &V5ComponentCFrozenESchedule,
    free: &[QM31; V5_C_EMAT_COLUMNS],
) -> Result<[QM31; V5_C_EMAT_ROWS], V5ComponentCEmatError> {
    let encoder = CircleEncoder::new_for_domain_log(V5_DOMAIN_LOG);
    evaluate_reference_with_encoder(schedule, &encoder, free)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5ComponentCEmat {
    entries: Vec<QM31>,
}

impl V5ComponentCEmat {
    /// Generate every column from the actual free-coordinate encoder. The
    /// layer-zero rows use sparse entries of the real circle encoding matrix;
    /// the four claims use the same literal Rust evaluators as the prover.
    pub fn generate(schedule: &V5ComponentCFrozenESchedule) -> Result<Self, V5ComponentCEmatError> {
        let encoder = CircleEncoder::new_for_domain_log(V5_DOMAIN_LOG);
        let mut entries = vec![QM31::ZERO; V5_C_EMAT_ROWS * V5_C_EMAT_COLUMNS];
        for column in 0..V5_C_EMAT_COLUMNS {
            let free = free_basis(column);
            let lane = V5ComponentCLane::encode_free_coordinates(&free);
            if lane.free_coordinates() != free {
                return Err(V5ComponentCEmatError::FreeCoordinateRoundTrip { column });
            }
            if v5_c_inactive_functional(lane.values()) != QM31::ZERO {
                return Err(V5ComponentCEmatError::InactiveFunctional { column });
            }
            let values = evaluate_sparse_with_encoder(schedule, &encoder, &free)?;
            for (row, value) in values.into_iter().enumerate() {
                entries[row * V5_C_EMAT_COLUMNS + column] = value;
            }
        }
        Ok(Self { entries })
    }

    pub fn from_entries(entries: Vec<QM31>) -> Result<Self, V5ComponentCEmatError> {
        let expected = V5_C_EMAT_ROWS * V5_C_EMAT_COLUMNS;
        if entries.len() != expected {
            return Err(V5ComponentCEmatError::MatrixShape {
                expected,
                actual: entries.len(),
            });
        }
        Ok(Self { entries })
    }

    pub fn entry(&self, row: usize, column: usize) -> QM31 {
        self.entries[row * V5_C_EMAT_COLUMNS + column]
    }

    pub fn column(&self, column: usize) -> [QM31; V5_C_EMAT_ROWS] {
        core::array::from_fn(|row| self.entry(row, column))
    }

    pub fn mul_vec(&self, vector: &[QM31; V5_C_EMAT_COLUMNS]) -> [QM31; V5_C_EMAT_ROWS] {
        core::array::from_fn(|row| {
            (0..V5_C_EMAT_COLUMNS).fold(QM31::ZERO, |sum, column| {
                sum.add(self.entry(row, column).mul(vector[column]))
            })
        })
    }

    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut bytes = vec![0u8; V5_C_EMAT_MATRIX_BYTES];
        for (index, value) in self.entries.iter().copied().enumerate() {
            value.write_le_bytes(
                &mut bytes[index * V5_C_EMAT_QM31_BYTES..(index + 1) * V5_C_EMAT_QM31_BYTES],
            );
        }
        bytes
    }

    pub fn sha256(&self) -> [u8; 32] {
        crate::host_hashv(&[MATRIX_HASH_DOMAIN, &self.canonical_bytes()])
    }

    pub fn encode_artifact(&self, schedule: &V5ComponentCFrozenESchedule) -> Vec<u8> {
        let schedule_bytes = schedule.canonical_bytes();
        debug_assert_eq!(schedule_bytes.len(), V5_C_EMAT_SCHEDULE_BYTES);
        let matrix_bytes = self.canonical_bytes();
        let schedule_hash = crate::host_hashv(&[SCHEDULE_HASH_DOMAIN, &schedule_bytes]);
        let matrix_hash = crate::host_hashv(&[MATRIX_HASH_DOMAIN, &matrix_bytes]);
        let mut output = vec![0u8; V5_C_EMAT_ARTIFACT_HEADER_BYTES];
        output[0..8].copy_from_slice(&V5_C_EMAT_ARTIFACT_MAGIC);
        output[8..10].copy_from_slice(&V5_C_EMAT_ARTIFACT_VERSION.to_le_bytes());
        output[10..12].copy_from_slice(&V5_C_EMAT_ARTIFACT_FLAGS.to_le_bytes());
        output[12..16].copy_from_slice(&(V5_C_EMAT_ARTIFACT_HEADER_BYTES as u32).to_le_bytes());
        output[16..20].copy_from_slice(&(V5_C_EMAT_ROWS as u32).to_le_bytes());
        output[20..24].copy_from_slice(&(V5_C_EMAT_COLUMNS as u32).to_le_bytes());
        output[24..28].copy_from_slice(&(V5_C_EMAT_LAYER_ZERO_ROWS as u32).to_le_bytes());
        output[28..32].copy_from_slice(&4u32.to_le_bytes());
        output[32..36].copy_from_slice(&(V5_REAL_HOST_QUERY_COUNT as u32).to_le_bytes());
        output[36..40].copy_from_slice(&V5_DOMAIN_LOG.to_le_bytes());
        output[40..44].copy_from_slice(&(schedule.pivot_row as u32).to_le_bytes());
        output[44..48].copy_from_slice(&P.to_le_bytes());
        output[48..52].copy_from_slice(&(V5_C_EMAT_QM31_BYTES as u32).to_le_bytes());
        output[52..56].copy_from_slice(&(schedule_bytes.len() as u32).to_le_bytes());
        output[56..64].copy_from_slice(&(matrix_bytes.len() as u64).to_le_bytes());
        output[64..96].copy_from_slice(&schedule_hash);
        output[96..128].copy_from_slice(&matrix_hash);
        output.extend_from_slice(&schedule_bytes);
        output.extend_from_slice(&matrix_bytes);
        output
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5ComponentCEmatArtifactView<'a> {
    pub schedule_bytes: &'a [u8],
    pub matrix_bytes: &'a [u8],
    pub schedule_sha256: [u8; 32],
    pub matrix_sha256: [u8; 32],
}

fn read_u16(bytes: &[u8], start: usize) -> Result<u16, V5ComponentCEmatError> {
    Ok(u16::from_le_bytes(
        bytes
            .get(start..start + 2)
            .ok_or(V5ComponentCEmatError::ArtifactShape)?
            .try_into()
            .unwrap(),
    ))
}

fn read_u32(bytes: &[u8], start: usize) -> Result<u32, V5ComponentCEmatError> {
    Ok(u32::from_le_bytes(
        bytes
            .get(start..start + 4)
            .ok_or(V5ComponentCEmatError::ArtifactShape)?
            .try_into()
            .unwrap(),
    ))
}

fn read_u64(bytes: &[u8], start: usize) -> Result<u64, V5ComponentCEmatError> {
    Ok(u64::from_le_bytes(
        bytes
            .get(start..start + 8)
            .ok_or(V5ComponentCEmatError::ArtifactShape)?
            .try_into()
            .unwrap(),
    ))
}

/// Parse and hash-check the maps-only artifact. Exact length is enforced, so
/// neither truncation nor hidden trailing sections are accepted.
pub fn validate_component_c_emat_artifact(
    bytes: &[u8],
) -> Result<V5ComponentCEmatArtifactView<'_>, V5ComponentCEmatError> {
    if bytes.len() < V5_C_EMAT_ARTIFACT_HEADER_BYTES
        || bytes.get(0..8) != Some(V5_C_EMAT_ARTIFACT_MAGIC.as_slice())
        || read_u16(bytes, 8)? != V5_C_EMAT_ARTIFACT_VERSION
        || read_u16(bytes, 10)? != V5_C_EMAT_ARTIFACT_FLAGS
        || read_u32(bytes, 12)? as usize != V5_C_EMAT_ARTIFACT_HEADER_BYTES
        || read_u32(bytes, 16)? as usize != V5_C_EMAT_ROWS
        || read_u32(bytes, 20)? as usize != V5_C_EMAT_COLUMNS
        || read_u32(bytes, 24)? as usize != V5_C_EMAT_LAYER_ZERO_ROWS
        || read_u32(bytes, 28)? != 4
        || read_u32(bytes, 32)? as usize != V5_REAL_HOST_QUERY_COUNT
        || read_u32(bytes, 36)? != V5_DOMAIN_LOG
        || read_u32(bytes, 44)? != P
        || read_u32(bytes, 48)? as usize != V5_C_EMAT_QM31_BYTES
        || read_u32(bytes, 52)? as usize != V5_C_EMAT_SCHEDULE_BYTES
        || read_u64(bytes, 56)? as usize != V5_C_EMAT_MATRIX_BYTES
    {
        return Err(V5ComponentCEmatError::ArtifactShape);
    }
    let schedule_len = read_u32(bytes, 52)? as usize;
    let schedule_start = V5_C_EMAT_ARTIFACT_HEADER_BYTES;
    let matrix_start = schedule_start
        .checked_add(schedule_len)
        .ok_or(V5ComponentCEmatError::ArtifactShape)?;
    let end = matrix_start
        .checked_add(V5_C_EMAT_MATRIX_BYTES)
        .ok_or(V5ComponentCEmatError::ArtifactShape)?;
    if end != bytes.len() {
        return Err(V5ComponentCEmatError::ArtifactShape);
    }
    let schedule_bytes = &bytes[schedule_start..matrix_start];
    let matrix_bytes = &bytes[matrix_start..end];
    let schedule_pivot = u32::from_le_bytes(
        schedule_bytes[schedule_bytes.len() - 4..]
            .try_into()
            .unwrap(),
    );
    if read_u32(bytes, 40)? != schedule_pivot || schedule_pivot as usize >= V5_C_ROWS {
        return Err(V5ComponentCEmatError::ArtifactShape);
    }
    let schedule_sha256: [u8; 32] = bytes[64..96].try_into().unwrap();
    let matrix_sha256: [u8; 32] = bytes[96..128].try_into().unwrap();
    if crate::host_hashv(&[SCHEDULE_HASH_DOMAIN, schedule_bytes]) != schedule_sha256 {
        return Err(V5ComponentCEmatError::ArtifactHash {
            section: "schedule",
        });
    }
    if crate::host_hashv(&[MATRIX_HASH_DOMAIN, matrix_bytes]) != matrix_sha256 {
        return Err(V5ComponentCEmatError::ArtifactHash { section: "matrix" });
    }
    if matrix_bytes
        .chunks_exact(V5_C_EMAT_QM31_BYTES)
        .any(|entry| QM31::from_le_bytes(entry).is_none())
    {
        return Err(V5ComponentCEmatError::ArtifactShape);
    }
    Ok(V5ComponentCEmatArtifactView {
        schedule_bytes,
        matrix_bytes,
        schedule_sha256,
        matrix_sha256,
    })
}

fn encode_qm31_vector(values: &[QM31]) -> Vec<u8> {
    let mut bytes = vec![0u8; values.len() * V5_C_EMAT_QM31_BYTES];
    for (index, value) in values.iter().copied().enumerate() {
        value.write_le_bytes(
            &mut bytes[index * V5_C_EMAT_QM31_BYTES..(index + 1) * V5_C_EMAT_QM31_BYTES],
        );
    }
    bytes
}

fn hash_qm31_vector(values: &[QM31]) -> [u8; 32] {
    crate::host_hashv(&[VECTOR_HASH_DOMAIN, &encode_qm31_vector(values)])
}

fn kat_word(seed: u32) -> [QM31; V5_C_EMAT_COLUMNS] {
    core::array::from_fn(|index| {
        let index = index as u64 + 1;
        let limb = |factor: u64, add: u64| {
            M31(((u64::from(seed) + factor * index + add) % u64::from(P)) as u32)
        };
        QM31 {
            c0: CM31::new(limb(1_003, 1), limb(1_009, 3)),
            c1: CM31::new(limb(1_021, 5), limb(1_031, 7)),
        }
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5ComponentCEmatKatMetadata {
    pub basis_columns: [usize; V5_C_EMAT_KAT_BASIS_COLUMNS.len()],
    pub basis_column_sha256: [[u8; 32]; V5_C_EMAT_KAT_BASIS_COLUMNS.len()],
    pub dense_input_sha256: [u8; 32],
    pub dense_output_sha256: [u8; 32],
    pub reference_parity_cases: usize,
    pub linearity_checks: usize,
}

/// Run deterministic teeth and return their hashes for the JSON manifest.
/// Selected basis columns and one dense vector use the complete C2 encoder;
/// matrix multiplication and sparse evaluation must match them exactly.
pub fn build_component_c_emat_kats(
    schedule: &V5ComponentCFrozenESchedule,
    matrix: &V5ComponentCEmat,
) -> Result<V5ComponentCEmatKatMetadata, V5ComponentCEmatError> {
    let encoder = CircleEncoder::new_for_domain_log(V5_DOMAIN_LOG);
    let mut basis_hashes = [[0u8; 32]; V5_C_EMAT_KAT_BASIS_COLUMNS.len()];
    for (kat, column) in V5_C_EMAT_KAT_BASIS_COLUMNS.iter().copied().enumerate() {
        let free = free_basis(column);
        let sparse = evaluate_sparse_with_encoder(schedule, &encoder, &free)?;
        let reference = evaluate_reference_with_encoder(schedule, &encoder, &free)?;
        let emitted = matrix.column(column);
        if sparse != reference || sparse != emitted {
            return Err(V5ComponentCEmatError::ReferenceParity {
                case: "basis",
                index: column,
            });
        }
        basis_hashes[kat] = hash_qm31_vector(&emitted);
    }

    let dense = kat_word(0xc031_5eed);
    let dense_sparse = evaluate_sparse_with_encoder(schedule, &encoder, &dense)?;
    let dense_reference = evaluate_reference_with_encoder(schedule, &encoder, &dense)?;
    let dense_emitted = matrix.mul_vec(&dense);
    if dense_sparse != dense_reference || dense_sparse != dense_emitted {
        return Err(V5ComponentCEmatError::ReferenceParity {
            case: "dense",
            index: 0,
        });
    }

    let left = kat_word(0x51a7_1001);
    let right = kat_word(0x51a7_2002);
    let scalar = QM31 {
        c0: CM31::new(M31(17), M31(19)),
        c1: CM31::new(M31(23), M31(29)),
    };
    let sum = core::array::from_fn(|index| left[index].add(right[index]));
    let scaled = core::array::from_fn(|index| scalar.mul(left[index]));
    let e_left = evaluate_sparse_with_encoder(schedule, &encoder, &left)?;
    let e_right = evaluate_sparse_with_encoder(schedule, &encoder, &right)?;
    let e_sum = evaluate_sparse_with_encoder(schedule, &encoder, &sum)?;
    let expected_sum = core::array::from_fn(|row| e_left[row].add(e_right[row]));
    if e_sum != expected_sum || matrix.mul_vec(&sum) != expected_sum {
        return Err(V5ComponentCEmatError::Linearity { case: "additivity" });
    }
    let e_scaled = evaluate_sparse_with_encoder(schedule, &encoder, &scaled)?;
    let expected_scaled = core::array::from_fn(|row| scalar.mul(e_left[row]));
    if e_scaled != expected_scaled || matrix.mul_vec(&scaled) != expected_scaled {
        return Err(V5ComponentCEmatError::Linearity {
            case: "homogeneity",
        });
    }

    Ok(V5ComponentCEmatKatMetadata {
        basis_columns: V5_C_EMAT_KAT_BASIS_COLUMNS,
        basis_column_sha256: basis_hashes,
        dense_input_sha256: hash_qm31_vector(&dense),
        dense_output_sha256: hash_qm31_vector(&dense_emitted),
        reference_parity_cases: V5_C_EMAT_KAT_BASIS_COLUMNS.len() + 1,
        linearity_checks: 2,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(seed: u32) -> QM31 {
        QM31 {
            c0: CM31::new(M31(seed * 1_003 + 1), M31(seed * 1_009 + 3)),
            c1: CM31::new(M31(seed * 1_021 + 5), M31(seed * 1_031 + 7)),
        }
    }

    fn synthetic_schedule() -> V5ComponentCFrozenESchedule {
        let queries = core::array::from_fn(|index| 123 + 4_096 * index as u32);
        let indices =
            derive_circle_line_query_indices_for_count(&queries, V5_LAYER_ZERO_LEAVES).unwrap();
        assert_eq!(indices.layer0.len(), V5_REAL_HOST_QUERY_COUNT);
        assert!(indices
            .later
            .iter()
            .all(|layer| layer.len() == V5_REAL_HOST_QUERY_COUNT));
        let z = core::array::from_fn(|coordinate| q(100 + coordinate as u32));
        let points = [z, binary_successor_point(&z), xor12_point(&z)];
        let terminal_covector: [QM31; V5_C_ROWS] =
            v5_structured_terminal_covector(&z).try_into().unwrap();
        V5ComponentCFrozenESchedule {
            statement_digest: [0x51; 32],
            transcript_state_after_queries: [0xa7; 32],
            roots: core::array::from_fn(|root| [root as u8 + 1; 32]),
            query_selector: 0,
            queries,
            layer0_fibres: indices.layer0.try_into().unwrap(),
            later_fibres: [
                indices.later[0].clone().try_into().unwrap(),
                indices.later[1].clone().try_into().unwrap(),
                indices.later[2].clone().try_into().unwrap(),
            ],
            points,
            terminal_covector,
            inactive_masks: atomic_state_only_copy_inactive_row_masks_v3(),
            pivot_row: v5_c_pivot_row(),
        }
    }

    #[test]
    fn collision_shape_is_rejected_before_matrix_generation() {
        let queries = core::array::from_fn(|index| index as u32);
        let indices =
            derive_circle_line_query_indices_for_count(&queries, V5_LAYER_ZERO_LEAVES).unwrap();
        assert_eq!(
            validate_query_shape(&queries, &indices),
            Err(V5ComponentCEmatError::CollisionShape {
                layer: 1,
                expected: V5_REAL_HOST_QUERY_COUNT,
                actual: 5,
            })
        );

        let mut drift = indices;
        drift.layer0.swap(0, 1);
        assert_eq!(
            validate_query_shape(&queries, &drift),
            Err(V5ComponentCEmatError::OpeningIndexDrift)
        );
    }

    #[test]
    fn sparse_matrix_reference_linearity_and_artifact_teeth_are_exact() {
        let schedule = synthetic_schedule();
        let matrix = V5ComponentCEmat::generate(&schedule).unwrap();
        assert_eq!(matrix.canonical_bytes().len(), V5_C_EMAT_MATRIX_BYTES);
        assert_eq!(schedule.pivot_row, 0);

        let kats = build_component_c_emat_kats(&schedule, &matrix).unwrap();
        assert_eq!(kats.reference_parity_cases, 9);
        assert_eq!(kats.linearity_checks, 2);

        let matrix_bytes = matrix.canonical_bytes();
        for (index, bytes) in matrix_bytes.chunks_exact(16).enumerate() {
            let decoded = QM31::from_le_bytes(bytes).unwrap();
            assert_eq!(decoded, matrix.entries[index]);
        }
        for row in 0..V5_C_EMAT_ROWS {
            for column in [0, 137, V5_C_EMAT_COLUMNS - 1] {
                let start = (row * V5_C_EMAT_COLUMNS + column) * 16;
                assert_eq!(
                    QM31::from_le_bytes(&matrix_bytes[start..start + 16]).unwrap(),
                    matrix.entry(row, column)
                );
            }
        }

        let artifact = matrix.encode_artifact(&schedule);
        assert_eq!(artifact, matrix.encode_artifact(&schedule));
        let view = validate_component_c_emat_artifact(&artifact).unwrap();
        assert_eq!(view.schedule_sha256, schedule.sha256());
        assert_eq!(view.matrix_sha256, matrix.sha256());
        assert_eq!(view.matrix_bytes.len(), V5_C_EMAT_MATRIX_BYTES);

        let mut schedule_mutation = artifact.clone();
        schedule_mutation[V5_C_EMAT_ARTIFACT_HEADER_BYTES] ^= 1;
        assert!(matches!(
            validate_component_c_emat_artifact(&schedule_mutation),
            Err(V5ComponentCEmatError::ArtifactHash {
                section: "schedule"
            })
        ));

        let mut matrix_mutation = artifact.clone();
        *matrix_mutation.last_mut().unwrap() ^= 1;
        assert!(matches!(
            validate_component_c_emat_artifact(&matrix_mutation),
            Err(V5ComponentCEmatError::ArtifactHash { section: "matrix" })
        ));

        // A recomputed section hash must not launder a non-canonical field
        // limb into an otherwise well-shaped artifact.
        let mut noncanonical_matrix = artifact.clone();
        let matrix_start = V5_C_EMAT_ARTIFACT_HEADER_BYTES + V5_C_EMAT_SCHEDULE_BYTES;
        noncanonical_matrix[matrix_start..matrix_start + 4].copy_from_slice(&P.to_le_bytes());
        let matrix_hash = crate::host_hashv(&[
            MATRIX_HASH_DOMAIN,
            &noncanonical_matrix[matrix_start..matrix_start + V5_C_EMAT_MATRIX_BYTES],
        ]);
        noncanonical_matrix[96..128].copy_from_slice(&matrix_hash);
        assert_eq!(
            validate_component_c_emat_artifact(&noncanonical_matrix),
            Err(V5ComponentCEmatError::ArtifactShape)
        );

        let mut shape_mutation = artifact.clone();
        shape_mutation[16..20].copy_from_slice(&75u32.to_le_bytes());
        assert_eq!(
            validate_component_c_emat_artifact(&shape_mutation),
            Err(V5ComponentCEmatError::ArtifactShape)
        );

        let mut pivot_header_mutation = artifact.clone();
        pivot_header_mutation[40] ^= 1;
        assert_eq!(
            validate_component_c_emat_artifact(&pivot_header_mutation),
            Err(V5ComponentCEmatError::ArtifactShape)
        );

        let mut trailing = artifact;
        trailing.push(0);
        assert_eq!(
            validate_component_c_emat_artifact(&trailing),
            Err(V5ComponentCEmatError::ArtifactShape)
        );
    }
}
