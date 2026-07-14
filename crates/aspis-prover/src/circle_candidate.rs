//! Host-side encoder and commitment primitives for the M31 circle candidate.
//!
//! This module deliberately stops at deterministic arithmetic and Merkle
//! commitments. It does not parse a proof, alter an accepted wire format,
//! drive a transcript, or make a protocol or security claim.

use aspis_core::circle_fri::{
    evaluate_final_line_tensor_at_query_for_domain_log,
    normalized_circle_to_line_arity4_at_fiber_for_domain_log,
    normalized_line_arity4_at_fiber_for_domain_log, CircleFriError, FIXED_ARITY4_ROUNDS,
};
use aspis_core::circle_prefix::{
    CANDIDATE_FINAL_POLY_LEN, CANDIDATE_FLAGS, CANDIDATE_FOLD_NONCES_LEN, CANDIDATE_LOG_ROWS,
    CANDIDATE_OOD_SAMPLES, CANDIDATE_PREFIX_LEN, CANDIDATE_PREFIX_OFFSETS, CANDIDATE_ROUND_COUNT,
    CANDIDATE_STATEMENT_VALUE_COUNT,
};
use aspis_core::field::{qm31_power_table, M31, QM31};
use aspis_core::merkle::{leaf_hash, node_hash, node_hash4};
use aspis_core::params::{FoldPayload, MerkleMode, FINAL_POLY_LOG_LEN};
use aspis_core::proof::{
    Header, HEADER_LEN, M31_CIRCLE_C1_COLUMNS as CORE_C1_COLUMNS, M31_CIRCLE_C1_FIBER_LEN,
    M31_CIRCLE_C2_LAYER_TAG, M31_CIRCLE_COMBINED_LAYER_TAG_BASE, SECOND_PHASE_LEAF_LEN_V4_S2,
    VERSION_V4_S2,
};
use aspis_core::sumcheck::SUMCHECK_COEFFICIENTS;
use aspis_core::HashFn;

pub const TRACE_LOG_SIZE: u32 = 10;
pub const DOMAIN_LOG_SIZE: u32 = 12;
pub const TRACE_LEN: usize = 1usize << TRACE_LOG_SIZE;
pub const CODEWORD_LEN: usize = 1usize << DOMAIN_LOG_SIZE;
pub const FIBER_COUNT: usize = TRACE_LEN;
pub const FIBER_SLOTS: usize = 4;
pub const C1_COLUMNS: usize = CORE_C1_COLUMNS;
pub const C2_COLUMNS: usize = 2;
pub const TOTAL_COLUMNS: usize = C1_COLUMNS + C2_COLUMNS;
pub const C1_LAYER0_LEAF_BYTES: usize = M31_CIRCLE_C1_FIBER_LEN;
pub const C2_LAYER0_LEAF_BYTES: usize = SECOND_PHASE_LEAF_LEN_V4_S2;
pub const COMBINED_LAYER_LEAF_BYTES: usize = 4 * 16;
pub const COMBINED_COMMITTED_LAYERS: usize = 3;
pub const FINAL_EVALUATION_LEN: usize = 16;
pub const FINAL_COEFFICIENT_LEN: usize = 4;

/// Candidate layer-zero tags reserved by the teeth-first integration plan.
pub const M31_CIRCLE_C1_LAYER0_TAG: u8 = M31_CIRCLE_COMBINED_LAYER_TAG_BASE;
pub const M31_CIRCLE_C2_LAYER0_TAG: u8 = M31_CIRCLE_C2_LAYER_TAG;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CircleCandidateError {
    MessageLength {
        expected: usize,
        actual: usize,
    },
    ColumnCount {
        expected: usize,
        actual: usize,
    },
    CodewordLength {
        column: usize,
        expected: usize,
        actual: usize,
    },
    FiberIndex {
        index: usize,
    },
    LeafLength {
        expected: usize,
        actual: usize,
    },
    NonCanonicalM31 {
        offset: usize,
    },
    NonCanonicalQm31 {
        offset: usize,
    },
    CombinedLength {
        expected: usize,
        actual: usize,
    },
    TerminalEvaluationMismatch {
        index: usize,
    },
    Fold(CircleFriError),
}

impl core::fmt::Display for CircleCandidateError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Self::MessageLength { expected, actual } => {
                write!(
                    formatter,
                    "expected {expected} message values, got {actual}"
                )
            }
            Self::ColumnCount { expected, actual } => {
                write!(formatter, "expected {expected} columns, got {actual}")
            }
            Self::CodewordLength {
                column,
                expected,
                actual,
            } => write!(
                formatter,
                "column {column} has {actual} code symbols; expected {expected}"
            ),
            Self::FiberIndex { index } => {
                write!(formatter, "fiber index {index} is outside 0..{FIBER_COUNT}")
            }
            Self::LeafLength { expected, actual } => {
                write!(formatter, "expected {expected} leaf bytes, got {actual}")
            }
            Self::NonCanonicalM31 { offset } => {
                write!(formatter, "non-canonical M31 at leaf byte offset {offset}")
            }
            Self::NonCanonicalQm31 { offset } => {
                write!(formatter, "non-canonical QM31 at leaf byte offset {offset}")
            }
            Self::CombinedLength { expected, actual } => {
                write!(
                    formatter,
                    "expected {expected} combined values, got {actual}"
                )
            }
            Self::TerminalEvaluationMismatch { index } => {
                write!(formatter, "terminal evaluation mismatch at index {index}")
            }
            Self::Fold(error) => write!(formatter, "circle-FRI fold failed: {error:?}"),
        }
    }
}

impl std::error::Error for CircleCandidateError {}

impl From<CircleFriError> for CircleCandidateError {
    fn from(error: CircleFriError) -> Self {
        Self::Fold(error)
    }
}

/// Deterministic commitments after the separately authenticated C1 and C2
/// roots have been gamma-combined. Layers 1, 2, and 3 are committed; the
/// fourth fold produces the sixteen final-domain evaluations checked against
/// the four natural terminal coefficients.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CircleFoldCommitments {
    pub committed_evaluations: [Vec<QM31>; COMBINED_COMMITTED_LAYERS],
    pub committed_leaves: [Vec<[u8; COMBINED_LAYER_LEAF_BYTES]>; COMBINED_COMMITTED_LAYERS],
    pub roots: [[u8; 32]; COMBINED_COMMITTED_LAYERS],
    pub final_evaluations: Vec<QM31>,
    pub final_coefficients: [QM31; FINAL_COEFFICIENT_LEN],
}

#[derive(Clone, Copy)]
struct CirclePoint {
    x: M31,
    y: M31,
}

const CIRCLE_LOG_ORDER: u32 = 31;
const CIRCLE_GENERATOR: CirclePoint = CirclePoint {
    x: M31(2),
    y: M31(1_268_011_823),
};

impl CirclePoint {
    fn identity() -> Self {
        Self {
            x: M31::ONE,
            y: M31::ZERO,
        }
    }

    fn add(self, rhs: Self) -> Self {
        Self {
            x: self.x.mul(rhs.x).sub(self.y.mul(rhs.y)),
            y: self.x.mul(rhs.y).add(self.y.mul(rhs.x)),
        }
    }

    fn double(self) -> Self {
        self.add(self)
    }

    fn mul(self, mut scalar: usize) -> Self {
        let mut result = Self::identity();
        let mut power = self;
        while scalar != 0 {
            if scalar & 1 == 1 {
                result = result.add(power);
            }
            power = power.double();
            scalar >>= 1;
        }
        result
    }
}

#[derive(Clone, Copy)]
struct Coset {
    initial: CirclePoint,
    step: CirclePoint,
    log_size: u32,
}

impl Coset {
    fn half_odds(log_size: u32) -> Self {
        let initial_index = 1usize << (CIRCLE_LOG_ORDER - (log_size + 2));
        let step_index = 1usize << (CIRCLE_LOG_ORDER - log_size);
        Self {
            initial: CIRCLE_GENERATOR.mul(initial_index),
            step: CIRCLE_GENERATOR.mul(step_index),
            log_size,
        }
    }

    fn size(self) -> usize {
        1usize << self.log_size
    }

    fn point(self, index: usize) -> CirclePoint {
        self.initial.add(self.step.mul(index))
    }

    fn double(self) -> Self {
        debug_assert!(self.log_size > 0);
        Self {
            initial: self.initial.double(),
            step: self.step.double(),
            log_size: self.log_size - 1,
        }
    }
}

fn bit_reverse_index(index: usize, log_size: u32) -> usize {
    if log_size == 0 {
        0
    } else {
        index.reverse_bits() >> (usize::BITS - log_size)
    }
}

fn bit_reverse<T>(values: &mut [T]) {
    let log_size = values.len().ilog2();
    for index in 0..values.len() {
        let reversed = bit_reverse_index(index, log_size);
        if reversed > index {
            values.swap(index, reversed);
        }
    }
}

fn precompute_twiddles(mut coset: Coset) -> Vec<M31> {
    let mut twiddles = Vec::with_capacity(coset.size());
    while coset.log_size != 0 {
        let layer_start = twiddles.len();
        twiddles.extend((0..coset.size() / 2).map(|index| coset.point(index).x));
        bit_reverse(&mut twiddles[layer_start..]);
        coset = coset.double();
    }
    // Stwo pads its size-(n-1) twiddle tree to n.
    twiddles.push(M31::ONE);
    twiddles
}

fn line_twiddle_layers(twiddles: &[M31], line_log_size: u32) -> Vec<Vec<M31>> {
    let mut layers = (0..line_log_size)
        .map(|layer| {
            let len = 1usize << layer;
            twiddles[twiddles.len() - 2 * len..twiddles.len() - len].to_vec()
        })
        .collect::<Vec<_>>();
    layers.reverse();
    layers
}

fn circle_twiddles(first_line_layer: &[M31]) -> Vec<M31> {
    let mut result = Vec::with_capacity(first_line_layer.len() * 2);
    for pair in first_line_layer.chunks_exact(2) {
        let x = pair[0];
        let y = pair[1];
        result.extend([y, y.neg(), x.neg(), x]);
    }
    result
}

fn fft_layer_m31(values: &mut [M31], layer: usize, block: usize, twiddle: M31) {
    for lane in 0..(1usize << layer) {
        let index0 = (block << (layer + 1)) + lane;
        let index1 = index0 + (1usize << layer);
        let left = values[index0];
        let weighted_right = values[index1].mul(twiddle);
        values[index0] = left.add(weighted_right);
        values[index1] = left.sub(weighted_right);
    }
}

fn fft_layer_qm31(values: &mut [QM31], layer: usize, block: usize, twiddle: M31) {
    for lane in 0..(1usize << layer) {
        let index0 = (block << (layer + 1)) + lane;
        let index1 = index0 + (1usize << layer);
        let left = values[index0];
        let weighted_right = values[index1].mul_m31(twiddle);
        values[index0] = left.add(weighted_right);
        values[index1] = left.sub(weighted_right);
    }
}

/// Reusable canonical log-12 circle encoder. Twiddles are built once so all
/// 49 C1 columns and both C2 helpers share the same domain preparation.
#[derive(Clone, Debug)]
pub struct CircleEncoder {
    domain_log_size: u32,
    codeword_len: usize,
    line_layers: Vec<Vec<M31>>,
    first_circle_layer: Vec<M31>,
}

impl CircleEncoder {
    pub fn new() -> Self {
        Self::new_for_domain_log(DOMAIN_LOG_SIZE)
    }

    pub fn new_for_domain_log(domain_log_size: u32) -> Self {
        assert!(domain_log_size >= TRACE_LOG_SIZE + 2);
        let half_coset = Coset::half_odds(domain_log_size - 1);
        let twiddles = precompute_twiddles(half_coset);
        let line_layers = line_twiddle_layers(&twiddles, domain_log_size - 1);
        let first_circle_layer = circle_twiddles(&line_layers[0]);
        Self {
            domain_log_size,
            codeword_len: 1usize << domain_log_size,
            line_layers,
            first_circle_layer,
        }
    }

    pub fn domain_log_size(&self) -> u32 {
        self.domain_log_size
    }

    pub fn codeword_len(&self) -> usize {
        self.codeword_len
    }

    /// One entry of the exact circle-FFT encoding matrix. This follows the
    /// unique butterfly path from a unit message row to one codeword index
    /// and is used by host rank gates that need a few authenticated positions
    /// on very large blowup domains. It is algebraically identical to
    /// `encode_c1_message(e_row)[codeword_index]` without allocating the full
    /// word.
    pub(crate) fn encode_c1_basis_value(
        &self,
        row: usize,
        codeword_index: usize,
    ) -> Result<M31, CircleCandidateError> {
        if row >= TRACE_LEN {
            return Err(CircleCandidateError::MessageLength {
                expected: TRACE_LEN,
                actual: row + 1,
            });
        }
        if codeword_index >= self.codeword_len {
            return Err(CircleCandidateError::FiberIndex {
                index: codeword_index,
            });
        }
        let mut value = M31::ONE;
        for bit in 0..TRACE_LOG_SIZE {
            if (row >> bit) & 1 == 0 {
                continue;
            }
            let (twiddle, output_bit) = if bit == 0 {
                (
                    self.first_circle_layer[codeword_index >> 1],
                    codeword_index & 1,
                )
            } else {
                (
                    self.line_layers[(bit - 1) as usize][codeword_index >> (bit + 1)],
                    (codeword_index >> bit) & 1,
                )
            };
            value = value.mul(if output_bit == 0 {
                twiddle
            } else {
                twiddle.neg()
            });
        }
        Ok(value)
    }

    /// One exact encoding-matrix entry for a host-only power-of-two message
    /// prefix. This is the sparse counterpart of `encode_c2_message_prefix`
    /// and avoids materializing a large diagnostic codeword when only queried
    /// fibers are needed. Production message tables remain fixed at
    /// `TRACE_LOG_SIZE` and do not call this method.
    pub(crate) fn encode_prefix_basis_value(
        &self,
        message_log_size: u32,
        row: usize,
        codeword_index: usize,
    ) -> Result<M31, CircleCandidateError> {
        let message_len =
            1usize
                .checked_shl(message_log_size)
                .ok_or(CircleCandidateError::MessageLength {
                    expected: self.codeword_len / 4,
                    actual: usize::MAX,
                })?;
        if message_log_size + 2 > self.domain_log_size || row >= message_len {
            return Err(CircleCandidateError::MessageLength {
                expected: message_len,
                actual: row.saturating_add(1),
            });
        }
        if codeword_index >= self.codeword_len {
            return Err(CircleCandidateError::FiberIndex {
                index: codeword_index,
            });
        }
        let mut value = M31::ONE;
        for bit in 0..message_log_size {
            if (row >> bit) & 1 == 0 {
                continue;
            }
            let (twiddle, output_bit) = if bit == 0 {
                (
                    self.first_circle_layer[codeword_index >> 1],
                    codeword_index & 1,
                )
            } else {
                (
                    self.line_layers[(bit - 1) as usize][codeword_index >> (bit + 1)],
                    (codeword_index >> bit) & 1,
                )
            };
            value = value.mul(if output_bit == 0 {
                twiddle
            } else {
                twiddle.neg()
            });
        }
        Ok(value)
    }

    /// Encode one direct M31 message table. Input index order is preserved:
    /// no AIR interpolation, IFFT, or coefficient permutation is performed.
    pub fn encode_c1_message(&self, message: &[M31]) -> Result<Vec<M31>, CircleCandidateError> {
        if message.len() != TRACE_LEN {
            return Err(CircleCandidateError::MessageLength {
                expected: TRACE_LEN,
                actual: message.len(),
            });
        }
        let mut values = vec![M31::ZERO; self.codeword_len];
        values[..TRACE_LEN].copy_from_slice(message);
        for (layer, twiddles) in self.line_layers.iter().enumerate().rev() {
            for (block, twiddle) in twiddles.iter().copied().enumerate() {
                fft_layer_m31(&mut values, layer + 1, block, twiddle);
            }
        }
        for (block, twiddle) in self.first_circle_layer.iter().copied().enumerate() {
            fft_layer_m31(&mut values, 0, block, twiddle);
        }
        Ok(values)
    }

    /// Encode one QM31 helper coordinatewise using the same M31 twiddles.
    pub fn encode_c2_message(&self, message: &[QM31]) -> Result<Vec<QM31>, CircleCandidateError> {
        if message.len() != TRACE_LEN {
            return Err(CircleCandidateError::MessageLength {
                expected: TRACE_LEN,
                actual: message.len(),
            });
        }
        let mut values = vec![QM31::ZERO; self.codeword_len];
        values[..TRACE_LEN].copy_from_slice(message);
        for (layer, twiddles) in self.line_layers.iter().enumerate().rev() {
            for (block, twiddle) in twiddles.iter().copied().enumerate() {
                fft_layer_qm31(&mut values, layer + 1, block, twiddle);
            }
        }
        for (block, twiddle) in self.first_circle_layer.iter().copied().enumerate() {
            fft_layer_qm31(&mut values, 0, block, twiddle);
        }
        Ok(values)
    }

    /// Host-only generalized prefix encoder used by code-rate and hiding
    /// probes. Production message tables remain pinned to `TRACE_LEN`; this
    /// method permits a larger power-of-two message prefix while preserving
    /// the same circle FFT and requiring at least rate 1/4.
    pub(crate) fn encode_c2_message_prefix(
        &self,
        message: &[QM31],
    ) -> Result<Vec<QM31>, CircleCandidateError> {
        if !message.len().is_power_of_two() || message.len() > self.codeword_len / 4 {
            return Err(CircleCandidateError::MessageLength {
                expected: self.codeword_len / 4,
                actual: message.len(),
            });
        }
        let mut values = vec![QM31::ZERO; self.codeword_len];
        values[..message.len()].copy_from_slice(message);
        for (layer, twiddles) in self.line_layers.iter().enumerate().rev() {
            for (block, twiddle) in twiddles.iter().copied().enumerate() {
                fft_layer_qm31(&mut values, layer + 1, block, twiddle);
            }
        }
        for (block, twiddle) in self.first_circle_layer.iter().copied().enumerate() {
            fft_layer_qm31(&mut values, 0, block, twiddle);
        }
        Ok(values)
    }

    pub fn encode_c1_columns(
        &self,
        messages: &[Vec<M31>],
    ) -> Result<Vec<Vec<M31>>, CircleCandidateError> {
        if messages.len() != C1_COLUMNS {
            return Err(CircleCandidateError::ColumnCount {
                expected: C1_COLUMNS,
                actual: messages.len(),
            });
        }
        messages
            .iter()
            .map(|message| self.encode_c1_message(message))
            .collect()
    }

    pub fn encode_c2_columns(
        &self,
        messages: &[Vec<QM31>],
    ) -> Result<Vec<Vec<QM31>>, CircleCandidateError> {
        if messages.len() != C2_COLUMNS {
            return Err(CircleCandidateError::ColumnCount {
                expected: C2_COLUMNS,
                actual: messages.len(),
            });
        }
        messages
            .iter()
            .map(|message| self.encode_c2_message(message))
            .collect()
    }
}

impl Default for CircleEncoder {
    fn default() -> Self {
        Self::new()
    }
}

fn validate_codewords<T>(
    codewords: &[Vec<T>],
    expected_columns: usize,
    expected_codeword_len: usize,
) -> Result<(), CircleCandidateError> {
    if codewords.len() != expected_columns {
        return Err(CircleCandidateError::ColumnCount {
            expected: expected_columns,
            actual: codewords.len(),
        });
    }
    for (column, codeword) in codewords.iter().enumerate() {
        if codeword.len() != expected_codeword_len {
            return Err(CircleCandidateError::CodewordLength {
                column,
                expected: expected_codeword_len,
                actual: codeword.len(),
            });
        }
    }
    Ok(())
}

/// Build one exact 784-byte C1 leaf in slot-major, column-minor order.
pub fn c1_layer0_leaf(
    encoded_columns: &[Vec<M31>],
    fiber: usize,
) -> Result<[u8; C1_LAYER0_LEAF_BYTES], CircleCandidateError> {
    validate_codewords(encoded_columns, C1_COLUMNS, CODEWORD_LEN)?;
    if fiber >= FIBER_COUNT {
        return Err(CircleCandidateError::FiberIndex { index: fiber });
    }
    Ok(c1_layer0_leaf_validated(encoded_columns, fiber))
}

fn c1_layer0_leaf_validated(
    encoded_columns: &[Vec<M31>],
    fiber: usize,
) -> [u8; C1_LAYER0_LEAF_BYTES] {
    let mut leaf = [0u8; C1_LAYER0_LEAF_BYTES];
    let mut offset = 0;
    for slot in 0..FIBER_SLOTS {
        let codeword_index = FIBER_SLOTS * fiber + slot;
        for column in encoded_columns {
            leaf[offset..offset + 4].copy_from_slice(&column[codeword_index].to_le_bytes());
            offset += 4;
        }
    }
    leaf
}

/// Build one exact 128-byte C2 leaf in helper-major, slot-minor order.
pub fn c2_layer0_leaf(
    encoded_helpers: &[Vec<QM31>],
    fiber: usize,
) -> Result<[u8; C2_LAYER0_LEAF_BYTES], CircleCandidateError> {
    validate_codewords(encoded_helpers, C2_COLUMNS, CODEWORD_LEN)?;
    if fiber >= FIBER_COUNT {
        return Err(CircleCandidateError::FiberIndex { index: fiber });
    }
    Ok(c2_layer0_leaf_validated(encoded_helpers, fiber))
}

fn c2_layer0_leaf_validated(
    encoded_helpers: &[Vec<QM31>],
    fiber: usize,
) -> [u8; C2_LAYER0_LEAF_BYTES] {
    let mut leaf = [0u8; C2_LAYER0_LEAF_BYTES];
    let mut offset = 0;
    for helper in encoded_helpers {
        for slot in 0..FIBER_SLOTS {
            let codeword_index = FIBER_SLOTS * fiber + slot;
            helper[codeword_index].write_le_bytes(&mut leaf[offset..offset + 16]);
            offset += 16;
        }
    }
    leaf
}

pub fn c1_layer0_leaves(
    encoded_columns: &[Vec<M31>],
) -> Result<Vec<[u8; C1_LAYER0_LEAF_BYTES]>, CircleCandidateError> {
    c1_layer0_leaves_for_codeword_len(encoded_columns, CODEWORD_LEN)
}

pub fn c1_layer0_leaves_for_codeword_len(
    encoded_columns: &[Vec<M31>],
    codeword_len: usize,
) -> Result<Vec<[u8; C1_LAYER0_LEAF_BYTES]>, CircleCandidateError> {
    validate_codewords(encoded_columns, C1_COLUMNS, codeword_len)?;
    Ok((0..codeword_len / FIBER_SLOTS)
        .map(|fiber| c1_layer0_leaf_validated(encoded_columns, fiber))
        .collect())
}

pub fn c2_layer0_leaves(
    encoded_helpers: &[Vec<QM31>],
) -> Result<Vec<[u8; C2_LAYER0_LEAF_BYTES]>, CircleCandidateError> {
    c2_layer0_leaves_for_codeword_len(encoded_helpers, CODEWORD_LEN)
}

pub fn c2_layer0_leaves_for_codeword_len(
    encoded_helpers: &[Vec<QM31>],
    codeword_len: usize,
) -> Result<Vec<[u8; C2_LAYER0_LEAF_BYTES]>, CircleCandidateError> {
    validate_codewords(encoded_helpers, C2_COLUMNS, codeword_len)?;
    Ok((0..codeword_len / FIBER_SLOTS)
        .map(|fiber| c2_layer0_leaf_validated(encoded_helpers, fiber))
        .collect())
}

fn radix4_root<const N: usize>(leaves: &[[u8; N]], layer_tag: u8, hash: HashFn) -> [u8; 32] {
    debug_assert!(!leaves.is_empty());
    debug_assert!(leaves.len().is_power_of_two());
    let mut level = leaves
        .iter()
        .map(|leaf| leaf_hash(hash, layer_tag, leaf))
        .collect::<Vec<_>>();
    while level.len() > 1 {
        level = if level.len() == 2 {
            vec![node_hash(hash, &level[0], &level[1])]
        } else {
            debug_assert_eq!(level.len() % 4, 0);
            level
                .chunks_exact(4)
                .map(|children| node_hash4(hash, children.try_into().unwrap()))
                .collect()
        };
    }
    level[0]
}

/// Commit all C1 leaves under the candidate-only layer tag `0x40`.
pub fn c1_layer0_root(
    encoded_columns: &[Vec<M31>],
    hash: HashFn,
) -> Result<[u8; 32], CircleCandidateError> {
    let leaves = c1_layer0_leaves(encoded_columns)?;
    Ok(radix4_root(&leaves, M31_CIRCLE_C1_LAYER0_TAG, hash))
}

pub fn c1_layer0_root_for_codeword_len(
    encoded_columns: &[Vec<M31>],
    codeword_len: usize,
    hash: HashFn,
) -> Result<[u8; 32], CircleCandidateError> {
    let leaves = c1_layer0_leaves_for_codeword_len(encoded_columns, codeword_len)?;
    Ok(radix4_root(&leaves, M31_CIRCLE_C1_LAYER0_TAG, hash))
}

/// Commit both C2 helpers in one tree under the candidate-only tag `0xc0`.
pub fn c2_layer0_root(
    encoded_helpers: &[Vec<QM31>],
    hash: HashFn,
) -> Result<[u8; 32], CircleCandidateError> {
    let leaves = c2_layer0_leaves(encoded_helpers)?;
    Ok(radix4_root(&leaves, M31_CIRCLE_C2_LAYER0_TAG, hash))
}

pub fn c2_layer0_root_for_codeword_len(
    encoded_helpers: &[Vec<QM31>],
    codeword_len: usize,
    hash: HashFn,
) -> Result<[u8; 32], CircleCandidateError> {
    let leaves = c2_layer0_leaves_for_codeword_len(encoded_helpers, codeword_len)?;
    Ok(radix4_root(&leaves, M31_CIRCLE_C2_LAYER0_TAG, hash))
}

/// Canonically decode and gamma-combine one opened four-slot C1/C2 fiber.
/// C1 uses powers 0..48; h1 and h2 use powers 49 and 50 respectively.
pub fn gamma_combine_opened_fiber(
    c1_leaf: &[u8],
    c2_leaf: &[u8],
    gamma: QM31,
) -> Result<[QM31; FIBER_SLOTS], CircleCandidateError> {
    if c1_leaf.len() != C1_LAYER0_LEAF_BYTES {
        return Err(CircleCandidateError::LeafLength {
            expected: C1_LAYER0_LEAF_BYTES,
            actual: c1_leaf.len(),
        });
    }
    if c2_leaf.len() != C2_LAYER0_LEAF_BYTES {
        return Err(CircleCandidateError::LeafLength {
            expected: C2_LAYER0_LEAF_BYTES,
            actual: c2_leaf.len(),
        });
    }

    let powers = qm31_power_table::<TOTAL_COLUMNS>(gamma);
    let mut combined = [QM31::ZERO; FIBER_SLOTS];
    for (slot, value) in combined.iter_mut().enumerate() {
        for (column, power) in powers[..C1_COLUMNS].iter().copied().enumerate() {
            let offset = (slot * C1_COLUMNS + column) * 4;
            let bytes: [u8; 4] = c1_leaf[offset..offset + 4].try_into().unwrap();
            let symbol = M31::from_le_bytes(bytes)
                .ok_or(CircleCandidateError::NonCanonicalM31 { offset })?;
            *value = value.add(power.mul_m31(symbol));
        }
    }
    for helper in 0..C2_COLUMNS {
        for (slot, value) in combined.iter_mut().enumerate() {
            let offset = (helper * FIBER_SLOTS + slot) * 16;
            let symbol = QM31::from_le_bytes(&c2_leaf[offset..offset + 16])
                .ok_or(CircleCandidateError::NonCanonicalQm31 { offset })?;
            *value = value.add(powers[C1_COLUMNS + helper].mul(symbol));
        }
    }
    Ok(combined)
}

/// Gamma-combine all 49 direct M31 codewords and both QM31 helper codewords
/// in exactly the same power order as [`gamma_combine_opened_fiber`].
pub fn gamma_combine_codewords(
    encoded_columns: &[Vec<M31>],
    encoded_helpers: &[Vec<QM31>],
    gamma: QM31,
) -> Result<Vec<QM31>, CircleCandidateError> {
    gamma_combine_codewords_for_len(encoded_columns, encoded_helpers, gamma, CODEWORD_LEN)
}

pub fn gamma_combine_codewords_for_len(
    encoded_columns: &[Vec<M31>],
    encoded_helpers: &[Vec<QM31>],
    gamma: QM31,
    codeword_len: usize,
) -> Result<Vec<QM31>, CircleCandidateError> {
    validate_codewords(encoded_columns, C1_COLUMNS, codeword_len)?;
    validate_codewords(encoded_helpers, C2_COLUMNS, codeword_len)?;
    let powers = qm31_power_table::<TOTAL_COLUMNS>(gamma);
    let mut combined = vec![QM31::ZERO; codeword_len];
    for (column, power) in encoded_columns
        .iter()
        .zip(powers[..C1_COLUMNS].iter().copied())
    {
        for (target, symbol) in combined.iter_mut().zip(column) {
            *target = target.add(power.mul_m31(*symbol));
        }
    }
    for (helper, power) in encoded_helpers
        .iter()
        .zip(powers[C1_COLUMNS..].iter().copied())
    {
        for (target, symbol) in combined.iter_mut().zip(helper) {
            *target = target.add(power.mul(*symbol));
        }
    }
    Ok(combined)
}

/// Validate the fixed 49-plus-two natural message-table shape.
fn validate_message_tables(
    c1_messages: &[Vec<M31>],
    c2_messages: &[Vec<QM31>],
) -> Result<(), CircleCandidateError> {
    if c1_messages.len() != C1_COLUMNS {
        return Err(CircleCandidateError::ColumnCount {
            expected: C1_COLUMNS,
            actual: c1_messages.len(),
        });
    }
    if c2_messages.len() != C2_COLUMNS {
        return Err(CircleCandidateError::ColumnCount {
            expected: C2_COLUMNS,
            actual: c2_messages.len(),
        });
    }
    for message in c1_messages {
        if message.len() != TRACE_LEN {
            return Err(CircleCandidateError::MessageLength {
                expected: TRACE_LEN,
                actual: message.len(),
            });
        }
    }
    for message in c2_messages {
        if message.len() != TRACE_LEN {
            return Err(CircleCandidateError::MessageLength {
                expected: TRACE_LEN,
                actual: message.len(),
            });
        }
    }
    Ok(())
}

/// Gamma-combine the corresponding natural MLE message tables. This is the
/// relation-side vector; unlike later `LinePoly` coefficient storage it is
/// never bit-reversed in place.
pub fn gamma_combine_messages(
    c1_messages: &[Vec<M31>],
    c2_messages: &[Vec<QM31>],
    gamma: QM31,
) -> Result<Vec<QM31>, CircleCandidateError> {
    validate_message_tables(c1_messages, c2_messages)?;

    let powers = qm31_power_table::<TOTAL_COLUMNS>(gamma);
    let mut combined = vec![QM31::ZERO; TRACE_LEN];
    for (column, power) in c1_messages.iter().zip(powers[..C1_COLUMNS].iter().copied()) {
        for (target, coefficient) in combined.iter_mut().zip(column) {
            *target = target.add(power.mul_m31(*coefficient));
        }
    }
    for (helper, power) in c2_messages.iter().zip(powers[C1_COLUMNS..].iter().copied()) {
        for (target, coefficient) in combined.iter_mut().zip(helper) {
            *target = target.add(power.mul(*coefficient));
        }
    }
    Ok(combined)
}

/// Derive the second public MLE point by flipping exactly the two low row
/// coordinates under Aspis's big-endian variable convention.
pub fn xor11_point(z: &[QM31; TRACE_LOG_SIZE as usize]) -> [QM31; TRACE_LOG_SIZE as usize] {
    let mut second = *z;
    for coordinate in &mut second[TRACE_LOG_SIZE as usize - 2..] {
        *coordinate = QM31::ONE.sub(*coordinate);
    }
    second
}

/// Evaluate all 49 C1 columns and both C2 helpers at `z` and `xor11(z)` in
/// fixed point-major, column-major order. These are the exact 102 values
/// absorbed before gamma by the candidate prefix schedule.
pub fn candidate_statement_evaluations(
    c1_messages: &[Vec<M31>],
    c2_messages: &[Vec<QM31>],
    z: &[QM31; TRACE_LOG_SIZE as usize],
) -> Result<[QM31; CANDIDATE_STATEMENT_VALUE_COUNT], CircleCandidateError> {
    // Reuse the full shape check without duplicating a second error surface.
    validate_message_tables(c1_messages, c2_messages)?;
    let points = [*z, xor11_point(z)];
    let mut evaluations = [QM31::ZERO; CANDIDATE_STATEMENT_VALUE_COUNT];
    let mut output = 0usize;
    for point in points {
        for column in c1_messages {
            evaluations[output] = super::multilinear_eval(column, &point);
            output += 1;
        }
        for helper in c2_messages {
            evaluations[output] = super::multilinear_eval_extension(helper, &point);
            output += 1;
        }
    }
    debug_assert_eq!(output, CANDIDATE_STATEMENT_VALUE_COUNT);
    Ok(evaluations)
}

/// Production payment evaluations use the frozen XOR-11 row permutation,
/// which toggles row-index bits 0, 1, and 3. The legacy candidate fixture
/// above toggles only bits 0 and 1 and remains pinned for its diagnostics.
pub fn candidate_payment_statement_evaluations(
    c1_messages: &[Vec<M31>],
    c2_messages: &[Vec<QM31>],
    z: &[QM31; TRACE_LOG_SIZE as usize],
) -> Result<[QM31; CANDIDATE_STATEMENT_VALUE_COUNT], CircleCandidateError> {
    validate_message_tables(c1_messages, c2_messages)?;
    let points = [*z, aspis_statement::xor11_point(z)];
    let mut evaluations = [QM31::ZERO; CANDIDATE_STATEMENT_VALUE_COUNT];
    let mut output = 0usize;
    for point in points {
        for column in c1_messages {
            evaluations[output] = super::multilinear_eval(column, &point);
            output += 1;
        }
        for helper in c2_messages {
            evaluations[output] = super::multilinear_eval_extension(helper, &point);
            output += 1;
        }
    }
    debug_assert_eq!(output, CANDIDATE_STATEMENT_VALUE_COUNT);
    Ok(evaluations)
}

/// Gamma-compress each point's 51 statement values with powers `0..=50`.
pub fn gamma_combine_statement_evaluations(
    evaluations: &[QM31; CANDIDATE_STATEMENT_VALUE_COUNT],
    gamma: QM31,
) -> [QM31; 2] {
    let powers = qm31_power_table::<TOTAL_COLUMNS>(gamma);
    core::array::from_fn(|point| {
        evaluations[point * TOTAL_COLUMNS..(point + 1) * TOTAL_COLUMNS]
            .iter()
            .zip(powers.iter().copied())
            .fold(QM31::ZERO, |sum, (value, power)| sum.add(power.mul(*value)))
    })
}

pub(crate) fn combined_layer_leaves(values: &[QM31]) -> Vec<[u8; COMBINED_LAYER_LEAF_BYTES]> {
    debug_assert_eq!(values.len() % FIBER_SLOTS, 0);
    values
        .chunks_exact(FIBER_SLOTS)
        .map(|slots| {
            let mut leaf = [0u8; COMBINED_LAYER_LEAF_BYTES];
            for (slot, value) in slots.iter().enumerate() {
                value.write_le_bytes(&mut leaf[slot * 16..slot * 16 + 16]);
            }
            leaf
        })
        .collect()
}

pub(crate) fn fold_adjacent_natural_arity4(values: &[QM31], alpha: QM31) -> Vec<QM31> {
    let alpha_squared = alpha.square();
    let alpha_cubed = alpha_squared.mul(alpha);
    values
        .chunks_exact(FIBER_SLOTS)
        .map(|chunk| {
            chunk[0]
                .add(alpha.mul(chunk[1]))
                .add(alpha_squared.mul(chunk[2]))
                .add(alpha_cubed.mul(chunk[3]))
        })
        .collect()
}

/// Fold one codeword layer in the fixed circle-then-line candidate schedule.
///
/// This is exposed inside the prover crate so the sequential prefix builder
/// can commit a layer before sampling the next layer's OOD challenges. It is
/// the same arithmetic used by [`build_fold_commitments`].
pub(crate) fn fold_candidate_codeword_round_for_domain_log(
    evaluations: &[QM31],
    alpha: QM31,
    round: usize,
    domain_log_size: u32,
) -> Result<Vec<QM31>, CircleCandidateError> {
    let expected = (1usize << domain_log_size) >> (2 * round);
    if round >= FIXED_ARITY4_ROUNDS as usize || evaluations.len() != expected {
        return Err(CircleCandidateError::CombinedLength {
            expected,
            actual: evaluations.len(),
        });
    }
    evaluations
        .chunks_exact(FIBER_SLOTS)
        .enumerate()
        .map(|(fiber, values)| {
            let values: [QM31; FIBER_SLOTS] = values.try_into().unwrap();
            if round == 0 {
                normalized_circle_to_line_arity4_at_fiber_for_domain_log(
                    values,
                    alpha,
                    domain_log_size,
                    fiber,
                )
            } else {
                normalized_line_arity4_at_fiber_for_domain_log(
                    values,
                    alpha,
                    domain_log_size,
                    round as u8,
                    fiber,
                )
            }
        })
        .collect::<Result<Vec<_>, _>>()
        .map_err(Into::into)
}

/// Commit the already-folded values for candidate layer `1..=3`.
pub(crate) fn combined_candidate_layer_root_for_domain_log(
    evaluations: &[QM31],
    layer: usize,
    domain_log_size: u32,
    hash: HashFn,
) -> Result<[u8; 32], CircleCandidateError> {
    let expected = (1usize << domain_log_size) >> (2 * layer);
    if !(1..=COMBINED_COMMITTED_LAYERS).contains(&layer) || evaluations.len() != expected {
        return Err(CircleCandidateError::CombinedLength {
            expected,
            actual: evaluations.len(),
        });
    }
    let leaves = combined_layer_leaves(evaluations);
    Ok(radix4_root(
        &leaves,
        M31_CIRCLE_COMBINED_LAYER_TAG_BASE + layer as u8,
        hash,
    ))
}

/// Fold one combined log-12 circle codeword through the four fixed arity-4
/// rounds, commit the three intervening line layers, and cross-check the
/// terminal evaluations against the folded natural coefficient tensor.
pub fn build_fold_commitments(
    combined_codeword: &[QM31],
    combined_message: &[QM31],
    alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
    hash: HashFn,
) -> Result<CircleFoldCommitments, CircleCandidateError> {
    build_fold_commitments_for_domain_log(
        combined_codeword,
        combined_message,
        alphas,
        DOMAIN_LOG_SIZE,
        hash,
    )
}

pub fn build_fold_commitments_for_domain_log(
    combined_codeword: &[QM31],
    combined_message: &[QM31],
    alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
    domain_log_size: u32,
    hash: HashFn,
) -> Result<CircleFoldCommitments, CircleCandidateError> {
    let codeword_len = 1usize << domain_log_size;
    if combined_codeword.len() != codeword_len {
        return Err(CircleCandidateError::CombinedLength {
            expected: codeword_len,
            actual: combined_codeword.len(),
        });
    }
    if combined_message.len() != TRACE_LEN {
        return Err(CircleCandidateError::CombinedLength {
            expected: TRACE_LEN,
            actual: combined_message.len(),
        });
    }

    let mut current_evaluations = combined_codeword.to_vec();
    let mut current_coefficients = combined_message.to_vec();
    let mut committed_evaluations: [Vec<QM31>; COMBINED_COMMITTED_LAYERS] =
        core::array::from_fn(|_| Vec::new());
    let mut committed_leaves: [Vec<[u8; COMBINED_LAYER_LEAF_BYTES]>; COMBINED_COMMITTED_LAYERS] =
        core::array::from_fn(|_| Vec::new());
    let mut roots = [[0u8; 32]; COMBINED_COMMITTED_LAYERS];

    for (round, alpha) in alphas.into_iter().enumerate() {
        let next_evaluations = fold_candidate_codeword_round_for_domain_log(
            &current_evaluations,
            alpha,
            round,
            domain_log_size,
        )?;
        current_coefficients = fold_adjacent_natural_arity4(&current_coefficients, alpha);
        current_evaluations = next_evaluations;

        if round < COMBINED_COMMITTED_LAYERS {
            let leaves = combined_layer_leaves(&current_evaluations);
            roots[round] = combined_candidate_layer_root_for_domain_log(
                &current_evaluations,
                round + 1,
                domain_log_size,
                hash,
            )?;
            committed_evaluations[round] = current_evaluations.clone();
            committed_leaves[round] = leaves;
        }
    }

    let expected_final_evaluations = 1usize << (domain_log_size - 8);
    if current_evaluations.len() != expected_final_evaluations {
        return Err(CircleCandidateError::CombinedLength {
            expected: expected_final_evaluations,
            actual: current_evaluations.len(),
        });
    }
    let final_evaluations = current_evaluations;
    let final_coefficients: [QM31; FINAL_COEFFICIENT_LEN] = current_coefficients
        .try_into()
        .map_err(|values: Vec<QM31>| CircleCandidateError::CombinedLength {
            expected: FINAL_COEFFICIENT_LEN,
            actual: values.len(),
        })?;

    // The final line domain has sixteen points. `query = index << 6` maps to
    // each one exactly once under the fixed q -> q>>6 propagation rule.
    for (index, evaluation) in final_evaluations.iter().enumerate() {
        let expected = evaluate_final_line_tensor_at_query_for_domain_log(
            final_coefficients,
            index << 6,
            domain_log_size,
        )?;
        if *evaluation != expected {
            return Err(CircleCandidateError::TerminalEvaluationMismatch { index });
        }
    }

    Ok(CircleFoldCommitments {
        committed_evaluations,
        committed_leaves,
        roots,
        final_evaluations,
        final_coefficients,
    })
}

/// Encode and combine the fixed C1/C2 messages, then build all later
/// commitments. This convenience path is host-only and does not drive a
/// Fiat-Shamir transcript; its `gamma` and `alphas` are explicit inputs.
pub fn encode_and_build_fold_commitments(
    encoder: &CircleEncoder,
    c1_messages: &[Vec<M31>],
    c2_messages: &[Vec<QM31>],
    gamma: QM31,
    alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
    hash: HashFn,
) -> Result<CircleFoldCommitments, CircleCandidateError> {
    let encoded_columns = encoder.encode_c1_columns(c1_messages)?;
    let encoded_helpers = encoder.encode_c2_columns(c2_messages)?;
    let combined_codeword = gamma_combine_codewords(&encoded_columns, &encoded_helpers, gamma)?;
    let combined_message = gamma_combine_messages(c1_messages, c2_messages, gamma)?;
    build_fold_commitments(&combined_codeword, &combined_message, alphas, hash)
}

/// Serialize the exact fixed candidate prefix consumed by
/// `aspis_core::circle_prefix::CandidatePrefix`.
///
/// The caller supplies already-computed roots, statement evaluations, OOD
/// values, sumcheck messages, terminal coefficients, and grinding nonce. This
/// function performs no Fiat-Shamir sampling and selects no two-point rule;
/// its sole purpose is to keep the host writer byte-identical to the core
/// parser before either is connected to proof acceptance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CandidatePrefixMaterial {
    pub c1_root: [u8; 32],
    pub c2_root: [u8; 32],
    pub statement_evaluations: [QM31; CANDIDATE_STATEMENT_VALUE_COUNT],
    pub later_roots: [[u8; 32]; COMBINED_COMMITTED_LAYERS],
    pub ood_values: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    pub sumchecks: [[QM31; SUMCHECK_COEFFICIENTS]; CANDIDATE_ROUND_COUNT],
    pub final_coefficients: [QM31; CANDIDATE_FINAL_POLY_LEN],
    pub nonce: u64,
    pub fold_nonces: [u64; CANDIDATE_ROUND_COUNT],
}

pub fn candidate_prefix_header_for_shape(
    shape: aspis_core::circle_prefix::CandidateProfileShape,
) -> Header {
    Header {
        version: VERSION_V4_S2,
        profile_id: shape.profile_id,
        log_rows: CANDIDATE_LOG_ROWS,
        log_blowup: shape.log_blowup,
        query_count: shape.query_count,
        grinding_bits: shape.grinding_bits,
        fold_payload: FoldPayload::RawFibers as u8,
        merkle_mode: MerkleMode::Radix4MinimalSubtree as u8,
        num_rounds: CANDIDATE_ROUND_COUNT as u32,
        final_poly_log_len: FINAL_POLY_LOG_LEN,
        flags: CANDIDATE_FLAGS,
    }
}

pub fn serialize_candidate_prefix(
    material: &CandidatePrefixMaterial,
) -> [u8; CANDIDATE_PREFIX_LEN] {
    serialize_candidate_prefix_for_shape(
        material,
        aspis_core::circle_prefix::SELECTED_CANDIDATE_SHAPE,
    )
    .try_into()
    .expect("legacy candidate shape has the fixed prefix length")
}

pub fn serialize_candidate_prefix_for_shape(
    material: &CandidatePrefixMaterial,
    shape: aspis_core::circle_prefix::CandidateProfileShape,
) -> Vec<u8> {
    let mut bytes = vec![0u8; shape.prefix_len()];
    let header = candidate_prefix_header_for_shape(shape);
    header.write(&mut bytes[..HEADER_LEN]);
    bytes[CANDIDATE_PREFIX_OFFSETS.c1_root_start..][..32].copy_from_slice(&material.c1_root);
    bytes[CANDIDATE_PREFIX_OFFSETS.c2_root_start..][..32].copy_from_slice(&material.c2_root);

    for (index, value) in material.statement_evaluations.iter().enumerate() {
        let start = CANDIDATE_PREFIX_OFFSETS.statement_evaluations_start + index * 16;
        value.write_le_bytes(&mut bytes[start..start + 16]);
    }
    for layer in 0..CANDIDATE_ROUND_COUNT {
        let offsets = CANDIDATE_PREFIX_OFFSETS.rounds[layer];
        if let Some(root_start) = offsets.root_start {
            bytes[root_start..root_start + 32].copy_from_slice(&material.later_roots[layer - 1]);
        }
        for (sample, value) in material.ood_values[layer].iter().enumerate() {
            let start = offsets.ood_values_start + sample * 16;
            value.write_le_bytes(&mut bytes[start..start + 16]);
        }
        for (coefficient, value) in material.sumchecks[layer].iter().enumerate() {
            let start = offsets.sumcheck_start + coefficient * 16;
            value.write_le_bytes(&mut bytes[start..start + 16]);
        }
    }
    for (coefficient, value) in material.final_coefficients.iter().enumerate() {
        let start = CANDIDATE_PREFIX_OFFSETS.final_polynomial_start + coefficient * 16;
        value.write_le_bytes(&mut bytes[start..start + 16]);
    }
    bytes[CANDIDATE_PREFIX_OFFSETS.nonce_start
        ..CANDIDATE_PREFIX_OFFSETS.nonce_start + core::mem::size_of::<u64>()]
        .copy_from_slice(&material.nonce.to_le_bytes());
    if shape.has_fold_pow() {
        debug_assert_eq!(
            shape.prefix_len(),
            CANDIDATE_PREFIX_LEN + CANDIDATE_FOLD_NONCES_LEN
        );
        for (round, nonce) in material.fold_nonces.iter().enumerate() {
            let start = CANDIDATE_PREFIX_LEN + round * core::mem::size_of::<u64>();
            bytes[start..start + core::mem::size_of::<u64>()].copy_from_slice(&nonce.to_le_bytes());
        }
    }
    bytes
}

/// Extract the four base coordinates of a QM31 value. Kept private so the
/// public C2 API remains representation-independent.
#[cfg(test)]
fn qm31_coordinates(value: QM31) -> [M31; 4] {
    [value.c0.a, value.c0.b, value.c1.a, value.c1.b]
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::CM31;

    #[test]
    fn c2_transform_is_coordinatewise() {
        let encoder = CircleEncoder::new();
        let message = (0..TRACE_LEN)
            .map(|index| QM31 {
                c0: CM31::new(M31(index as u32 + 1), M31(index as u32 + 3)),
                c1: CM31::new(M31(index as u32 + 5), M31(index as u32 + 7)),
            })
            .collect::<Vec<_>>();
        let encoded = encoder.encode_c2_message(&message).unwrap();
        for coordinate in 0..4 {
            let base = message
                .iter()
                .map(|value| qm31_coordinates(*value)[coordinate])
                .collect::<Vec<_>>();
            let expected = encoder.encode_c1_message(&base).unwrap();
            for (actual, expected) in encoded.iter().zip(expected) {
                assert_eq!(qm31_coordinates(*actual)[coordinate], expected);
            }
        }
    }

    #[test]
    fn sparse_basis_entry_matches_full_circle_fft() {
        for domain_log in [12, 15] {
            let encoder = CircleEncoder::new_for_domain_log(domain_log);
            for row in [0usize, 1, 2, 3, 17, 511, 1023] {
                let mut message = vec![M31::ZERO; TRACE_LEN];
                message[row] = M31::ONE;
                let encoded = encoder.encode_c1_message(&message).unwrap();
                for index in [
                    0usize,
                    1,
                    2,
                    3,
                    encoder.codeword_len() / 3,
                    encoder.codeword_len() / 2 + 7,
                    encoder.codeword_len() - 1,
                ] {
                    assert_eq!(
                        encoder.encode_c1_basis_value(row, index).unwrap(),
                        encoded[index],
                        "domain_log={domain_log}, row={row}, index={index}"
                    );
                }
            }
        }
    }
}
