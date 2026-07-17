//! Aspis v5 masking component (A): the block-form circle mask.
//!
//! # Status: PROVISIONAL — first cut, feature-gated (`v5-mask`), NOT in the v4 path
//!
//! This module is a clean-room implementation of the v5 hiding component (A):
//! an aligned block-form circle mask
//!
//! ```text
//!     T̂ = T + B_896 · R,
//! ```
//!
//! where `B_896` is one fixed nonzero tensor-basis factor on the codeword
//! domain and
//!
//! ```text
//!     R ∈ V_b = { p(x) + y·q(x) : deg p, deg q ≤ m-1 }
//! ```
//!
//! is a random block-form circle polynomial with `m = V5_MASK_M = 48`
//! coefficients in each block (`b = V5_MASK_B = 2m = 96` total), sampled from
//! the pinned uniform QM31 rejection sampler (mirroring the rejection rule in
//! `crate::state_only_entropy`).
//!
//! ## What this provisional primitive ESTABLISHES (validated by the tests here)
//!
//! * The block-form mask object `R = p(x) + y·q(x)` and its uniform sampler.
//! * The reserved-row layout: active rows `0..=878`, reserved rows
//!   `896..=991` (exactly `b = 96` rows), carrying the mask. The start is
//!   aligned to a 128-coordinate tensor block.
//! * The agreement property `T̂ == T` on every active row.
//! * Rate preservation: the masked column is a length-`TRACE_LEN` message and
//!   encodes, through the *real* circle encoder, to a rate-1/512 codeword.
//! * The real encoder's basis images satisfy, entry by entry,
//!
//!   ```text
//!       L = diag(B_896(p_i)) · V,
//!   ```
//!
//!   where `V` is the block-form circle Vandermonde model used by
//!   `CircleTMatrixHiding`. Ordinary monomial coefficients are converted to
//!   the encoder's natural line-tensor basis before being placed in the
//!   reserved rows. The tests compare all 96 columns with sparse basis images
//!   emitted by the real circle encoder.
//! * Teeth: the leakage matrix is nonsingular on a sampled valid schedule and
//!   singular on a deliberately duplicated schedule.
//! * The wire fibre geometry: one proof opens 18 disjoint four-point fibres,
//!   i.e. 72 layer-zero positions = 36 x-nodes each with a ±y pair — the
//!   `circleTMatrix` witness shape. The rectangular 72×96 leakage map has
//!   full row rank (certified by the 72×72 witness-shape minor), across
//!   distinct parameter families, and a fibre collision only deletes rows
//!   (the distinct view keeps full row rank). A square `b = 96`
//!   point-evaluation schedule CANNOT be instantiated from one proof; the
//!   square schedule is retained only as an algebraic diagnostic.
//!
//! ## What remains PENDING (NOT established here)
//!
//! * A mechanically checked Rust↔Lean correspondence for the concrete
//!   coefficient table. `CircleTensorBinding.lean` proves the aligned tensor
//!   and conversion algebra, while the tests below check the Rust table and
//!   real encoder; neither alone is a cross-language proof.
//! * The Fiat-Shamir query-index → fibre-position binding and the complete
//!   released-view enumeration. The fibre schedule below models the wire's
//!   orbit geometry; which fibre each FS index selects is not modelled here.
//!   OOD, fold and terminal coordinates are component (C)'s to mask, not
//!   component (A)'s: they are not point-evaluations of the masked lane.
//! * The production field-width binding: the current mask coefficients are
//!   QM31, while semantic C1 columns are M31.
//! * Component (B)'s commitment and verifier wire. The feature-gated
//!   degree-preserving arithmetic primitive lives in `v5_sumcheck_mask`, but
//!   is deliberately not integrated here.
//! * Component (C): the DEEP mask.
//! * The verifier / `Good_spend` changes, and the wire re-enumeration.
//!
//! Nothing in this module is wired into any v4 prover/verifier function; it is
//! reachable only under `--features v5-mask`.

use aspis_core::circle::{
    double_x, secure_circle_point_from_parameter, CirclePointError, SecureCirclePoint,
};
use aspis_core::field::{CM31, M31, QM31};

use crate::circle_candidate::{CircleCandidateError, CircleEncoder};

// ---------------------------------------------------------------------------
// Deliverable 1: constants and the reserved index set.
// ---------------------------------------------------------------------------

/// Trace domain: 1024 rows of the M31 circle code.
pub const V5_TRACE_ROWS: usize = 1024;

/// Codeword domain log size. Rate `TRACE_ROWS / 2^19 = 1024 / 524288 = 1/512`.
pub const V5_DOMAIN_LOG: u32 = 19;

/// Codeword length `2^19` (rate 1/512).
pub const V5_CODEWORD_LEN: usize = 1usize << V5_DOMAIN_LOG;

/// Inclusive upper bound of the active-row sub-domain `H'`.
pub const V5_ACTIVE_ROW_END: usize = 878;

/// Number of active rows carrying the real trace: `0..=878` (879 rows, ≤ 879).
pub const V5_ACTIVE_ROWS: usize = V5_ACTIVE_ROW_END + 1;

/// First reserved row. Alignment to 128 coordinates makes every reserved
/// tensor basis element factor as `B_896 * B_j`, for `0 <= j < 96`.
pub const V5_RESERVED_START: usize = 896;

/// Inclusive last reserved row.
pub const V5_RESERVED_END: usize = V5_RESERVED_START + V5_MASK_B - 1;

/// Width of the aligned tensor block containing the 96 reserved coordinates.
pub const V5_RESERVED_ALIGNMENT: usize = 128;

/// Total reserved rows `b = 2m = 96`.
pub const V5_MASK_B: usize = 96;

/// Per-block mask coefficient count `m = 48` (`deg p, deg q ≤ m-1 = 47`).
pub const V5_MASK_M: usize = 48;

/// Rejection-sampler retry budget per M31 draw (mirrors `state_only_entropy`).
pub const V5_MASK_SAMPLE_RETRY_LIMIT: usize = 16;

// Compile-time pins of the reserved layout.
const _: () = assert!(V5_RESERVED_END - V5_RESERVED_START + 1 == V5_MASK_B);
const _: () = assert!(V5_MASK_B == 2 * V5_MASK_M);
const _: () = assert!(V5_ACTIVE_ROW_END < V5_RESERVED_START);
const _: () = assert!(V5_ACTIVE_ROWS <= 879);
const _: () = assert!(V5_RESERVED_START.is_multiple_of(V5_RESERVED_ALIGNMENT));
const _: () = assert!(V5_MASK_B <= V5_RESERVED_ALIGNMENT);
const _: () = assert!(V5_RESERVED_END < V5_TRACE_ROWS);

/// The active-row sub-domain `H' = 0..=878`.
pub const fn v5_active_rows() -> core::ops::RangeInclusive<usize> {
    0..=V5_ACTIVE_ROW_END
}

/// The reserved index set `896..=991` (carries the mask).
pub const fn v5_reserved_rows() -> core::ops::RangeInclusive<usize> {
    V5_RESERVED_START..=V5_RESERVED_END
}

/// Reserved rows split, in circle-FFT bit-0 order, into a `p`-block (even
/// offset, the pure-`x` part) and a `q`-block (odd offset, the `y·x` part).
/// Returns the message index of the `k`-th coefficient of each block.
#[inline]
pub const fn v5_reserved_p_index(k: usize) -> usize {
    V5_RESERVED_START + 2 * k
}

#[inline]
pub const fn v5_reserved_q_index(k: usize) -> usize {
    V5_RESERVED_START + 2 * k + 1
}

#[inline]
fn qm31_from_m31(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}

// ---------------------------------------------------------------------------
// Deliverable 2: the block-form mask and its uniform sampler.
// ---------------------------------------------------------------------------

/// A random block-form circle polynomial `R = p(x) + y·q(x)` with
/// `deg p, deg q ≤ m-1`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockMask {
    /// `p` block coefficients `p_0 .. p_{m-1}` (the pure-`x` block).
    pub p: [QM31; V5_MASK_M],
    /// `q` block coefficients `q_0 .. q_{m-1}` (the `y·x` block).
    pub q: [QM31; V5_MASK_M],
}

impl BlockMask {
    /// Evaluate `R(x, y) = p(x) + y·q(x)` at a circle point via Horner.
    pub fn evaluate(&self, x: QM31, y: QM31) -> QM31 {
        let mut p_val = QM31::ZERO;
        let mut q_val = QM31::ZERO;
        for k in (0..V5_MASK_M).rev() {
            p_val = p_val.mul(x).add(self.p[k]);
            q_val = q_val.mul(x).add(self.q[k]);
        }
        p_val.add(y.mul(q_val))
    }

    /// Evaluate at a [`SecureCirclePoint`].
    pub fn evaluate_at(&self, point: SecureCirclePoint) -> QM31 {
        self.evaluate(point.x, point.y)
    }
}

/// A source of raw 32-bit words for the rejection sampler. Any Fiat-Shamir /
/// OS entropy expander can implement this; tests use a small xorshift.
pub trait Qm31WordSource {
    fn next_word(&mut self) -> u32;
}

/// Sampler exhausted its retry budget while rejecting non-canonical draws.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MaskSampleExhausted;

/// Draw one canonical M31 with the pinned rejection rule: take the low 31 bits
/// and reject any value `>= P`. Mirrors `state_only_entropy::…::m31`.
fn sample_m31<S: Qm31WordSource>(source: &mut S) -> Result<M31, MaskSampleExhausted> {
    for _ in 0..V5_MASK_SAMPLE_RETRY_LIMIT {
        let candidate = source.next_word() & 0x7fff_ffff;
        if candidate < aspis_core::field::P {
            return Ok(M31(candidate));
        }
    }
    Err(MaskSampleExhausted)
}

/// Draw one uniform QM31 as four rejection-sampled M31 coordinates.
pub(crate) fn sample_qm31<S: Qm31WordSource>(source: &mut S) -> Result<QM31, MaskSampleExhausted> {
    Ok(QM31 {
        c0: CM31::new(sample_m31(source)?, sample_m31(source)?),
        c1: CM31::new(sample_m31(source)?, sample_m31(source)?),
    })
}

/// Sample a block-form mask: `m` QM31 for `p`, then `m` QM31 for `q`.
pub fn sample_block_mask<S: Qm31WordSource>(
    source: &mut S,
) -> Result<BlockMask, MaskSampleExhausted> {
    let mut p = [QM31::ZERO; V5_MASK_M];
    let mut q = [QM31::ZERO; V5_MASK_M];
    for value in p.iter_mut() {
        *value = sample_qm31(source)?;
    }
    for value in q.iter_mut() {
        *value = sample_qm31(source)?;
    }
    Ok(BlockMask { p, q })
}

// ---------------------------------------------------------------------------
// Deliverable 3: the exact aligned tensor basis and coefficient conversion.
// ---------------------------------------------------------------------------

/// Evaluate the natural line tensor basis element
/// `N_i(x) = product(T_(2^bit)(x), bit in bits(i))`.
///
/// The first factor is `x`; subsequent factors use `T_(2n)(x) = 2T_n(x)^2-1`.
pub fn natural_line_basis_value(mut index: usize, x: QM31) -> QM31 {
    let mut value = QM31::ONE;
    let mut factor = x;
    while index != 0 {
        if index & 1 == 1 {
            value = value.mul(factor);
        }
        index >>= 1;
        if index != 0 {
            factor = double_x(factor);
        }
    }
    value
}

/// Evaluate the natural circle tensor basis element `B_i(x,y)`.
///
/// Even coordinates are `N_(i/2)(x)` and odd coordinates are
/// `y * N_(i/2)(x)`, matching the real encoder's bit-zero circle layer.
pub fn natural_circle_basis_value(index: usize, point: SecureCirclePoint) -> QM31 {
    let line = natural_line_basis_value(index >> 1, point.x);
    if index & 1 == 0 {
        line
    } else {
        point.y.mul(line)
    }
}

/// The common tensor factor shared by rows `896..=991`.
pub fn aligned_tensor_factor(point: SecureCirclePoint) -> QM31 {
    natural_circle_basis_value(V5_RESERVED_START, point)
}

/// Ordinary-polynomial expansions of the natural line tensor basis, over M31.
/// Entry `basis[i][j]` is the coefficient of `x^j` in `N_i(x)`.
fn natural_line_basis_polynomials(size: usize) -> Vec<Vec<M31>> {
    let log_size = usize::BITS as usize - (size - 1).leading_zeros() as usize;
    let mut factors = Vec::with_capacity(log_size);
    factors.push(vec![M31::ZERO, M31::ONE]);
    for bit in 1..log_size {
        let previous = &factors[bit - 1];
        let mut squared = vec![M31::ZERO; 2 * previous.len() - 1];
        for (left, &a) in previous.iter().enumerate() {
            for (right, &b) in previous.iter().enumerate() {
                squared[left + right] = squared[left + right].add(a.mul(b));
            }
        }
        for value in &mut squared {
            *value = value.double();
        }
        squared[0] = squared[0].sub(M31::ONE);
        factors.push(squared);
    }

    let mut basis = Vec::with_capacity(size);
    basis.push(vec![M31::ONE]);
    for index in 1..size {
        let bit = index.trailing_zeros() as usize;
        let prefix = &basis[index ^ (1usize << bit)];
        let factor = &factors[bit];
        let mut polynomial = vec![M31::ZERO; prefix.len() + factor.len() - 1];
        for (left, &a) in prefix.iter().enumerate() {
            for (right, &b) in factor.iter().enumerate() {
                polynomial[left + right] = polynomial[left + right].add(a.mul(b));
            }
        }
        basis.push(polynomial);
    }
    basis
}

/// Express each ordinary monomial `x^degree` in the natural line basis.
fn ordinary_monomials_in_natural_line_basis(size: usize) -> Vec<Vec<M31>> {
    let basis = natural_line_basis_polynomials(size);
    (0..size)
        .map(|degree| {
            let mut residual = vec![M31::ZERO; size];
            residual[degree] = M31::ONE;
            let mut coefficients = vec![M31::ZERO; size];
            for pivot in (0..=degree).rev() {
                let diagonal = basis[pivot][pivot];
                let scale = residual[pivot].mul(diagonal.inv());
                coefficients[pivot] = scale;
                for (monomial, &value) in basis[pivot].iter().enumerate() {
                    residual[monomial] = residual[monomial].sub(scale.mul(value));
                }
            }
            debug_assert!(residual.iter().all(|value| *value == M31::ZERO));
            coefficients
        })
        .collect()
}

fn ordinary_to_natural_with_conversion(
    coefficients: &[QM31; V5_MASK_M],
    conversion: &[Vec<M31>],
) -> [QM31; V5_MASK_M] {
    let mut natural = [QM31::ZERO; V5_MASK_M];
    for (degree, coefficient) in coefficients.iter().copied().enumerate() {
        for (index, weight) in conversion[degree].iter().copied().enumerate() {
            natural[index] = natural[index].add(coefficient.mul_m31(weight));
        }
    }
    natural
}

fn block_mask_in_natural_basis(mask: &BlockMask) -> ([QM31; V5_MASK_M], [QM31; V5_MASK_M]) {
    let conversion = ordinary_monomials_in_natural_line_basis(V5_MASK_M);
    (
        ordinary_to_natural_with_conversion(&mask.p, &conversion),
        ordinary_to_natural_with_conversion(&mask.q, &conversion),
    )
}

/// Evaluate the exact reserved coefficient representation at a circle point.
/// This is independent of the compact `B_896 * R` formula used by
/// [`leakage_apply`].
pub fn evaluate_aligned_mask_from_message(mask: &BlockMask, point: SecureCirclePoint) -> QM31 {
    let (natural_p, natural_q) = block_mask_in_natural_basis(mask);
    let mut value = QM31::ZERO;
    for k in 0..V5_MASK_M {
        value = value
            .add(natural_p[k].mul(natural_circle_basis_value(v5_reserved_p_index(k), point)))
            .add(natural_q[k].mul(natural_circle_basis_value(v5_reserved_q_index(k), point)));
    }
    value
}

// ---------------------------------------------------------------------------
// Deliverable 4: build the masked column T̂ and check rate preservation.
// ---------------------------------------------------------------------------

/// Failure envelope for the v5 masking primitives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V5MaskError {
    /// Real column had the wrong length.
    ColumnLength { expected: usize, actual: usize },
    /// The query schedule did not carry exactly `b = 96` points.
    ScheduleLength { expected: usize, actual: usize },
    /// A schedule parameter was singular under the rational circle map.
    CirclePoint(CirclePointError),
    /// The underlying circle encoder rejected the message.
    Encoder(CircleCandidateError),
}

impl From<CircleCandidateError> for V5MaskError {
    fn from(error: CircleCandidateError) -> Self {
        Self::Encoder(error)
    }
}

/// Build the masked column `T̂ = T + B_896·R`.
///
/// The mask occupies exactly the aligned reserved rows, so `T̂` agrees with
/// `T` on every non-reserved row, including every active row. Ordinary
/// monomial coefficients are converted to natural line-tensor coefficients;
/// even offsets carry the pure-`x` block and odd offsets the `y` block.
pub fn mask_column(real: &[QM31], mask: &BlockMask) -> Result<Vec<QM31>, V5MaskError> {
    if real.len() != V5_TRACE_ROWS {
        return Err(V5MaskError::ColumnLength {
            expected: V5_TRACE_ROWS,
            actual: real.len(),
        });
    }
    let mut masked = real.to_vec();
    let (natural_p, natural_q) = block_mask_in_natural_basis(mask);
    for k in 0..V5_MASK_M {
        masked[v5_reserved_p_index(k)] = masked[v5_reserved_p_index(k)].add(natural_p[k]);
        masked[v5_reserved_q_index(k)] = masked[v5_reserved_q_index(k)].add(natural_q[k]);
    }
    Ok(masked)
}

/// A circle encoder pinned to the v5 domain (`log = 19`, rate 1/512).
pub fn v5_encoder() -> CircleEncoder {
    CircleEncoder::new_for_domain_log(V5_DOMAIN_LOG)
}

/// Encode a masked column through the *real* circle encoder and return the
/// codeword. The output length is `V5_CODEWORD_LEN = 2^19`, so rate 1/512 is
/// preserved for any length-`TRACE_ROWS` masked message.
pub fn encode_masked_column(
    encoder: &CircleEncoder,
    masked: &[QM31],
) -> Result<Vec<QM31>, V5MaskError> {
    Ok(encoder.encode_c2_message(masked)?)
}

/// One row of the actual encoder leakage map, in ordinary block-coefficient
/// order `(p_0..p_47, q_0..q_47)`.
///
/// This evaluates the sparse basis images of every converted reserved
/// coefficient. It is intentionally separate from the compact factorisation
/// in [`encoder_factored_leakage_row`].
pub fn encoder_leakage_row(
    encoder: &CircleEncoder,
    codeword_index: usize,
) -> Result<[QM31; V5_MASK_B], V5MaskError> {
    let conversion = ordinary_monomials_in_natural_line_basis(V5_MASK_M);
    let mut row = [QM31::ZERO; V5_MASK_B];
    for degree in 0..V5_MASK_M {
        let mut p = M31::ZERO;
        let mut q = M31::ZERO;
        for (natural, &weight) in conversion[degree].iter().enumerate() {
            p =
                p.add(weight.mul(
                    encoder.encode_c1_basis_value(v5_reserved_p_index(natural), codeword_index)?,
                ));
            q =
                q.add(weight.mul(
                    encoder.encode_c1_basis_value(v5_reserved_q_index(natural), codeword_index)?,
                ));
        }
        row[degree] = qm31_from_m31(p);
        row[V5_MASK_M + degree] = qm31_from_m31(q);
    }
    Ok(row)
}

/// The claimed compact form of [`encoder_leakage_row`]: the common encoder
/// basis image at row 896 times `[1,x,...,x^47,y,...,yx^47]`.
pub fn encoder_factored_leakage_row(
    encoder: &CircleEncoder,
    codeword_index: usize,
) -> Result<[QM31; V5_MASK_B], V5MaskError> {
    let factor = encoder.encode_c1_basis_value(V5_RESERVED_START, codeword_index)?;
    let x = encoder.encode_c1_basis_value(2, codeword_index)?;
    let y = encoder.encode_c1_basis_value(1, codeword_index)?;
    let mut row = [QM31::ZERO; V5_MASK_B];
    let mut power = M31::ONE;
    for degree in 0..V5_MASK_M {
        row[degree] = qm31_from_m31(factor.mul(power));
        row[V5_MASK_M + degree] = qm31_from_m31(factor.mul(y).mul(power));
        power = power.mul(x);
    }
    Ok(row)
}

/// Exclusive message-coordinate bound of the aligned mask. It is below the
/// fixed 1024-coordinate message width, so the rate remains 1/512.
pub const fn v5_mask_message_bound() -> usize {
    V5_RESERVED_END + 1
}

// ---------------------------------------------------------------------------
// Deliverable 5: the leakage matrix and its diag·block-Vandermonde structure.
// ---------------------------------------------------------------------------

/// A square algebraic diagnostic schedule of exactly `b = 96` circle points.
///
/// This is not the production Fiat-Shamir schedule or a released-view
/// enumeration. It exists to test the factorised matrix before that wire is
/// defined.
#[derive(Clone, Debug)]
pub struct MaskQuerySchedule {
    pub points: Vec<SecureCirclePoint>,
}

impl MaskQuerySchedule {
    fn validate(&self) -> Result<(), V5MaskError> {
        if self.points.len() != V5_MASK_B {
            return Err(V5MaskError::ScheduleLength {
                expected: V5_MASK_B,
                actual: self.points.len(),
            });
        }
        Ok(())
    }
}

/// Deterministic diagnostic schedule parameter for row `i`.
fn valid_query_parameter(i: usize) -> QM31 {
    QM31 {
        c0: CM31::new(M31(i as u32 + 3), M31(2)),
        c1: CM31::new(M31(5), M31(i as u32 + 1)),
    }
}

/// A sampled valid query schedule of `b = 96` distinct circle points.
pub fn sampled_valid_schedule() -> Result<MaskQuerySchedule, V5MaskError> {
    let mut points = Vec::with_capacity(V5_MASK_B);
    for i in 0..V5_MASK_B {
        let point = secure_circle_point_from_parameter(valid_query_parameter(i))
            .map_err(V5MaskError::CirclePoint)?;
        points.push(point);
    }
    Ok(MaskQuerySchedule { points })
}

/// A deliberately degenerate schedule with two identical rows.
pub fn degenerate_schedule() -> Result<MaskQuerySchedule, V5MaskError> {
    let mut schedule = sampled_valid_schedule()?;
    schedule.points[1] = schedule.points[0];
    Ok(schedule)
}

/// One block-form circle Vandermonde row at a point:
/// `[x^0 .. x^{m-1}, y·x^0 .. y·x^{m-1}]` (length `b = 2m`).
pub fn block_vandermonde_row(point: SecureCirclePoint) -> [QM31; V5_MASK_B] {
    let mut row = [QM31::ZERO; V5_MASK_B];
    let mut power = QM31::ONE;
    for k in 0..V5_MASK_M {
        row[k] = power;
        row[V5_MASK_M + k] = point.y.mul(power);
        power = power.mul(point.x);
    }
    row
}

/// The block-form circle Vandermonde `V` at the schedule (this is the
/// `circleTMatrix` the Lean `CircleTMatrixHiding` obligation binds).
pub fn block_vandermonde(schedule: &MaskQuerySchedule) -> Result<Vec<Vec<QM31>>, V5MaskError> {
    schedule.validate()?;
    Ok(schedule
        .points
        .iter()
        .map(|point| block_vandermonde_row(*point).to_vec())
        .collect())
}

/// The per-row aligned tensor factors `B_896(p_i)`.
pub fn aligned_factor_diagonal(schedule: &MaskQuerySchedule) -> Result<Vec<QM31>, V5MaskError> {
    schedule.validate()?;
    Ok(schedule
        .points
        .iter()
        .map(|point| aligned_tensor_factor(*point))
        .collect())
}

/// The leakage matrix `L`: the map from the `2m` mask coefficients
/// `(p_0..p_{m-1}, q_0..q_{m-1})` to evaluations of `B_896·R`.
///
/// Row `i` is `B_896(p_i) · [block Vandermonde row at p_i]`, i.e.
/// `L = diag(B_896(p_i)) · V`.
pub fn leakage_matrix_at(schedule: &MaskQuerySchedule) -> Result<Vec<Vec<QM31>>, V5MaskError> {
    schedule.validate()?;
    Ok(schedule
        .points
        .iter()
        .map(|point| {
            let factor = aligned_tensor_factor(*point);
            block_vandermonde_row(*point)
                .iter()
                .map(|entry| factor.mul(*entry))
                .collect()
        })
        .collect())
}

/// Apply the leakage matrix to a block mask: returns the `b` query-point
/// evaluations of `B_896·R`. Independent cross-check of `leakage_matrix_at`.
pub fn leakage_apply(
    schedule: &MaskQuerySchedule,
    mask: &BlockMask,
) -> Result<Vec<QM31>, V5MaskError> {
    schedule.validate()?;
    Ok(schedule
        .points
        .iter()
        .map(|point| aligned_tensor_factor(*point).mul(mask.evaluate_at(*point)))
        .collect())
}

// ---------------------------------------------------------------------------
// Square-matrix determinant over QM31 (Gaussian elimination, partial pivot).
// ---------------------------------------------------------------------------

/// Determinant of a square QM31 matrix via Gaussian elimination. Returns
/// `QM31::ZERO` iff the matrix is singular.
pub fn qm31_determinant(matrix: &[Vec<QM31>]) -> QM31 {
    let n = matrix.len();
    let mut work: Vec<Vec<QM31>> = matrix.to_vec();
    let mut det = QM31::ONE;
    for column in 0..n {
        // Find a nonzero pivot in this column at or below the diagonal.
        let pivot = (column..n).find(|&row| !work[row][column].is_zero());
        let pivot = match pivot {
            Some(row) => row,
            None => return QM31::ZERO,
        };
        if pivot != column {
            work.swap(pivot, column);
            det = det.neg();
        }
        let pivot_value = work[column][column];
        det = det.mul(pivot_value);
        let pivot_inv = pivot_value
            .try_inv()
            .expect("pivot is nonzero by construction");
        let (pivot_rows, later_rows) = work.split_at_mut(column + 1);
        let pivot_row = &pivot_rows[column];
        for work_row in later_rows {
            let factor = work_row[column].mul(pivot_inv);
            if factor.is_zero() {
                continue;
            }
            for (entry, &pivot_entry) in work_row[column..].iter_mut().zip(&pivot_row[column..]) {
                *entry = entry.sub(factor.mul(pivot_entry));
            }
        }
    }
    det
}

// ---------------------------------------------------------------------------
// Wire fibre geometry: 18 disjoint four-point fibres (72 layer-zero rows).
//
// One deployed proof opens `q = 18` query fibres of the 2^19 codeword domain
// (Johnson fibre count 2^17, so each fibre has exactly 4 positions). The
// layer-zero point-evaluation leak of a masked lane therefore has at most
// `18 * 4 = 72` distinct rows: the square `b = 96` schedule above CANNOT be
// instantiated from one proof, and is retained only as an algebraic
// diagnostic. The wire-shaped hiding statement is rectangular: the 72 x 96
// leakage map has full row rank, hence is surjective, hence the fibre-count
// hiding lemma applies (`CoreHiding` takes surjectivity directly; it never
// needed a square matrix).
//
// The geometry is what makes the rank deterministic rather than
// probabilistic: a four-point fibre is the orbit {(x,y), (x,-y), (-x,y),
// (-x,-y)} (on the circle, y^2 = 1 - x^2 is shared by x and -x), so 18
// disjoint fibres present 36 distinct x-nodes each carrying a +-y pair --
// exactly the `circleTMatrix` witness shape. Distinctness of the nodes
// follows from fibre disjointness (the `CircleGroupOrder` same-x criterion),
// not from a Schwartz-Zippel bound over the schedule.
// ---------------------------------------------------------------------------

/// Queries per branch on the deployed wire (`queries_per_branch` in the
/// soundness-parameter manifest).
pub const V5_QUERY_COUNT: usize = 18;

/// Positions per opened fibre: the 2^19 codeword over 2^17 Johnson fibres.
pub const V5_FIBRE_SIZE: usize = 4;

/// Distinct layer-zero positions one proof can open: `18 * 4 = 72`.
pub const V5_LAYER_ZERO_ROWS: usize = V5_QUERY_COUNT * V5_FIBRE_SIZE;

/// Distinct x-nodes those positions occupy: each fibre contributes the pair
/// `{x, -x}`, so disjoint fibres give `2` nodes each.
pub const V5_FIBRE_X_NODES: usize = V5_LAYER_ZERO_ROWS / 2;

/// The four-point orbit of a base circle point: `{(x, +-y), (-x, +-y)}`.
/// All four lie on the circle since `(-x)^2 + (+-y)^2 = x^2 + y^2`.
pub fn fibre_positions(base: SecureCirclePoint) -> [SecureCirclePoint; V5_FIBRE_SIZE] {
    let SecureCirclePoint { x, y } = base;
    [
        SecureCirclePoint { x, y },
        SecureCirclePoint { x, y: y.neg() },
        SecureCirclePoint { x: x.neg(), y },
        SecureCirclePoint { x: x.neg(), y: y.neg() },
    ]
}

/// A layer-zero query schedule in wire geometry: 18 fibre base points, each
/// expanded to its four-point orbit. This models the ORBIT STRUCTURE of the
/// deployed schedule; the Fiat-Shamir index -> fibre binding stays a named
/// obligation.
#[derive(Clone, Debug)]
pub struct FibreSchedule {
    pub bases: Vec<SecureCirclePoint>,
}

impl FibreSchedule {
    fn validate(&self) -> Result<(), V5MaskError> {
        if self.bases.len() != V5_QUERY_COUNT {
            return Err(V5MaskError::ScheduleLength {
                expected: V5_QUERY_COUNT,
                actual: self.bases.len(),
            });
        }
        Ok(())
    }

    /// The 72 layer-zero positions, fibre by fibre.
    pub fn positions(&self) -> Vec<SecureCirclePoint> {
        self.bases
            .iter()
            .flat_map(|&base| fibre_positions(base))
            .collect()
    }
}

/// A diagnostic fibre schedule from 18 generic distinct parameters. The
/// parameter offset keeps it disjoint from the square diagnostic schedule.
pub fn sampled_fibre_schedule() -> Result<FibreSchedule, V5MaskError> {
    let mut bases = Vec::with_capacity(V5_QUERY_COUNT);
    for i in 0..V5_QUERY_COUNT {
        let base = secure_circle_point_from_parameter(valid_query_parameter(101 + 7 * i))
            .map_err(V5MaskError::CirclePoint)?;
        bases.push(base);
    }
    Ok(FibreSchedule { bases })
}

/// A schedule in which one fibre is opened twice (a Fiat-Shamir collision).
pub fn repeated_fibre_schedule() -> Result<FibreSchedule, V5MaskError> {
    let mut schedule = sampled_fibre_schedule()?;
    schedule.bases[1] = schedule.bases[0];
    Ok(schedule)
}

/// The rectangular wire leakage matrix: 72 rows (fibre positions, in fibre
/// order) by `b = 96` columns, row `i` equal to
/// `B_896(p_i) * [block Vandermonde row at p_i]`.
pub fn fibre_leakage_matrix(schedule: &FibreSchedule) -> Result<Vec<Vec<QM31>>, V5MaskError> {
    schedule.validate()?;
    Ok(schedule
        .positions()
        .into_iter()
        .map(|point| {
            let factor = aligned_tensor_factor(point);
            block_vandermonde_row(point)
                .iter()
                .map(|entry| factor.mul(*entry))
                .collect()
        })
        .collect())
}

/// The 72 x 72 minor on the first `V5_FIBRE_X_NODES = 36` columns of each
/// coefficient block: the `circleTMatrix` witness shape at 36 x-nodes with
/// +-y pairs. Its nonsingularity certifies full row rank of the rectangular
/// leakage matrix.
pub fn fibre_leakage_minor(schedule: &FibreSchedule) -> Result<Vec<Vec<QM31>>, V5MaskError> {
    let full = fibre_leakage_matrix(schedule)?;
    Ok(full
        .into_iter()
        .map(|row| {
            let mut minor = Vec::with_capacity(V5_LAYER_ZERO_ROWS);
            minor.extend_from_slice(&row[0..V5_FIBRE_X_NODES]);
            minor.extend_from_slice(&row[V5_MASK_M..V5_MASK_M + V5_FIBRE_X_NODES]);
            minor
        })
        .collect())
}

/// Rank of a rectangular QM31 matrix by Gaussian elimination.
pub fn qm31_rank(matrix: &[Vec<QM31>]) -> usize {
    let rows = matrix.len();
    if rows == 0 {
        return 0;
    }
    let cols = matrix[0].len();
    let mut work: Vec<Vec<QM31>> = matrix.to_vec();
    let mut rank = 0usize;
    for column in 0..cols {
        let pivot = (rank..rows).find(|&row| !work[row][column].is_zero());
        let Some(pivot) = pivot else { continue };
        work.swap(pivot, rank);
        let pivot_row = work[rank].clone();
        let pivot_inv = pivot_row[column]
            .try_inv()
            .expect("pivot is nonzero by construction");
        for (row, work_row) in work.iter_mut().enumerate() {
            if row == rank {
                continue;
            }
            let factor = work_row[column].mul(pivot_inv);
            if factor.is_zero() {
                continue;
            }
            for (entry, &pivot_entry) in work_row[column..].iter_mut().zip(&pivot_row[column..]) {
                *entry = entry.sub(factor.mul(pivot_entry));
            }
        }
        rank += 1;
        if rank == rows {
            break;
        }
    }
    rank
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Small deterministic xorshift word source for the sampler tests.
    struct XorShift(u64);

    impl Qm31WordSource for XorShift {
        fn next_word(&mut self) -> u32 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            (x >> 21) as u32
        }
    }

    /// A word source that always yields a non-canonical draw (`>= P` after
    /// masking), to exercise the rejection budget.
    struct AlwaysOutOfRange;

    impl Qm31WordSource for AlwaysOutOfRange {
        fn next_word(&mut self) -> u32 {
            0xffff_ffff
        }
    }

    fn sample_mask(seed: u64) -> BlockMask {
        let mut source = XorShift(seed);
        sample_block_mask(&mut source).expect("sampler has ample budget")
    }

    // (a) T̂ == T on all active rows.
    #[test]
    fn masked_column_agrees_with_trace_on_active_rows() {
        let real: Vec<QM31> = (0..V5_TRACE_ROWS)
            .map(|i| qm31_from_m31(M31(i as u32 * 7 + 11)))
            .collect();
        let mask = sample_mask(0x5651_2a11_9c3d_77ffu64);
        let masked = mask_column(&real, &mask).unwrap();
        for row in v5_active_rows() {
            assert_eq!(masked[row], real[row], "row {row} disturbed");
        }
        // Every non-reserved row is untouched, including the gap before the
        // aligned block and the unused tail after it.
        for row in 0..V5_TRACE_ROWS {
            if !v5_reserved_rows().contains(&row) {
                assert_eq!(masked[row], real[row], "non-reserved row {row} disturbed");
            }
        }
        // The reserved rows actually changed (mask is nonzero w.h.p.).
        let changed = v5_reserved_rows().any(|row| masked[row] != real[row]);
        assert!(changed, "mask left every reserved row untouched");
    }

    // (b) Masked column encodes to a codeword of the right length (rate 1/512).
    #[test]
    fn masked_column_encodes_at_rate_1_over_512() {
        let real: Vec<QM31> = (0..V5_TRACE_ROWS)
            .map(|i| qm31_from_m31(M31(i as u32 + 1)))
            .collect();
        let mask = sample_mask(0x1234_5678_9abc_def1u64);
        let masked = mask_column(&real, &mask).unwrap();
        assert_eq!(masked.len(), V5_TRACE_ROWS);

        let encoder = v5_encoder();
        let codeword = encode_masked_column(&encoder, &masked).unwrap();
        assert_eq!(codeword.len(), V5_CODEWORD_LEN);
        assert_eq!(codeword.len(), V5_TRACE_ROWS * 512);
        assert!(v5_mask_message_bound() <= V5_TRACE_ROWS);
        assert_eq!(v5_mask_message_bound(), 992);
    }

    // (c) Leakage matrix nonsingular on a valid schedule, singular on a
    // degenerate one (teeth).
    #[test]
    fn leakage_matrix_nonsingular_on_valid_and_singular_on_degenerate() {
        let valid = sampled_valid_schedule().unwrap();
        let leakage = leakage_matrix_at(&valid).unwrap();
        assert_eq!(leakage.len(), V5_MASK_B);
        assert_eq!(leakage[0].len(), V5_MASK_B);
        assert!(
            !qm31_determinant(&leakage).is_zero(),
            "valid schedule leakage matrix was singular"
        );

        // The block Vandermonde alone is also nonsingular on the valid schedule.
        let vander = block_vandermonde(&valid).unwrap();
        assert!(
            !qm31_determinant(&vander).is_zero(),
            "block Vandermonde was singular on a generic schedule"
        );

        let degenerate = degenerate_schedule().unwrap();
        let degenerate_leakage = leakage_matrix_at(&degenerate).unwrap();
        assert!(
            qm31_determinant(&degenerate_leakage).is_zero(),
            "degenerate schedule leakage matrix was NOT singular"
        );
        // The duplicated point collapses the underlying block Vandermonde too.
        let degenerate_vander = block_vandermonde(&degenerate).unwrap();
        assert!(
            qm31_determinant(&degenerate_vander).is_zero(),
            "duplicated block Vandermonde was not singular"
        );
    }

    // (d) The sampler accepts only canonical coordinates and enforces its
    // rejection budget. The uniformity claim follows from the rejection rule,
    // not from this finite statistical smoke test.
    #[test]
    fn sampler_is_canonical_and_rejects_out_of_range() {
        let mut source = XorShift(0x9e37_79b9_7f4a_7c15u64);
        let count = 8_000usize;
        let mut sum = 0u128;
        let mut low = 0usize;
        let mut high = 0usize;
        for _ in 0..count {
            let value = sample_m31(&mut source).unwrap();
            assert!(value.0 < aspis_core::field::P, "non-canonical draw");
            sum += u128::from(value.0);
            if value.0 < aspis_core::field::P / 2 {
                low += 1;
            } else {
                high += 1;
            }
        }
        let mean = (sum / count as u128) as u32;
        let expected = aspis_core::field::P / 2;
        // Within 3% of the midpoint over 8k samples.
        let tolerance = expected / 32;
        assert!(
            mean.abs_diff(expected) < tolerance,
            "sample mean {mean} far from {expected}"
        );
        assert!(low > count / 3 && high > count / 3, "range poorly covered");

        // The rejection rule refuses a stream that never produces a canonical
        // value and exhausts its budget instead of returning a biased element.
        let mut bad = AlwaysOutOfRange;
        assert_eq!(sample_m31(&mut bad), Err(MaskSampleExhausted));
        assert_eq!(sample_block_mask(&mut bad), Err(MaskSampleExhausted));
    }

    // (e) The concrete conversion table reconstructs every ordinary monomial
    // coefficient-by-coefficient from the natural basis.
    #[test]
    fn monomial_to_natural_table_is_an_exact_inverse() {
        let basis = natural_line_basis_polynomials(V5_MASK_M);
        let conversion = ordinary_monomials_in_natural_line_basis(V5_MASK_M);
        for degree in 0..V5_MASK_M {
            let mut reconstructed = vec![M31::ZERO; V5_MASK_M];
            for natural in 0..V5_MASK_M {
                let weight = conversion[degree][natural];
                for (monomial, &coefficient) in basis[natural].iter().enumerate() {
                    reconstructed[monomial] = reconstructed[monomial].add(weight.mul(coefficient));
                }
            }
            for (monomial, coefficient) in reconstructed.into_iter().enumerate() {
                assert_eq!(
                    coefficient,
                    if monomial == degree {
                        M31::ONE
                    } else {
                        M31::ZERO
                    },
                    "conversion entry ({monomial}, {degree}) is not the identity"
                );
            }
        }
    }

    // (f) The aligned polynomial route equals diag(B_896(p_i)) · V.
    #[test]
    fn leakage_matrix_is_diag_times_block_vandermonde() {
        let schedule = sampled_valid_schedule().unwrap();
        let leakage = leakage_matrix_at(&schedule).unwrap();
        let vander = block_vandermonde(&schedule).unwrap();
        let diag = aligned_factor_diagonal(&schedule).unwrap();

        for i in 0..V5_MASK_B {
            assert!(!diag[i].is_zero(), "valid diagonal entry {i} vanished");
            for j in 0..V5_MASK_B {
                assert_eq!(
                    leakage[i][j],
                    diag[i].mul(vander[i][j]),
                    "L[{i}][{j}] != diag * V"
                );
            }
        }

        // Independent paths: matrix application, compact factorisation, and
        // the exact reserved coefficient representation all agree.
        let mask = sample_mask(0x0bad_c0de_1337_babeu64);
        let direct = leakage_apply(&schedule, &mask).unwrap();
        let coeffs: Vec<QM31> = mask.p.iter().chain(mask.q.iter()).copied().collect();
        for i in 0..V5_MASK_B {
            let mut acc = QM31::ZERO;
            for j in 0..V5_MASK_B {
                acc = acc.add(leakage[i][j].mul(coeffs[j]));
            }
            assert_eq!(acc, direct[i], "matrix-vector row {i} disagreed");
            assert_eq!(
                direct[i],
                evaluate_aligned_mask_from_message(&mask, schedule.points[i]),
                "reserved coefficient evaluation {i} disagreed"
            );
        }
    }

    // (g) The real encoder basis images equal the factored block matrix.
    #[test]
    fn real_encoder_leakage_is_aligned_factor_times_block_vandermonde() {
        let encoder = v5_encoder();
        let indices = [
            0usize,
            1,
            2,
            3,
            4,
            7,
            31,
            255,
            1_023,
            V5_CODEWORD_LEN / 3,
            V5_CODEWORD_LEN / 2,
            V5_CODEWORD_LEN - 4,
            V5_CODEWORD_LEN - 1,
        ];
        for index in indices {
            assert_eq!(
                encoder_leakage_row(&encoder, index).unwrap(),
                encoder_factored_leakage_row(&encoder, index).unwrap(),
                "real encoder factorisation failed at codeword index {index}"
            );
        }
    }

    // (h) Full C2 encoding of a concrete aligned mask agrees with the compact
    // factorisation at representative codeword positions.
    #[test]
    fn encoded_mask_symbols_match_the_aligned_polynomial() {
        let encoder = v5_encoder();
        let mask = sample_mask(0x18a4_9c2e_7d31_b605u64);
        let message = mask_column(&[QM31::ZERO; V5_TRACE_ROWS], &mask).unwrap();
        let codeword = encoder.encode_c2_message(&message).unwrap();
        for index in [
            0usize,
            1,
            17,
            511,
            65_537,
            V5_CODEWORD_LEN / 2 + 3,
            V5_CODEWORD_LEN - 1,
        ] {
            let x = qm31_from_m31(encoder.encode_c1_basis_value(2, index).unwrap());
            let y = qm31_from_m31(encoder.encode_c1_basis_value(1, index).unwrap());
            let factor = qm31_from_m31(
                encoder
                    .encode_c1_basis_value(V5_RESERVED_START, index)
                    .unwrap(),
            );
            assert_eq!(codeword[index], factor.mul(mask.evaluate(x, y)));
        }
    }

    // Structural pins so a silent constant edit is caught.
    #[test]
    fn reserved_layout_is_pinned() {
        assert_eq!(V5_TRACE_ROWS, 1024);
        assert_eq!(V5_ACTIVE_ROWS, 879);
        assert_eq!(*v5_active_rows().end(), 878);
        assert_eq!(*v5_reserved_rows().start(), 896);
        assert_eq!(*v5_reserved_rows().end(), 991);
        assert_eq!(v5_reserved_rows().count(), V5_MASK_B);
        assert_eq!(V5_MASK_B, 96);
        assert_eq!(V5_MASK_M, 48);
        assert_eq!(V5_CODEWORD_LEN, 1 << 19);
        // p/q blocks exactly tile the reserved rows.
        assert!(V5_RESERVED_START.is_multiple_of(V5_RESERVED_ALIGNMENT));
        assert_eq!(v5_reserved_p_index(0), 896);
        assert_eq!(v5_reserved_q_index(V5_MASK_M - 1), 991);
    }

    fn assert_on_circle(point: SecureCirclePoint) {
        assert_eq!(
            point.x.mul(point.x).add(point.y.mul(point.y)),
            QM31::ONE,
            "point left the circle"
        );
    }

    // (i) The design record: one proof opens 72 of 96 -- a square b = 96
    // point-evaluation schedule cannot be instantiated from one proof, and
    // the fibre orbit really is 4 distinct on-circle points.
    #[test]
    fn one_proof_opens_72_layer_zero_positions_not_96() {
        assert_eq!(V5_LAYER_ZERO_ROWS, 72);
        assert!(V5_LAYER_ZERO_ROWS < V5_MASK_B);

        let schedule = sampled_fibre_schedule().unwrap();
        let positions = schedule.positions();
        assert_eq!(positions.len(), V5_LAYER_ZERO_ROWS);
        for &point in &positions {
            assert_on_circle(point);
        }
        // All 72 positions pairwise distinct (disjoint fibres, x != 0, y != 0).
        for i in 0..positions.len() {
            for j in (i + 1)..positions.len() {
                let same = positions[i].x == positions[j].x && positions[i].y == positions[j].y;
                assert!(!same, "positions {i} and {j} coincide");
            }
        }
        // Whatever the schedule, the layer-zero leakage rank cannot reach 96.
        let leakage = fibre_leakage_matrix(&schedule).unwrap();
        assert!(qm31_rank(&leakage) <= V5_LAYER_ZERO_ROWS);
    }

    // (j) The wire-shaped hiding certificate: full row rank 72, certified by
    // the 72 x 72 circleTMatrix-witness minor, deterministically across
    // schedules (three distinct parameter families, not one lucky draw).
    #[test]
    fn fibre_leakage_has_full_row_rank() {
        for offset in [0usize, 1000, 2000] {
            let mut bases = Vec::with_capacity(V5_QUERY_COUNT);
            for i in 0..V5_QUERY_COUNT {
                let base = secure_circle_point_from_parameter(valid_query_parameter(
                    201 + offset + 11 * i,
                ))
                .unwrap();
                bases.push(base);
            }
            let schedule = FibreSchedule { bases };
            let leakage = fibre_leakage_matrix(&schedule).unwrap();
            assert_eq!(leakage.len(), V5_LAYER_ZERO_ROWS);
            assert_eq!(leakage[0].len(), V5_MASK_B);
            assert_eq!(
                qm31_rank(&leakage),
                V5_LAYER_ZERO_ROWS,
                "leakage lost row rank at offset {offset}"
            );

            let minor = fibre_leakage_minor(&schedule).unwrap();
            assert_eq!(minor.len(), V5_LAYER_ZERO_ROWS);
            assert_eq!(minor[0].len(), V5_LAYER_ZERO_ROWS);
            assert!(
                !qm31_determinant(&minor).is_zero(),
                "witness-shape minor singular at offset {offset}"
            );

            // The diagonal factor B_896 is nonzero at every schedule point
            // (numeric mirror of the kernel-checked nonvanishing).
            for point in schedule.positions() {
                assert!(!aligned_tensor_factor(point).is_zero());
            }
        }
    }

    // (k) A Fiat-Shamir fibre collision only deletes rows: the distinct view
    // keeps full row rank, so hiding survives repeats by dedup.
    #[test]
    fn repeated_fibre_keeps_full_rank_on_distinct_rows() {
        let schedule = repeated_fibre_schedule().unwrap();
        let leakage = fibre_leakage_matrix(&schedule).unwrap();
        // One duplicated fibre = 4 duplicated rows.
        assert_eq!(qm31_rank(&leakage), V5_LAYER_ZERO_ROWS - V5_FIBRE_SIZE);

        let positions = schedule.positions();
        let mut distinct_rows: Vec<Vec<QM31>> = Vec::new();
        let mut seen: Vec<SecureCirclePoint> = Vec::new();
        for (row, &point) in leakage.iter().zip(positions.iter()) {
            if seen
                .iter()
                .any(|&prior| prior.x == point.x && prior.y == point.y)
            {
                continue;
            }
            seen.push(point);
            distinct_rows.push(row.clone());
        }
        assert_eq!(distinct_rows.len(), V5_LAYER_ZERO_ROWS - V5_FIBRE_SIZE);
        assert_eq!(qm31_rank(&distinct_rows), distinct_rows.len());
    }
}
