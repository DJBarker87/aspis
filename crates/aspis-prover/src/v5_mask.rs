//! Aspis v5 masking component (A): the block-form circle mask.
//!
//! # Status: PROVISIONAL — first cut, feature-gated (`v5-mask`), NOT in the v4 path
//!
//! This module is a clean-room implementation of the v5 hiding component (A):
//! the block-form circle mask
//!
//! ```text
//!     T̂ = T + Z_{H'} · R,
//! ```
//!
//! where `H'` is the active-row sub-domain, `Z_{H'}` is its vanishing
//! polynomial (so `T̂ = T` on every active row), and
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
//!   `928..=1023` (exactly `b = 96` rows), carrying the mask.
//! * The agreement property `T̂ == T` on every active row.
//! * Rate preservation: the masked column is a length-`TRACE_LEN` message and
//!   encodes, through the *real* circle encoder, to a rate-1/512 codeword.
//! * The ideal polynomial-route leakage matrix at the query points comes out
//!   exactly as
//!
//!   ```text
//!       L = diag(Z_{H'}(p_i)) · V
//!   ```
//!
//!   where `V` is the block-form circle Vandermonde model used by
//!   `CircleTMatrixHiding`. The test
//!   `leakage_matrix_is_diag_times_block_vandermonde` checks these two ideal
//!   descriptions against each other. It does not compare either description
//!   with basis images emitted by the real circle encoder.
//! * Teeth: the leakage matrix is nonsingular on a sampled valid schedule and
//!   singular on a deliberately degenerate one (a query landing on an active
//!   row, where `Z_{H'}` vanishes and the mask leaks nothing).
//!
//! ## What remains PENDING (NOT established here)
//!
//! * The exact coefficient identity between the reserved-row coefficient
//!   placement used by [`mask_column`] and the circle-FFT coefficients of the
//!   genuine polynomial product `Z_{H'}·R`. The leakage-matrix structure below
//!   is built from the genuine-polynomial route (manifestly `diag·V`); binding
//!   it to the encoder's reserved-coefficient route is the pending Lean
//!   obligation (a) — "the final Lean `= diag·circleTMatrix` decide".
//! * The exact circle vanishing polynomial. [`vanishing_active`] uses a
//!   documented line-coordinate product over distinct active abscissae as a
//!   provisional stand-in; the production circle vanishing (via the doubling
//!   structure `π(x)=2x²−1` / coset vanishing) is what Lean pins.
//! * The production trace-coset binding of rows to circle points.
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

use aspis_core::circle::{secure_circle_point_from_parameter, CirclePointError, SecureCirclePoint};
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

/// First reserved row. The reserved set is pinned to the top `b = 96` rows.
pub const V5_RESERVED_START: usize = 928;

/// Inclusive last reserved row.
pub const V5_RESERVED_END: usize = V5_TRACE_ROWS - 1;

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
const _: () = assert!(V5_RESERVED_END == V5_TRACE_ROWS - 1);

/// The active-row sub-domain `H' = 0..=878`.
pub const fn v5_active_rows() -> core::ops::RangeInclusive<usize> {
    0..=V5_ACTIVE_ROW_END
}

/// The reserved index set `928..=1023` (carries the mask).
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
// Deliverable 3: the active-row vanishing polynomial Z_{H'}.
// ---------------------------------------------------------------------------

/// The line abscissa assigned to active row `i`.
///
/// PROVISIONAL: active rows are given distinct line coordinates
/// `a_i = i + 1 ∈ M31` (`1..=879`, all canonical and distinct). These stand in
/// for the production active-row circle coordinates; the exact circle-coset
/// binding is pending in Lean.
#[inline]
pub fn v5_active_abscissa(row: usize) -> M31 {
    debug_assert!(row <= V5_ACTIVE_ROW_END);
    M31(row as u32 + 1)
}

/// Evaluate the active-row vanishing polynomial
/// `Z_{H'}(x) = ∏_{i active} (x − a_i)`.
///
/// PROVISIONAL: implemented as the exact degree-879 line-coordinate product
/// over the distinct active abscissae. It vanishes precisely when `x` equals an
/// active abscissa, so `T̂ = T` on active rows. The task's noted efficient
/// doubling-structure form (`π(x)=2x²−1`) is a pending optimization; the O(|H'|)
/// product here is correct and adequate for host-side provisional use.
pub fn vanishing_active(x: QM31) -> QM31 {
    let mut acc = QM31::ONE;
    for row in 0..V5_ACTIVE_ROWS {
        let a = qm31_from_m31(v5_active_abscissa(row));
        acc = acc.mul(x.sub(a));
    }
    acc
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

/// Build the masked column `T̂ = T + Z_{H'}·R`.
///
/// PROVISIONAL coefficient-space realization: the mask occupies exactly the
/// reserved rows, so `T̂` agrees with `T` on every non-reserved row (in
/// particular every active row). The `p` block lands on even reserved offsets
/// and the `q` block on odd reserved offsets, mirroring the circle-FFT bit-0
/// (`x` vs `y·x`) split. This is the reserved-row image of `Z_{H'}·R`; the
/// exact circle-FFT coefficient identity with the genuine polynomial product is
/// the pending Lean obligation documented at the module head.
pub fn mask_column(real: &[QM31], mask: &BlockMask) -> Result<Vec<QM31>, V5MaskError> {
    if real.len() != V5_TRACE_ROWS {
        return Err(V5MaskError::ColumnLength {
            expected: V5_TRACE_ROWS,
            actual: real.len(),
        });
    }
    let mut masked = real.to_vec();
    for k in 0..V5_MASK_M {
        masked[v5_reserved_p_index(k)] = masked[v5_reserved_p_index(k)].add(mask.p[k]);
        masked[v5_reserved_q_index(k)] = masked[v5_reserved_q_index(k)].add(mask.q[k]);
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

/// The flat degree budget of `Z_{H'}·R` in the line coordinate:
/// `deg Z_{H'} + max(deg p, deg q) = 879 + 47 = 926 < 1024`. Returned so the
/// rate check can assert the mask never inflates the message degree.
pub const fn v5_mask_flat_degree_bound() -> usize {
    V5_ACTIVE_ROWS + (V5_MASK_M - 1)
}

// ---------------------------------------------------------------------------
// Deliverable 5: the leakage matrix and its diag·block-Vandermonde structure.
// ---------------------------------------------------------------------------

/// A query schedule: exactly `b = 96` circle points at which the mask codeword
/// is opened. These are the fold-derived FRI query points.
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

/// PROVISIONAL deterministic schedule parameter for query `i`. Chosen with a
/// nonzero `c1` so the point is never singular and its `x` is never a (pure
/// M31) active abscissa — hence `Z_{H'}(x_i) ≠ 0` on the valid schedule.
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

/// A deliberately degenerate schedule: query 0 is moved onto the identity
/// point `(1, 0)`, whose `x = 1 = a_0` is the first active abscissa. There
/// `Z_{H'}` vanishes, so the whole leakage row is zero and `L` is singular —
/// even though the block Vandermonde `V` itself stays nonsingular. This is the
/// teeth showing the `diag(Z_{H'})` factor carries real weight.
pub fn degenerate_schedule() -> Result<MaskQuerySchedule, V5MaskError> {
    let mut schedule = sampled_valid_schedule()?;
    schedule.points[0] = SecureCirclePoint {
        x: QM31::ONE,
        y: QM31::ZERO,
    };
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

/// The per-query diagonal factors `Z_{H'}(x_i)`.
pub fn vanishing_diagonal(schedule: &MaskQuerySchedule) -> Result<Vec<QM31>, V5MaskError> {
    schedule.validate()?;
    Ok(schedule
        .points
        .iter()
        .map(|point| vanishing_active(point.x))
        .collect())
}

/// The leakage matrix `L`: the map from the `2m` mask coefficients
/// `(p_0..p_{m-1}, q_0..q_{m-1})` to the query-point evaluations of `Z_{H'}·R`.
///
/// Row `i` is `Z_{H'}(x_i) · [block Vandermonde row at p_i]`, i.e.
/// `L = diag(Z_{H'}(p_i)) · V`. This is the structural deliverable; that the
/// structure holds exactly is checked by
/// `leakage_matrix_is_diag_times_block_vandermonde` (evidence for Lean
/// obligation (a)).
pub fn leakage_matrix_at(schedule: &MaskQuerySchedule) -> Result<Vec<Vec<QM31>>, V5MaskError> {
    schedule.validate()?;
    Ok(schedule
        .points
        .iter()
        .map(|point| {
            let z = vanishing_active(point.x);
            block_vandermonde_row(*point)
                .iter()
                .map(|entry| z.mul(*entry))
                .collect()
        })
        .collect())
}

/// Apply the leakage matrix to a block mask: returns the `b` query-point
/// evaluations of `Z_{H'}·R`. Independent cross-check of `leakage_matrix_at`.
pub fn leakage_apply(
    schedule: &MaskQuerySchedule,
    mask: &BlockMask,
) -> Result<Vec<QM31>, V5MaskError> {
    schedule.validate()?;
    Ok(schedule
        .points
        .iter()
        .map(|point| vanishing_active(point.x).mul(mask.evaluate_at(*point)))
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
        for row in (column + 1)..n {
            let factor = work[row][column].mul(pivot_inv);
            if factor.is_zero() {
                continue;
            }
            for col in column..n {
                let subtract = factor.mul(work[column][col]);
                work[row][col] = work[row][col].sub(subtract);
            }
        }
    }
    det
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
        // And every non-reserved row is untouched (rows 879..=927 too).
        for row in 0..V5_RESERVED_START {
            assert_eq!(masked[row], real[row], "non-reserved row {row} disturbed");
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
        // Flat degree budget of Z_{H'}·R fits in the message space.
        assert!(v5_mask_flat_degree_bound() < V5_TRACE_ROWS);
        assert_eq!(v5_mask_flat_degree_bound(), 926);
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
        // ... yet its block Vandermonde stays nonsingular: the vanishing
        // diagonal is what collapses the rank.
        let degenerate_vander = block_vandermonde(&degenerate).unwrap();
        assert!(
            !qm31_determinant(&degenerate_vander).is_zero(),
            "degenerate block Vandermonde unexpectedly singular"
        );
        assert!(vanishing_active(degenerate.points[0].x).is_zero());
    }

    // (d) Mask coefficients are uniform (sampler check).
    #[test]
    fn sampler_is_canonical_uniform_and_rejects_out_of_range() {
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

    // (e) The ideal polynomial-route leakage matrix equals
    // diag(Z_{H'}(p_i)) · V for the explicit block-form V. This does not bind
    // the real encoder's basis images.
    #[test]
    fn leakage_matrix_is_diag_times_block_vandermonde() {
        let schedule = sampled_valid_schedule().unwrap();
        let leakage = leakage_matrix_at(&schedule).unwrap();
        let vander = block_vandermonde(&schedule).unwrap();
        let diag = vanishing_diagonal(&schedule).unwrap();

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

        // Independent path: L applied to a concrete mask equals the direct
        // per-point evaluation of Z_{H'}·R.
        let mask = sample_mask(0x0bad_c0de_1337_babeu64);
        let direct = leakage_apply(&schedule, &mask).unwrap();
        let coeffs: Vec<QM31> = mask.p.iter().chain(mask.q.iter()).copied().collect();
        for i in 0..V5_MASK_B {
            let mut acc = QM31::ZERO;
            for j in 0..V5_MASK_B {
                acc = acc.add(leakage[i][j].mul(coeffs[j]));
            }
            assert_eq!(acc, direct[i], "matrix-vector row {i} disagreed");
        }
    }

    // Structural pins so a silent constant edit is caught.
    #[test]
    fn reserved_layout_is_pinned() {
        assert_eq!(V5_TRACE_ROWS, 1024);
        assert_eq!(V5_ACTIVE_ROWS, 879);
        assert_eq!(*v5_active_rows().end(), 878);
        assert_eq!(*v5_reserved_rows().start(), 928);
        assert_eq!(*v5_reserved_rows().end(), 1023);
        assert_eq!(v5_reserved_rows().count(), V5_MASK_B);
        assert_eq!(V5_MASK_B, 96);
        assert_eq!(V5_MASK_M, 48);
        assert_eq!(V5_CODEWORD_LEN, 1 << 19);
        // p/q blocks exactly tile the reserved rows.
        assert_eq!(v5_reserved_p_index(0), 928);
        assert_eq!(v5_reserved_q_index(V5_MASK_M - 1), 1023);
    }
}
