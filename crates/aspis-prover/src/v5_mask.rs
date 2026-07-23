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
//! domain and, for each existing semantic M31 C1 lane,
//!
//! ```text
//!     R ∈ V_b = { p(x) + y·q(x) : deg p, deg q ≤ m-1 }
//! ```
//!
//! is a random M31 block-form circle polynomial with `m = V5_MASK_M = 48`
//! coefficients in each block (`b = V5_MASK_B = 2m = 96` total). Each
//! coefficient is sampled directly in M31 with the pinned canonical rejection
//! rule. The sixteen lane masks use sixteen caller-supplied word sources; no
//! QM31 value is split into four M31 lane masks.
//!
//! The older [`BlockMask`] QM31 primitive remains in this module because the
//! feature-gated sumcheck work uses its QM31 sampler and because it is useful
//! for extension-field algebraic diagnostics. The field-correct semantic C1
//! primitive is [`M31BlockMask`].
//!
//! ## What this provisional primitive ESTABLISHES (validated by the tests here)
//!
//! * The M31 block-form mask object `R = p(x) + y·q(x)`, its canonical
//!   rejection sampler, and an API which samples one mask for each of the
//!   existing sixteen semantic C1 lanes from separate sources.
//! * The reserved-row layout: active rows `0..=878`, reserved rows
//!   `896..=991` (exactly `b = 96` rows), carrying the mask. The start is
//!   aligned to a 128-coordinate tensor block.
//! * The agreement property `T̂ == T` on every active row of an M31 C1
//!   message. Component (A) adds no mask-only C1 lane: each mask is placed in
//!   the reserved rows of its existing semantic lane. The bespoke H, G and D
//!   auxiliaries belong to the current-v4 context; this isolated primitive
//!   neither retains them nor defines their v5 replacement.
//! * Rate preservation: the masked column is a length-`TRACE_LEN` message and
//!   encodes, through the real M31 C1 circle encoder, to a rate-1/512 codeword.
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
//! * Production integration and the transcript/entropy derivation for sixteen
//!   independent lane sources. The API requires separate sources but cannot
//!   establish that a caller derived them independently.
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
use aspis_core::params::CIRCLE_GEN;

use crate::circle_candidate::{CircleCandidateError, CircleEncoder};

/// Provisional component (C): one full atomic-v3-kernel helper lane for
/// masking the combined PCS/OOD/fold/terminal view.  It is quarantined under
/// the same `v5-mask` feature and is not reachable from the v4 prover.
#[path = "v5_c_mask.rs"]
pub mod component_c;

/// Feature-gated construction of the real atomic-v3 v5 layer-zero messages,
/// rate-1/512 codewords and private Merkle roots.  This remains outside the
/// v4 prover and deliberately stops before transcript/opening integration.
#[path = "v5_spend_messages.rs"]
pub mod spend_messages;

/// Honest incremental PCS relation for the four-claim v5 CU/prover path.
/// It is isolated from every v4 proof format and production entrypoint.
#[path = "v5_relation_prover.rs"]
pub mod relation_prover;

/// Transcript-order-correct split construction of the real v5 layer-zero
/// commitment. C1 is committed before `lambda, chi`; C2 is built afterwards.
#[path = "v5_split_layer_zero.rs"]
pub mod split_layer_zero;

/// Real-witness host artefact for the isolated v5/tag-66 CU path.
#[path = "v5_real_host_proof.rs"]
pub mod real_host_proof;

/// Runtime-sized Component-C downstream evaluator.  It consumes the actual
/// sorted/deduplicated query lists and is shared by the direct-C correspondence
/// path and the old fixed-q18 offline matrix oracle.
#[path = "v5_component_c_runtime.rs"]
pub mod component_c_runtime;

/// Offline-only frozen-q18 Component-C conditioned-view matrix generator.
/// It emits audit material and is not linked into a verifier or v4 path.
#[path = "v5_component_c_emat.rs"]
pub mod component_c_emat;

/// Offline-only frozen-q18 Component-C private-view matrix generator.
/// Like `component_c_emat`, this is host audit machinery only: it does not
/// define a legal-difference space or enter any verifier/proof format.
#[path = "v5_component_c_fmat.rs"]
pub mod component_c_fmat;

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

/// Atomic-v3 leaves one linear relation on the 96 Component-A coefficients.
/// We derive ordinary `p_36`; the remaining 95 coefficients stay uniform.
/// This pivot is outside the 72-column minor used by the unconstrained proof.
pub const V5_ATOMIC_A_PIVOT_COORDINATE: usize = 36;
pub const V5_ATOMIC_A_FREE_COORDINATES: usize = V5_MASK_B - 1;

/// Existing semantic M31 C1 lane count in the proposed v5 width.
///
/// Component (A) samples one mask per lane and adds no mask-only C1 lane.
pub const V5_SEMANTIC_C1_LANES: usize = crate::v5_cu_envelope::V5_C1_COLUMNS;

/// Rejection-sampler retry budget per M31 draw (mirrors `state_only_entropy`).
pub const V5_MASK_SAMPLE_RETRY_LIMIT: usize = 16;

// Compile-time pins of the reserved layout.
const _: () = assert!(V5_RESERVED_END - V5_RESERVED_START + 1 == V5_MASK_B);
const _: () = assert!(V5_MASK_B == 2 * V5_MASK_M);
const _: () = assert!(V5_ATOMIC_A_PIVOT_COORDINATE < V5_MASK_M);
const _: () = assert!(V5_ATOMIC_A_FREE_COORDINATES == 95);
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
// Deliverable 2: field-native block masks and their rejection samplers.
// ---------------------------------------------------------------------------

/// An extension-field block mask retained for the QM31 sumcheck sampler and
/// algebraic diagnostics.
///
/// Semantic C1 columns must use [`M31BlockMask`]; a QM31 mask must not be split
/// into four M31 lane masks.
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

/// A field-correct mask for one existing semantic M31 C1 lane.
///
/// Its 96 coefficients describe `R(x,y) = p(x) + y*q(x)`, with 48 ordinary
/// M31 coefficients in each block. One independently derived instance is
/// required for each semantic lane.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct M31BlockMask {
    /// `p_0 .. p_47`, in ordinary monomial order.
    pub p: [M31; V5_MASK_M],
    /// `q_0 .. q_47`, in ordinary monomial order.
    pub q: [M31; V5_MASK_M],
}

impl M31BlockMask {
    const ZERO: Self = Self {
        p: [M31::ZERO; V5_MASK_M],
        q: [M31::ZERO; V5_MASK_M],
    };

    /// Evaluate `p(x) + y*q(x)` in M31 using Horner's rule.
    pub fn evaluate(&self, x: M31, y: M31) -> M31 {
        let mut p_value = M31::ZERO;
        let mut q_value = M31::ZERO;
        for degree in (0..V5_MASK_M).rev() {
            p_value = p_value.mul(x).add(self.p[degree]);
            q_value = q_value.mul(x).add(self.q[degree]);
        }
        p_value.add(y.mul(q_value))
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

/// Sample one field-correct semantic-lane mask: 48 M31 values for `p`, then
/// 48 M31 values for `q`.
///
/// If the raw words are independent and uniform, canonical rejection gives
/// independent uniform M31 coefficients. This function does not derive or
/// domain-separate the raw word source.
pub fn sample_m31_block_mask<S: Qm31WordSource>(
    source: &mut S,
) -> Result<M31BlockMask, MaskSampleExhausted> {
    let mut p = [M31::ZERO; V5_MASK_M];
    let mut q = [M31::ZERO; V5_MASK_M];
    for value in &mut p {
        *value = sample_m31(source)?;
    }
    for value in &mut q {
        *value = sample_m31(source)?;
    }
    Ok(M31BlockMask { p, q })
}

fn sample_atomic_m31_free_coordinate<S: Qm31WordSource>(
    source: &mut S,
    mask: &mut M31BlockMask,
    sum: M31,
    coordinate: usize,
) -> Result<M31, MaskSampleExhausted> {
    let value = sample_m31(source)?;
    let sum = sum.add(value);
    if coordinate < V5_MASK_M {
        mask.p[coordinate] = value;
    } else {
        mask.q[coordinate - V5_MASK_M] = value;
    }
    Ok(sum)
}

/// Sample Component A on the exact atomic-v3 coefficient-sum hyperplane.
///
/// Every natural line basis polynomial is one at `x = 1`, so the sum of the
/// 96 natural message coordinates equals the sum of these ordinary `p/q`
/// coefficients.  Deriving `p_36` therefore makes the mask's contribution to
/// the atomic copy-inactive functional exactly zero while preserving 95
/// independent uniform M31 coordinates.
pub fn sample_atomic_m31_block_mask<S: Qm31WordSource>(
    source: &mut S,
) -> Result<M31BlockMask, MaskSampleExhausted> {
    let mut mask = M31BlockMask::ZERO;
    let mut sum = M31::ZERO;
    let mut coordinate = 0;
    while coordinate < V5_MASK_B {
        if coordinate != V5_ATOMIC_A_PIVOT_COORDINATE {
            sum = sample_atomic_m31_free_coordinate(source, &mut mask, sum, coordinate)?;
        }
        coordinate += 1;
    }
    mask.p[V5_ATOMIC_A_PIVOT_COORDINATE] = sum.neg();
    debug_assert_eq!(atomic_m31_block_mask_coefficient_sum(&mask), M31::ZERO);
    Ok(mask)
}

pub fn atomic_m31_block_mask_coefficient_sum(mask: &M31BlockMask) -> M31 {
    let mut sum = M31::ZERO;
    let mut index = 0;
    while index < V5_MASK_M {
        sum = sum.add(mask.p[index]);
        index += 1;
    }
    index = 0;
    while index < V5_MASK_M {
        sum = sum.add(mask.q[index]);
        index += 1;
    }
    sum
}

/// Sample exactly one M31 mask for each of the sixteen existing semantic C1
/// lanes, using a separate caller-supplied source for every lane.
///
/// This fixed-width API cannot add mask-only wire lanes. The caller remains
/// responsible for deriving the sixteen sources independently and with lane
/// domain separation.
pub fn sample_m31_lane_masks<S: Qm31WordSource>(
    sources: &mut [S; V5_SEMANTIC_C1_LANES],
) -> Result<[M31BlockMask; V5_SEMANTIC_C1_LANES], MaskSampleExhausted> {
    let mut masks = core::array::from_fn(|_| M31BlockMask::ZERO);
    for (mask, source) in masks.iter_mut().zip(sources.iter_mut()) {
        *mask = sample_m31_block_mask(source)?;
    }
    Ok(masks)
}

/// Atomic-v3 version of [`sample_m31_lane_masks`].  Each lane has 95 free
/// coefficients and its own caller-supplied, domain-separated source.
pub fn sample_atomic_m31_lane_masks<S: Qm31WordSource>(
    sources: &mut [S; V5_SEMANTIC_C1_LANES],
) -> Result<[M31BlockMask; V5_SEMANTIC_C1_LANES], MaskSampleExhausted> {
    let mut masks = core::array::from_fn(|_| M31BlockMask::ZERO);
    for (mask, source) in masks.iter_mut().zip(sources.iter_mut()) {
        *mask = sample_atomic_m31_block_mask(source)?;
    }
    Ok(masks)
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

fn zero_m31_vec(len: usize) -> Vec<M31> {
    let mut values = Vec::with_capacity(len);
    let mut index = 0;
    while index < len {
        values.push(M31::ZERO);
        index += 1;
    }
    values
}

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
        index >>= 1u32;
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
    let line = natural_line_basis_value(index >> 1u32, point.x);
    if index & 1 == 0 {
        line
    } else {
        point.y.mul(line)
    }
}

/// Evaluate one of the 128 natural tensor rows in the Component-B block
/// `256..=383` from the three circle-encoder factors that determine it.
///
/// This helper contains no table lookup or alternate encoder construction:
/// `factor`, `x`, and `y` are respectively the real encoder's rows 256, 2,
/// and 1 at one codeword position.  It is kept in the feature-gated v5 module
/// so Charon/Aeneas can extract the exact arithmetic graph without changing
/// the shared v4 encoder implementation.
pub fn row256_natural_basis_from_factors(physical: usize, factor: M31, x: M31, y: M31) -> QM31 {
    let point = SecureCirclePoint {
        x: qm31_from_m31(x),
        y: qm31_from_m31(y),
    };
    qm31_from_m31(factor).mul(natural_circle_basis_value(physical, point))
}

/// Read the three determining factors from the real circle encoder and
/// evaluate one Component-B row.  The caller supplies the physical offset
/// `0..128`; the corresponding message row is `256 + physical`.
pub fn row256_encoder_natural_basis_value(
    encoder: &CircleEncoder,
    physical: usize,
    codeword_index: usize,
) -> Result<QM31, V5MaskError> {
    let factor = encoder.encode_c1_basis_value(256, codeword_index)?;
    let x = encoder.encode_c1_basis_value(2, codeword_index)?;
    let y = encoder.encode_c1_basis_value(1, codeword_index)?;
    Ok(row256_natural_basis_from_factors(physical, factor, x, y))
}

/// The three base-field values that determine every natural row in the
/// Component-B block at one opened codeword position.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Row256ConstructorFactors {
    pub factor: M31,
    pub x: M31,
    pub y: M31,
}

/// Reverse exactly `bits` low bits, without relying on a machine-width
/// `reverse_bits` intrinsic.  Keeping this first-order makes the v5-only
/// factor constructor directly extractable by pinned Charon/Aeneas.
fn row256_reverse_low_bits(mut value: usize, bits: u32) -> usize {
    let mut reversed = 0usize;
    let mut bit = 0u32;
    while bit < bits {
        reversed = (reversed << 1u32) | (value & 1usize);
        value >>= 1u32;
        bit += 1;
    }
    reversed
}

/// Negation flags for one accepted fixed-circle runtime slot.
///
/// The order is `(x,y), (x,-y), (-x,-y), (-x,y)`.  Keeping the small
/// first-order selector separate lets the pinned extractor expose the exact
/// runtime slot permutation without duplicating the constructor.
fn row256_constructor_slot_negations(slot: usize) -> Option<(bool, bool)> {
    if slot >= 4 {
        return None;
    }
    Some((slot >= 2, slot != 0 && slot != 3))
}

/// Fixed-generator binary powering with an explicitly typed shift count.
/// This is the same multiply/square loop as `CM31::pow`; keeping the tiny
/// wrapper v5-local avoids changing the shared field/encoder implementation
/// solely for Aeneas's generated shift type.
fn row256_circle_generator_pow(mut exponent: u64) -> CM31 {
    let mut base = CIRCLE_GEN;
    let mut accumulator = CM31::ONE;
    while exponent > 0 {
        if exponent & 1 == 1 {
            accumulator = accumulator.mul(base);
        }
        base = base.square();
        exponent >>= 1u32;
    }
    accumulator
}

/// Compute the exact rows 256, 2 and 1 of the log-19 circle encoder at one
/// `(stored fibre, runtime slot)` without materializing iterator-built
/// twiddle tables.
///
/// This is an equivalent first-order view of the existing constructor, not a
/// new encoder. `stored_fibre` is the bit-reversed 17-bit Merkle index and the
/// slot order is `(x,y), (x,-y), (-x,-y), (-x,y)`.
pub fn row256_constructor_factors(
    stored_fibre: usize,
    slot: usize,
) -> Option<Row256ConstructorFactors> {
    if stored_fibre >= (1usize << 17u32) {
        return None;
    }
    let (negate_x, negate_y) = match row256_constructor_slot_negations(slot) {
        Some(negations) => negations,
        None => return None,
    };

    let representative_natural = row256_reverse_low_bits(stored_fibre, 17);
    let representative_exponent = (1u64 << 11u32) + (1u64 << 13u32) * representative_natural as u64;
    let representative = row256_circle_generator_pow(representative_exponent);
    let x = if negate_x {
        representative.a.neg()
    } else {
        representative.a
    };
    let y = if negate_y {
        representative.b.neg()
    } else {
        representative.b
    };

    let position = 4 * stored_fibre + slot;
    let layer_stored = position >> 9u32;
    let layer_natural = row256_reverse_low_bits(layer_stored, 10);
    let factor_exponent = (1u64 << 18u32) + (1u64 << 20u32) * layer_natural as u64;
    let factor_point = row256_circle_generator_pow(factor_exponent);
    let factor = if position & (1usize << 8u32) == 0 {
        factor_point.a
    } else {
        factor_point.a.neg()
    };

    Some(Row256ConstructorFactors { factor, x, y })
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
    let mut bit = 1;
    while bit < log_size {
        let previous = &factors[bit - 1];
        let mut squared = zero_m31_vec(2 * previous.len() - 1);
        let mut left = 0;
        while left < previous.len() {
            let a = previous[left];
            let mut right = 0;
            while right < previous.len() {
                let b = previous[right];
                squared[left + right] = squared[left + right].add(a.mul(b));
                right += 1;
            }
            left += 1;
        }
        let mut coefficient = 0;
        while coefficient < squared.len() {
            squared[coefficient] = squared[coefficient].double();
            coefficient += 1;
        }
        squared[0] = squared[0].sub(M31::ONE);
        factors.push(squared);
        bit += 1;
    }

    let mut basis = Vec::with_capacity(size);
    basis.push(vec![M31::ONE]);
    let mut index = 1;
    while index < size {
        let mut shifted_index = index;
        let mut bit = 0;
        while shifted_index & 1 == 0 {
            shifted_index >>= 1u32;
            bit += 1;
        }
        let prefix = &basis[index ^ (1usize << (bit as u32))];
        let factor = &factors[bit];
        let mut polynomial = zero_m31_vec(prefix.len() + factor.len() - 1);
        let mut left = 0;
        while left < prefix.len() {
            let a = prefix[left];
            let mut right = 0;
            while right < factor.len() {
                let b = factor[right];
                polynomial[left + right] = polynomial[left + right].add(a.mul(b));
                right += 1;
            }
            left += 1;
        }
        basis.push(polynomial);
        index += 1;
    }
    basis
}

/// Express each ordinary monomial `x^degree` in the natural line basis.
fn ordinary_monomials_in_natural_line_basis(size: usize) -> Vec<Vec<M31>> {
    let basis = natural_line_basis_polynomials(size);
    let mut conversion = Vec::with_capacity(size);
    let mut degree = 0;
    while degree < size {
        let mut residual = zero_m31_vec(size);
        residual[degree] = M31::ONE;
        let mut coefficients = zero_m31_vec(size);
        let mut pivot = degree;
        loop {
            let diagonal = basis[pivot][pivot];
            let scale = residual[pivot].mul(diagonal.inv());
            coefficients[pivot] = scale;
            let mut monomial = 0;
            while monomial < basis[pivot].len() {
                let value = basis[pivot][monomial];
                residual[monomial] = residual[monomial].sub(scale.mul(value));
                monomial += 1;
            }
            if pivot == 0 {
                break;
            }
            pivot -= 1;
        }
        let mut residual_is_zero = true;
        let mut monomial = 0;
        while monomial < residual.len() {
            if residual[monomial] != M31::ZERO {
                residual_is_zero = false;
                break;
            }
            monomial += 1;
        }
        debug_assert!(residual_is_zero);
        conversion.push(coefficients);
        degree += 1;
    }
    conversion
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

fn ordinary_m31_to_natural_with_conversion(
    coefficients: &[M31; V5_MASK_M],
    conversion: &[Vec<M31>],
) -> [M31; V5_MASK_M] {
    let mut natural = [M31::ZERO; V5_MASK_M];
    let mut degree = 0;
    while degree < coefficients.len() {
        let coefficient = coefficients[degree];
        let mut index = 0;
        while index < conversion[degree].len() {
            let weight = conversion[degree][index];
            natural[index] = natural[index].add(coefficient.mul(weight));
            index += 1;
        }
        degree += 1;
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

/// Convert one semantic-lane mask from ordinary monomial coefficients to the
/// encoder's natural line-tensor coordinates, entirely over M31.
pub fn m31_block_mask_in_natural_basis(
    mask: &M31BlockMask,
) -> ([M31; V5_MASK_M], [M31; V5_MASK_M]) {
    let conversion = ordinary_monomials_in_natural_line_basis(V5_MASK_M);
    (
        ordinary_m31_to_natural_with_conversion(&mask.p, &conversion),
        ordinary_m31_to_natural_with_conversion(&mask.q, &conversion),
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

/// Mask one existing semantic M31 C1 column within its message coordinates.
///
/// Only rows `896..=991` receive the converted mask coefficients. Every other
/// row, in particular all active rows `0..=878`, is returned unchanged. This
/// does not create a new C1 column.
pub fn mask_m31_column(real: &[M31], mask: &M31BlockMask) -> Result<Vec<M31>, V5MaskError> {
    if real.len() != V5_TRACE_ROWS {
        return Err(V5MaskError::ColumnLength {
            expected: V5_TRACE_ROWS,
            actual: real.len(),
        });
    }
    let mut masked = Vec::with_capacity(real.len());
    let mut row = 0;
    while row < real.len() {
        masked.push(real[row]);
        row += 1;
    }
    let (natural_p, natural_q) = m31_block_mask_in_natural_basis(mask);
    let mut degree = 0;
    while degree < V5_MASK_M {
        masked[v5_reserved_p_index(degree)] =
            masked[v5_reserved_p_index(degree)].add(natural_p[degree]);
        masked[v5_reserved_q_index(degree)] =
            masked[v5_reserved_q_index(degree)].add(natural_q[degree]);
        degree += 1;
    }
    Ok(masked)
}

/// Encode one masked semantic lane through the real M31 C1 circle encoder.
pub fn encode_masked_m31_column(
    encoder: &CircleEncoder,
    masked: &[M31],
) -> Result<Vec<M31>, V5MaskError> {
    Ok(encoder.encode_c1_message(masked)?)
}

/// Build a QM31 diagnostic column `T̂ = T + B_896·R`.
///
/// The mask occupies exactly the aligned reserved rows, so `T̂` agrees with
/// `T` on every non-reserved row, including every active row. Ordinary
/// monomial coefficients are converted to natural line-tensor coefficients;
/// even offsets carry the pure-`x` block and odd offsets the `y` block.
/// Semantic C1 lanes must use [`mask_m31_column`] instead.
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

/// Encode a masked QM31 diagnostic column through the real circle encoder and
/// return the codeword. Semantic C1 lanes use [`encode_masked_m31_column`].
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
fn encoder_leakage_degree(
    encoder: &CircleEncoder,
    conversion_row: &[M31],
    codeword_index: usize,
) -> Result<(M31, M31), V5MaskError> {
    let mut p = M31::ZERO;
    let mut q = M31::ZERO;
    let mut natural = 0usize;
    while natural < conversion_row.len() {
        let weight = conversion_row[natural];
        let p_basis =
            encoder.encode_c1_basis_value(v5_reserved_p_index(natural), codeword_index)?;
        p = p.add(weight.mul(p_basis));
        let q_basis =
            encoder.encode_c1_basis_value(v5_reserved_q_index(natural), codeword_index)?;
        q = q.add(weight.mul(q_basis));
        natural += 1;
    }
    Ok((p, q))
}

pub fn encoder_leakage_row(
    encoder: &CircleEncoder,
    codeword_index: usize,
) -> Result<[QM31; V5_MASK_B], V5MaskError> {
    let conversion = ordinary_monomials_in_natural_line_basis(V5_MASK_M);
    let mut row = [QM31::ZERO; V5_MASK_B];
    let mut degree = 0usize;
    while degree < V5_MASK_M {
        let (p, q) = encoder_leakage_degree(encoder, &conversion[degree], codeword_index)?;
        row[degree] = qm31_from_m31(p);
        row[V5_MASK_M + degree] = qm31_from_m31(q);
        degree += 1;
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
        SecureCirclePoint {
            x: x.neg(),
            y: y.neg(),
        },
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

    fn sample_semantic_mask(seed: u64) -> M31BlockMask {
        let mut source = XorShift(seed);
        sample_m31_block_mask(&mut source).expect("sampler has ample budget")
    }

    fn embed_m31_mask(mask: &M31BlockMask) -> BlockMask {
        BlockMask {
            p: mask.p.map(qm31_from_m31),
            q: mask.q.map(qm31_from_m31),
        }
    }

    // Test-only copies of the pre-refactor iterator spellings. They are used
    // solely as differential oracles and are not reachable from production or
    // from either Charon start matcher.
    fn iterator_reference_atomic_coefficient_sum(mask: &M31BlockMask) -> M31 {
        mask.p
            .iter()
            .chain(mask.q.iter())
            .copied()
            .fold(M31::ZERO, M31::add)
    }

    fn iterator_reference_sample_atomic_m31_block_mask<S: Qm31WordSource>(
        source: &mut S,
    ) -> Result<M31BlockMask, MaskSampleExhausted> {
        let mut mask = M31BlockMask::ZERO;
        let mut sum = M31::ZERO;
        for coordinate in 0..V5_MASK_B {
            if coordinate == V5_ATOMIC_A_PIVOT_COORDINATE {
                continue;
            }
            let value = sample_m31(source)?;
            sum = sum.add(value);
            if coordinate < V5_MASK_M {
                mask.p[coordinate] = value;
            } else {
                mask.q[coordinate - V5_MASK_M] = value;
            }
        }
        mask.p[V5_ATOMIC_A_PIVOT_COORDINATE] = sum.neg();
        debug_assert_eq!(iterator_reference_atomic_coefficient_sum(&mask), M31::ZERO);
        Ok(mask)
    }

    fn iterator_reference_natural_line_basis_polynomials(size: usize) -> Vec<Vec<M31>> {
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

    fn iterator_reference_ordinary_monomials_in_natural_line_basis(size: usize) -> Vec<Vec<M31>> {
        let basis = iterator_reference_natural_line_basis_polynomials(size);
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

    fn iterator_reference_ordinary_m31_to_natural_with_conversion(
        coefficients: &[M31; V5_MASK_M],
        conversion: &[Vec<M31>],
    ) -> [M31; V5_MASK_M] {
        let mut natural = [M31::ZERO; V5_MASK_M];
        for (degree, coefficient) in coefficients.iter().copied().enumerate() {
            for (index, weight) in conversion[degree].iter().copied().enumerate() {
                natural[index] = natural[index].add(coefficient.mul(weight));
            }
        }
        natural
    }

    fn iterator_reference_m31_block_mask_in_natural_basis(
        mask: &M31BlockMask,
        conversion: &[Vec<M31>],
    ) -> ([M31; V5_MASK_M], [M31; V5_MASK_M]) {
        (
            iterator_reference_ordinary_m31_to_natural_with_conversion(&mask.p, conversion),
            iterator_reference_ordinary_m31_to_natural_with_conversion(&mask.q, conversion),
        )
    }

    fn iterator_reference_mask_m31_column(
        real: &[M31],
        mask: &M31BlockMask,
        conversion: &[Vec<M31>],
    ) -> Result<Vec<M31>, V5MaskError> {
        if real.len() != V5_TRACE_ROWS {
            return Err(V5MaskError::ColumnLength {
                expected: V5_TRACE_ROWS,
                actual: real.len(),
            });
        }
        let mut masked = real.to_vec();
        let (natural_p, natural_q) =
            iterator_reference_m31_block_mask_in_natural_basis(mask, conversion);
        for degree in 0..V5_MASK_M {
            masked[v5_reserved_p_index(degree)] =
                masked[v5_reserved_p_index(degree)].add(natural_p[degree]);
            masked[v5_reserved_q_index(degree)] =
                masked[v5_reserved_q_index(degree)].add(natural_q[degree]);
        }
        Ok(masked)
    }

    fn iterator_reference_encoder_leakage_row(
        encoder: &CircleEncoder,
        codeword_index: usize,
    ) -> Result<[QM31; V5_MASK_B], V5MaskError> {
        let conversion = ordinary_monomials_in_natural_line_basis(V5_MASK_M);
        let mut row = [QM31::ZERO; V5_MASK_B];
        for degree in 0..V5_MASK_M {
            let mut p = M31::ZERO;
            let mut q = M31::ZERO;
            for (natural, &weight) in conversion[degree].iter().enumerate() {
                p = p.add(weight.mul(
                    encoder.encode_c1_basis_value(v5_reserved_p_index(natural), codeword_index)?,
                ));
                q = q.add(weight.mul(
                    encoder.encode_c1_basis_value(v5_reserved_q_index(natural), codeword_index)?,
                ));
            }
            row[degree] = qm31_from_m31(p);
            row[V5_MASK_M + degree] = qm31_from_m31(q);
        }
        Ok(row)
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
            assert_eq!(
                encoder_leakage_row(&encoder, index),
                iterator_reference_encoder_leakage_row(&encoder, index),
                "indexed leakage evaluator differed from the iterator reference at {index}"
            );
        }
        assert_eq!(
            encoder_leakage_row(&encoder, V5_CODEWORD_LEN),
            iterator_reference_encoder_leakage_row(&encoder, V5_CODEWORD_LEN)
        );
    }

    // The v5-only row-256 helper is algebraically identical to every one of
    // the common encoder's 128 physical basis rows.  The positions include
    // both ends of the domain, butterfly boundaries, and non-power-of-two
    // interior positions; the fixture-level test in `v5_real_host_proof`
    // separately exercises all 72 accepted query/slot openings.
    #[test]
    fn row256_natural_helper_matches_real_encoder_rows() {
        let encoder = v5_encoder();
        let indices = [
            0usize,
            1,
            2,
            3,
            4,
            7,
            8,
            15,
            31,
            63,
            127,
            255,
            511,
            1_023,
            4_097,
            V5_CODEWORD_LEN / 7,
            V5_CODEWORD_LEN / 3,
            V5_CODEWORD_LEN / 2,
            V5_CODEWORD_LEN - 4,
            V5_CODEWORD_LEN - 1,
        ];
        for codeword_index in indices {
            for physical in 0..128 {
                let actual = qm31_from_m31(
                    encoder
                        .encode_c1_basis_value(256 + physical, codeword_index)
                        .unwrap(),
                );
                let factored =
                    row256_encoder_natural_basis_value(&encoder, physical, codeword_index).unwrap();
                assert_eq!(
                    actual, factored,
                    "row-256 factorisation failed at physical {physical}, codeword {codeword_index}"
                );
            }
        }
    }

    // Exhaustive finite-domain correspondence for the first-order v5 factor
    // constructor: every one of the 2^17 stored fibres and all four runtime
    // slots agree with the shared encoder's actual rows 256, 2 and 1.
    #[test]
    fn row256_slot_negations_match_original_branch_order() {
        for slot in 0..4 {
            assert_eq!(
                row256_constructor_slot_negations(slot),
                Some((slot >= 2, !(slot == 0 || slot == 3)))
            );
        }
        assert_eq!(row256_constructor_slot_negations(4), None);
    }

    #[test]
    fn row256_constructor_factors_match_real_encoder_exhaustively() {
        let encoder = v5_encoder();
        for stored_fibre in 0..(1usize << 17) {
            for slot in 0..4 {
                let position = 4 * stored_fibre + slot;
                let factors = row256_constructor_factors(stored_fibre, slot).unwrap();
                assert_eq!(
                    factors.factor,
                    encoder.encode_c1_basis_value(256, position).unwrap(),
                    "row 256 mismatch at stored fibre {stored_fibre}, slot {slot}"
                );
                assert_eq!(
                    factors.x,
                    encoder.encode_c1_basis_value(2, position).unwrap(),
                    "row 2 mismatch at stored fibre {stored_fibre}, slot {slot}"
                );
                assert_eq!(
                    factors.y,
                    encoder.encode_c1_basis_value(1, position).unwrap(),
                    "row 1 mismatch at stored fibre {stored_fibre}, slot {slot}"
                );
            }
        }
        assert_eq!(row256_constructor_factors(1usize << 17, 0), None);
        assert_eq!(row256_constructor_factors(0, 4), None);
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

    // (l) The semantic primitive samples exactly 48+48 canonical M31
    // coefficients and rejects the first non-canonical boundary value.
    #[test]
    fn m31_block_mask_sampler_is_field_native_and_canonical() {
        let mask = sample_semantic_mask(0x9f31_c1a5_0048_0048);
        for value in mask.p.iter().chain(mask.q.iter()) {
            assert!(value.0 < aspis_core::field::P);
        }

        struct RejectBoundaryOnce {
            calls: usize,
        }

        impl Qm31WordSource for RejectBoundaryOnce {
            fn next_word(&mut self) -> u32 {
                self.calls += 1;
                if self.calls == 1 {
                    aspis_core::field::P
                } else {
                    aspis_core::field::P - 1
                }
            }
        }

        let mut source = RejectBoundaryOnce { calls: 0 };
        assert_eq!(sample_m31(&mut source), Ok(M31(aspis_core::field::P - 1)));
        assert_eq!(
            source.calls, 2,
            "the non-canonical boundary was not rejected"
        );
    }

    #[test]
    fn indexed_aeneas_refactor_matches_iterator_reference() {
        let reference_basis = iterator_reference_natural_line_basis_polynomials(V5_MASK_M);
        assert_eq!(natural_line_basis_polynomials(V5_MASK_M), reference_basis);

        let reference_conversion =
            iterator_reference_ordinary_monomials_in_natural_line_basis(V5_MASK_M);
        assert_eq!(
            ordinary_monomials_in_natural_line_basis(V5_MASK_M),
            reference_conversion
        );

        let mut explicit = M31BlockMask::ZERO;
        explicit.p[0] = M31(3);
        explicit.p[V5_ATOMIC_A_PIVOT_COORDINATE] = M31(5);
        explicit.q[V5_MASK_M - 1] = M31(7);
        let mut masks = vec![explicit];
        for seed in [
            0x19e5_a31e_0000_0001,
            0x19e5_a31e_0000_0002,
            0x19e5_a31e_0000_0003,
        ] {
            masks.push(sample_semantic_mask(seed));
        }

        for (case, mask) in masks.iter().enumerate() {
            assert_eq!(
                atomic_m31_block_mask_coefficient_sum(mask),
                iterator_reference_atomic_coefficient_sum(mask),
                "coefficient sum differs in case {case}"
            );
            assert_eq!(
                m31_block_mask_in_natural_basis(mask),
                iterator_reference_m31_block_mask_in_natural_basis(mask, &reference_conversion),
                "conversion differs in case {case}"
            );

            let mut words = XorShift(0xd1ff_e7e5_0000_0000 ^ case as u64);
            let real: Vec<M31> = (0..V5_TRACE_ROWS)
                .map(|_| M31(words.next_word() & 0x3fff_ffff))
                .collect();
            assert_eq!(
                mask_m31_column(&real, mask),
                iterator_reference_mask_m31_column(&real, mask, &reference_conversion),
                "masked column differs in case {case}"
            );
        }

        let wrong_length = [M31::ONE; 7];
        assert_eq!(
            mask_m31_column(&wrong_length, &masks[0]),
            iterator_reference_mask_m31_column(&wrong_length, &masks[0], &reference_conversion)
        );
    }

    #[test]
    fn indexed_atomic_sampler_matches_flattened_iterator_reference() {
        #[derive(Clone, Debug, PartialEq, Eq)]
        struct RejectFirstThenCount {
            calls: usize,
            next: u32,
        }

        impl Qm31WordSource for RejectFirstThenCount {
            fn next_word(&mut self) -> u32 {
                self.calls += 1;
                if self.calls == 1 {
                    aspis_core::field::P
                } else {
                    let output = self.next;
                    self.next += 1;
                    output
                }
            }
        }

        let initial = RejectFirstThenCount {
            calls: 0,
            next: 100,
        };
        let mut indexed_source = initial.clone();
        let mut iterator_source = initial;
        let indexed = sample_atomic_m31_block_mask(&mut indexed_source);
        let iterator = iterator_reference_sample_atomic_m31_block_mask(&mut iterator_source);
        assert_eq!(indexed, iterator);
        assert_eq!(indexed_source, iterator_source);
        assert_eq!(indexed_source.calls, V5_ATOMIC_A_FREE_COORDINATES + 1);
        assert_eq!(
            indexed_source.next,
            100 + V5_ATOMIC_A_FREE_COORDINATES as u32
        );

        #[derive(Clone, Debug, PartialEq, Eq)]
        struct CountedExhaustion {
            calls: usize,
        }

        impl Qm31WordSource for CountedExhaustion {
            fn next_word(&mut self) -> u32 {
                self.calls += 1;
                aspis_core::field::P
            }
        }

        let mut indexed_exhaustion = CountedExhaustion { calls: 0 };
        let mut iterator_exhaustion = indexed_exhaustion.clone();
        assert_eq!(
            sample_atomic_m31_block_mask(&mut indexed_exhaustion),
            iterator_reference_sample_atomic_m31_block_mask(&mut iterator_exhaustion)
        );
        assert_eq!(indexed_exhaustion, iterator_exhaustion);
        assert_eq!(indexed_exhaustion.calls, V5_MASK_SAMPLE_RETRY_LIMIT);
    }

    // (m) The M31 ordinary-to-natural path reconstructs both ordinary
    // coefficient blocks exactly, without extension-field packing.
    #[test]
    fn m31_ordinary_to_natural_conversion_is_exact() {
        let mask = sample_semantic_mask(0xc10c_4d31_0a11_6e5f);
        let (natural_p, natural_q) = m31_block_mask_in_natural_basis(&mask);
        let basis = natural_line_basis_polynomials(V5_MASK_M);

        for (ordinary, expected) in [(&natural_p, &mask.p), (&natural_q, &mask.q)] {
            let mut reconstructed = [M31::ZERO; V5_MASK_M];
            for (natural_index, &natural_coefficient) in ordinary.iter().enumerate() {
                for (degree, &basis_coefficient) in basis[natural_index].iter().enumerate() {
                    reconstructed[degree] =
                        reconstructed[degree].add(natural_coefficient.mul(basis_coefficient));
                }
            }
            assert_eq!(&reconstructed, expected);
        }
    }

    // (n) The native message path changes only rows 896..=991 of an existing
    // M31 column and agrees with the aligned encoder model at codeword points.
    #[test]
    fn m31_masked_column_matches_the_aligned_encoder_model() {
        let real: Vec<M31> = (0..V5_TRACE_ROWS)
            .map(|row| M31((13 * row as u32 + 29) % aspis_core::field::P))
            .collect();
        let mask = sample_semantic_mask(0xa119_6ed0_31c1_8960);
        let (natural_p, natural_q) = m31_block_mask_in_natural_basis(&mask);
        let masked = mask_m31_column(&real, &mask).unwrap();

        for row in 0..V5_TRACE_ROWS {
            if !v5_reserved_rows().contains(&row) {
                assert_eq!(masked[row], real[row], "non-reserved row {row} changed");
            }
        }
        for degree in 0..V5_MASK_M {
            let p_row = v5_reserved_p_index(degree);
            let q_row = v5_reserved_q_index(degree);
            assert_eq!(masked[p_row], real[p_row].add(natural_p[degree]));
            assert_eq!(masked[q_row], real[q_row].add(natural_q[degree]));
        }

        let encoder = v5_encoder();
        let zero_masked = mask_m31_column(&[M31::ZERO; V5_TRACE_ROWS], &mask).unwrap();
        let codeword = encode_masked_m31_column(&encoder, &zero_masked).unwrap();
        assert_eq!(codeword.len(), V5_CODEWORD_LEN);
        assert_eq!(codeword.len(), V5_TRACE_ROWS * 512);
        let extension_mask = embed_m31_mask(&mask);
        let extension_coefficients: Vec<QM31> = extension_mask
            .p
            .iter()
            .chain(extension_mask.q.iter())
            .copied()
            .collect();

        for index in [
            0usize,
            1,
            17,
            511,
            65_537,
            V5_CODEWORD_LEN / 2 + 3,
            V5_CODEWORD_LEN - 1,
        ] {
            let x = encoder.encode_c1_basis_value(2, index).unwrap();
            let y = encoder.encode_c1_basis_value(1, index).unwrap();
            let factor = encoder
                .encode_c1_basis_value(V5_RESERVED_START, index)
                .unwrap();
            let expected = factor.mul(mask.evaluate(x, y));
            assert_eq!(codeword[index], expected, "M31 encoder mismatch at {index}");

            let aligned_row = encoder_factored_leakage_row(&encoder, index).unwrap();
            let extension_expected = aligned_row
                .iter()
                .zip(extension_coefficients.iter())
                .fold(QM31::ZERO, |sum, (&entry, &coefficient)| {
                    sum.add(entry.mul(coefficient))
                });
            assert_eq!(qm31_from_m31(codeword[index]), extension_expected);
        }
    }

    // (o) The fixed-width lane API consumes a separate source for each of the
    // sixteen semantic columns, returns exactly sixteen masks, and each mask
    // occupies only its own column's reserved rows.
    #[test]
    fn sixteen_semantic_lane_masks_use_separate_sources_and_layout() {
        #[derive(Clone, Copy)]
        struct LaneWords {
            next: u32,
            draws: usize,
        }

        impl Qm31WordSource for LaneWords {
            fn next_word(&mut self) -> u32 {
                let word = self.next;
                self.next += 1;
                self.draws += 1;
                word
            }
        }

        let mut sources: [LaneWords; V5_SEMANTIC_C1_LANES] =
            core::array::from_fn(|lane| LaneWords {
                next: 1_000 * (lane as u32 + 1),
                draws: 0,
            });
        let masks = sample_m31_lane_masks(&mut sources).unwrap();
        assert_eq!(masks.len(), V5_SEMANTIC_C1_LANES);

        for lane in 0..V5_SEMANTIC_C1_LANES {
            let base = 1_000 * (lane as u32 + 1);
            assert_eq!(sources[lane].draws, V5_MASK_B);
            for degree in 0..V5_MASK_M {
                assert_eq!(masks[lane].p[degree], M31(base + degree as u32));
                assert_eq!(
                    masks[lane].q[degree],
                    M31(base + V5_MASK_M as u32 + degree as u32)
                );
            }

            let real = vec![M31(lane as u32 + 41); V5_TRACE_ROWS];
            let masked = mask_m31_column(&real, &masks[lane]).unwrap();
            let (natural_p, natural_q) = m31_block_mask_in_natural_basis(&masks[lane]);
            for row in 0..V5_TRACE_ROWS {
                if !v5_reserved_rows().contains(&row) {
                    assert_eq!(masked[row], real[row], "lane {lane}, row {row}");
                }
            }
            for degree in 0..V5_MASK_M {
                let p_row = v5_reserved_p_index(degree);
                let q_row = v5_reserved_q_index(degree);
                assert_eq!(masked[p_row], real[p_row].add(natural_p[degree]));
                assert_eq!(masked[q_row], real[q_row].add(natural_q[degree]));
            }
        }

        for left in 0..V5_SEMANTIC_C1_LANES {
            for right in (left + 1)..V5_SEMANTIC_C1_LANES {
                assert_ne!(masks[left], masks[right]);
            }
        }
    }

    #[test]
    fn atomic_sampler_has_95_free_coordinates_and_zero_exact_inactive_sum() {
        use aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3;

        #[derive(Clone, Copy)]
        struct CountedWords {
            next: u32,
            draws: usize,
        }

        impl Qm31WordSource for CountedWords {
            fn next_word(&mut self) -> u32 {
                let output = self.next;
                self.next += 1;
                self.draws += 1;
                output
            }
        }

        let mut source = CountedWords {
            next: 100,
            draws: 0,
        };
        let mask = sample_atomic_m31_block_mask(&mut source).unwrap();
        assert_eq!(source.draws, V5_ATOMIC_A_FREE_COORDINATES);
        assert_eq!(atomic_m31_block_mask_coefficient_sum(&mask), M31::ZERO);

        let message = mask_m31_column(&[M31::ZERO; V5_TRACE_ROWS], &mask).unwrap();
        let inactive = atomic_state_only_copy_inactive_row_masks_v3();
        let inactive_sum = message
            .iter()
            .copied()
            .enumerate()
            .filter(|(row, _)| inactive[row >> 4] & (1 << (row & 15)) != 0)
            .fold(M31::ZERO, |sum, (_, value)| sum.add(value));
        assert_eq!(inactive_sum, M31::ZERO);
        assert!((V5_RESERVED_START..=V5_RESERVED_END)
            .all(|row| inactive[row >> 4] & (1 << (row & 15)) != 0));
    }

    #[test]
    fn sixteen_atomic_lane_masks_are_independently_conditioned() {
        #[derive(Clone, Copy)]
        struct LaneWords {
            next: u32,
            draws: usize,
        }

        impl Qm31WordSource for LaneWords {
            fn next_word(&mut self) -> u32 {
                let output = self.next;
                self.next += 1;
                self.draws += 1;
                output
            }
        }

        let mut sources: [LaneWords; V5_SEMANTIC_C1_LANES] =
            core::array::from_fn(|lane| LaneWords {
                next: 10_000 * (lane as u32 + 1),
                draws: 0,
            });
        let masks = sample_atomic_m31_lane_masks(&mut sources).unwrap();
        for lane in 0..V5_SEMANTIC_C1_LANES {
            assert_eq!(sources[lane].draws, V5_ATOMIC_A_FREE_COORDINATES);
            assert_eq!(
                atomic_m31_block_mask_coefficient_sum(&masks[lane]),
                M31::ZERO
            );
        }
        for left in 0..V5_SEMANTIC_C1_LANES {
            for right in left + 1..V5_SEMANTIC_C1_LANES {
                assert_ne!(masks[left], masks[right]);
            }
        }
    }
}

#[cfg(test)]
#[path = "v5_a_full_view_rank.rs"]
mod v5_a_full_view_rank;

#[cfg(test)]
#[path = "v5_b_structured_rank.rs"]
mod v5_b_structured_rank;
