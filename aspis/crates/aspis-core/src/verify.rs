//! The on-chain verifier logic (also the host reference — byte-exact shared
//! code path).
//!
//! What this proves, stated precisely (Stage 1 OOD-binding revision): transcript-bound
//! local fold consistency of a committed evaluation table down to an explicit
//! final polynomial, with grinding, against a bound statement digest, plus
//! transcript-derived per-round OOD points and an interleaved degree-6
//! sumcheck that enforces the OOD and external evaluation relations against
//! the explicit final coefficients. Version 3 also authenticates a
//! post-challenge C2 and folds its gamma-RLC with C1. It is not paper WHIR;
//! the soundness note states the exact assumption and remaining statement
//! layer delta.

use alloc::vec;
use alloc::vec::Vec;

use crate::field::{cm31_batch_inverse_with, CM31, M31, M31_QUARTER, QM31};
use crate::merkle::{
    leaf_hash, verify_minimal_subtree_bytes, verify_radix4_minimal_subtree_bytes,
    verify_single_path_bytes,
};
use crate::params::{
    profile_by_id, FoldPayload, MerkleMode, Profile, CIRCLE_GEN, CIRCLE_LOG_ORDER,
    FINAL_POLY_LOG_LEN, FOLD_VARS,
};
use crate::proof::{
    fiber_value_bytes, Cursor, Header, HEADER_LEN, OOD_VALUE_LEN, SECOND_PHASE_LAYER_TAG,
};
use crate::sumcheck::{
    boundary_sum as sumcheck_boundary, evaluate as evaluate_sumcheck, SumcheckPolynomial,
    WeightAccumulator, SUMCHECK_BYTES,
};
use crate::transcript::{label, HashFn, OodSampleError, Transcript};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum VerifyError {
    BadHeader,
    UnknownProfile,
    HeaderProfileMismatch,
    BadLength,
    NonCanonicalValue,
    GrindingFailed,
    UniqueCountMismatch {
        layer: u8,
    },
    MerkleMismatch {
        layer: u8,
    },
    SlotMismatch {
        layer: u8,
    },
    CarriedFoldMismatch {
        layer: u8,
    },
    FinalPolyMismatch,
    TrailingBytes,
    /// Bounded rejection-sampling retries exhausted while deriving a QM31
    /// challenge (2^-248 per limb; soundness-note §3 T9 / §6 completeness).
    ChallengeSampleExhausted,
    /// Proof header declares an evaluation claim but the caller supplied none.
    ClaimMissing,
    /// Caller supplied an evaluation claim but the proof header declares none.
    ClaimUnexpected,
    /// Claim point dimension does not match the profile's variable count.
    ClaimShape,
    /// The bounded sampler could not obtain a point outside the CM31
    /// subfield after three draws (honest probability below 2^-186).
    OodSampleExhausted,
    /// A round polynomial does not sum to the incoming batched relation.
    SumcheckBoundaryMismatch {
        layer: u8,
    },
    /// The reduced relation does not hold on the explicit final coefficients.
    EvaluationRelationMismatch,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TraceEvent {
    Start,
    HeaderParsed,
    TranscriptReady,
    LayerOodDone(u8),
    LayerSumcheckDone(u8),
    QueriesReady,
    LayerStart(u8),
    LayerMerkleDone(u8),
    LayerFoldDone(u8),
    FinalCheckStart,
    Done,
}

pub type TraceFn = fn(TraceEvent);
pub type M31InverseFn = fn(M31) -> M31;

#[derive(Clone, Copy)]
enum DenominatorBackend {
    /// Circle points have norm one, so their inverse is their conjugate.
    CircleConjugate,
    /// Retained for literal SBF comparisons and non-circle callers.
    BatchInverse(M31InverseFn),
}

#[inline(always)]
fn trace(trace: Option<TraceFn>, event: TraceEvent) {
    if let Some(trace) = trace {
        trace(event);
    }
}

impl VerifyError {
    /// Stable numeric code (used as the SBF program's custom error code).
    pub fn code(&self) -> u32 {
        match self {
            VerifyError::BadHeader => 1,
            VerifyError::UnknownProfile => 2,
            VerifyError::HeaderProfileMismatch => 3,
            VerifyError::BadLength => 4,
            VerifyError::NonCanonicalValue => 5,
            VerifyError::GrindingFailed => 6,
            VerifyError::UniqueCountMismatch { .. } => 7,
            VerifyError::MerkleMismatch { .. } => 8,
            VerifyError::SlotMismatch { .. } => 9,
            VerifyError::CarriedFoldMismatch { .. } => 10,
            VerifyError::FinalPolyMismatch => 11,
            VerifyError::TrailingBytes => 12,
            VerifyError::ChallengeSampleExhausted => 13,
            VerifyError::ClaimMissing => 14,
            VerifyError::ClaimUnexpected => 15,
            VerifyError::ClaimShape => 16,
            VerifyError::OodSampleExhausted => 17,
            VerifyError::SumcheckBoundaryMismatch { .. } => 18,
            VerifyError::EvaluationRelationMismatch => 19,
        }
    }
}

/// Per-layer domain geometry, derived from the circle group generator.
#[derive(Clone, Copy)]
pub struct LayerGeometry {
    /// generator of the layer's domain subgroup (order = domain size)
    pub omega: CM31,
    /// coset offset (order = 2 * domain size)
    pub offset: CM31,
    /// order-4 element omega^(fiber_count) used for fiber points
    pub iota: CM31,
    pub domain_size: u32,
    pub fiber_count: u32,
    pub log_fiber_count: u32,
}

pub fn layer_geometry(profile: &Profile, layer: u32) -> LayerGeometry {
    let log_domain = profile.log_rows + profile.log_blowup - FOLD_VARS * layer;
    let domain_size = 1u32 << log_domain;
    // CIRCLE_GEN has order 2^31; omega = G^(2^31 / N) has order N.
    let omega = CIRCLE_GEN.pow(1u64 << (CIRCLE_LOG_ORDER - log_domain));
    // offset has order 2N so the coset offset*<omega> avoids the subgroup.
    let offset = CIRCLE_GEN.pow(1u64 << (CIRCLE_LOG_ORDER - log_domain - 1));
    let fiber_count = domain_size >> FOLD_VARS;
    let iota = omega.pow(fiber_count as u64);
    LayerGeometry {
        omega,
        offset,
        iota,
        domain_size,
        fiber_count,
        log_fiber_count: log_domain - FOLD_VARS,
    }
}

/// Point at natural index `i` of the layer's domain: offset * omega^i.
pub fn domain_point(geom: &LayerGeometry, index: u32) -> CM31 {
    geom.offset.mul(geom.omega.pow(index as u64))
}

/// Per-verification window table for the public circle domain. The old path
/// recomputed the same sequence of omega squares for every queried fiber.
/// This table computes them once for layer zero, then advances layers by
/// shifting the table because omega_(r+1) = omega_r^4.
struct DomainPowerTable {
    geometry: LayerGeometry,
    omega_powers: [CM31; CIRCLE_LOG_ORDER as usize],
}

impl DomainPowerTable {
    fn new(profile: &Profile) -> Self {
        let geometry = layer_geometry(profile, 0);
        let mut omega_powers = [CM31::ONE; CIRCLE_LOG_ORDER as usize];
        omega_powers[0] = geometry.omega;
        for bit in 1..omega_powers.len() {
            omega_powers[bit] = omega_powers[bit - 1].square();
        }
        Self {
            geometry,
            omega_powers,
        }
    }

    #[inline(always)]
    fn point(&self, mut index: u32) -> CM31 {
        debug_assert!(index < self.geometry.domain_size);
        let mut point = self.geometry.offset;
        let mut bit = 0usize;
        while index != 0 {
            if index & 1 != 0 {
                point = point.mul(self.omega_powers[bit]);
            }
            index >>= 1;
            bit += 1;
        }
        point
    }

    fn fold_layer(&mut self) {
        for bit in 0..self.omega_powers.len() - FOLD_VARS as usize {
            self.omega_powers[bit] = self.omega_powers[bit + FOLD_VARS as usize];
        }
        for bit in self.omega_powers.len() - FOLD_VARS as usize..self.omega_powers.len() {
            self.omega_powers[bit] = CM31::ONE;
        }
        self.geometry.omega = self.omega_powers[0];
        self.geometry.offset = self.geometry.offset.square().square();
        self.geometry.domain_size >>= FOLD_VARS;
        self.geometry.fiber_count >>= FOLD_VARS;
        self.geometry.log_fiber_count -= FOLD_VARS;
        // iota = omega^(domain_size/4) is the same order-four circle
        // element at every layer, so it is intentionally unchanged.
    }
}

#[derive(Clone, Copy)]
enum Fiber {
    Base([CM31; 4]),
    Ext([QM31; 4]),
}

impl Fiber {
    fn get(&self, slot: u32) -> QM31 {
        match self {
            Fiber::Base(v) => QM31::from_cm31(v[slot as usize]),
            Fiber::Ext(v) => v[slot as usize],
        }
    }
}

fn parse_fiber(bytes: &[u8], layer: u32) -> Result<Fiber, VerifyError> {
    if layer == 0 {
        let mut v = [CM31::ZERO; 4];
        for (k, chunk) in bytes.chunks_exact(8).enumerate() {
            v[k] = CM31::from_le_bytes(chunk).ok_or(VerifyError::NonCanonicalValue)?;
        }
        Ok(Fiber::Base(v))
    } else {
        let mut v = [QM31::ZERO; 4];
        for (k, chunk) in bytes.chunks_exact(16).enumerate() {
            v[k] = QM31::from_le_bytes(chunk).ok_or(VerifyError::NonCanonicalValue)?;
        }
        Ok(Fiber::Ext(v))
    }
}

fn parse_extension_fiber(bytes: &[u8]) -> Result<[QM31; 4], VerifyError> {
    let mut values = [QM31::ZERO; 4];
    for (index, chunk) in bytes.chunks_exact(16).enumerate() {
        values[index] = QM31::from_le_bytes(chunk).ok_or(VerifyError::NonCanonicalValue)?;
    }
    Ok(values)
}

fn combine_first_phase_fibers(
    main: &Fiber,
    helper: [QM31; 4],
    gamma: QM31,
) -> Result<Fiber, VerifyError> {
    let Fiber::Base(main) = main else {
        return Err(VerifyError::BadHeader);
    };
    let mut combined = [QM31::ZERO; 4];
    for index in 0..4 {
        combined[index] = QM31::from_cm31(main[index]).add(gamma.mul(helper[index]));
    }
    Ok(Fiber::Ext(combined))
}

#[allow(clippy::too_many_arguments)]
fn verify_merkle_section(
    cursor: &mut Cursor<'_>,
    hash: HashFn,
    merkle_mode: MerkleMode,
    root: &[u8; 32],
    depth: u32,
    unique: &[u32],
    values_section: &[u8],
    value_bytes: usize,
    layer_tag: u8,
    error_layer: u8,
    entries: &mut Vec<(u32, [u8; 32])>,
    merkle_level: &mut Vec<(u32, [u8; 32])>,
    merkle_next: &mut Vec<(u32, [u8; 32])>,
) -> Result<(), VerifyError> {
    match merkle_mode {
        MerkleMode::SinglePaths => {
            for (index, &fiber_index) in unique.iter().enumerate() {
                let leaf = leaf_hash(
                    hash,
                    layer_tag,
                    &values_section[index * value_bytes..(index + 1) * value_bytes],
                );
                let path_bytes = cursor
                    .take(depth as usize * 32)
                    .ok_or(VerifyError::BadLength)?;
                if !verify_single_path_bytes(hash, root, depth, fiber_index, leaf, path_bytes) {
                    return Err(VerifyError::MerkleMismatch { layer: error_layer });
                }
            }
        }
        MerkleMode::MinimalSubtree => {
            let node_count = cursor.take_u32().ok_or(VerifyError::BadLength)? as usize;
            let node_bytes = cursor.take(node_count * 32).ok_or(VerifyError::BadLength)?;
            entries.clear();
            for (index, &fiber_index) in unique.iter().enumerate() {
                entries.push((
                    fiber_index,
                    leaf_hash(
                        hash,
                        layer_tag,
                        &values_section[index * value_bytes..(index + 1) * value_bytes],
                    ),
                ));
            }
            if !verify_minimal_subtree_bytes(
                hash,
                root,
                depth,
                entries,
                node_bytes,
                merkle_level,
                merkle_next,
            ) {
                return Err(VerifyError::MerkleMismatch { layer: error_layer });
            }
        }
        MerkleMode::Radix4MinimalSubtree => {
            let node_count = cursor.take_u32().ok_or(VerifyError::BadLength)? as usize;
            let node_bytes = cursor.take(node_count * 32).ok_or(VerifyError::BadLength)?;
            entries.clear();
            for (index, &fiber_index) in unique.iter().enumerate() {
                entries.push((
                    fiber_index,
                    leaf_hash(
                        hash,
                        layer_tag,
                        &values_section[index * value_bytes..(index + 1) * value_bytes],
                    ),
                ));
            }
            if !verify_radix4_minimal_subtree_bytes(
                hash,
                root,
                depth,
                entries,
                node_bytes,
                merkle_level,
                merkle_next,
            ) {
                return Err(VerifyError::MerkleMismatch { layer: error_layer });
            }
        }
    }
    Ok(())
}

/// Fold one fiber with challenge alpha at slot-0 point `s`, given batched
/// inverses of (2s, 2*iota*s, 2s^2). Late-lift arithmetic throughout.
#[allow(clippy::too_many_arguments)]
fn fold_fiber(
    fiber: &Fiber,
    alpha: QM31,
    alpha2: QM31,
    inv_2s: CM31,
    inv_2is: CM31,
    inv_2s2: CM31,
) -> QM31 {
    let (g1, g2) = match fiber {
        Fiber::Base(v) => {
            let sum02 = v[0].add(v[2]);
            let dif02 = v[0].sub(v[2]);
            let sum13 = v[1].add(v[3]);
            let dif13 = v[1].sub(v[3]);
            let g1 = QM31::from_cm31(sum02.half()).add(alpha.mul_cm31(dif02.mul(inv_2s)));
            let g2 = QM31::from_cm31(sum13.half()).add(alpha.mul_cm31(dif13.mul(inv_2is)));
            (g1, g2)
        }
        Fiber::Ext(v) => {
            let sum02 = v[0].add(v[2]);
            let dif02 = v[0].sub(v[2]);
            let sum13 = v[1].add(v[3]);
            let dif13 = v[1].sub(v[3]);
            let g1 = sum02.half().add(alpha.mul(dif02.mul_cm31(inv_2s)));
            let g2 = sum13.half().add(alpha.mul(dif13.mul_cm31(inv_2is)));
            (g1, g2)
        }
    };
    let sum = g1.add(g2);
    let dif = g1.sub(g2);
    sum.half().add(alpha2.mul(dif.mul_cm31(inv_2s2)))
}

/// Division-free carried-payload checks for one fiber (proof_carried_round_local).
/// Returns (ok_of_intra_round_checks, deferred) where `deferred` carries what
/// check3 needs once the next layer's value is known:
///   h * 2s^2 == s^2*(g1+g2) + alpha^2*(g1-g2)
#[derive(Clone, Copy)]
struct CarriedDeferred {
    two_s2: CM31,
    rhs: QM31,
}

fn carried_checks(
    fiber: &Fiber,
    g1: QM31,
    g2: QM31,
    alpha: QM31,
    alpha2: QM31,
    s: CM31,
    iota: CM31,
) -> (bool, CarriedDeferred) {
    let is = s.mul(iota);
    let two_s = s.double();
    let two_is = is.double();
    let s2 = s.square();
    let ok = match fiber {
        Fiber::Base(v) => {
            let c1 = g1.mul_cm31(two_s)
                == QM31::from_cm31(v[0].add(v[2]).mul(s)).add(alpha.mul_cm31(v[0].sub(v[2])));
            let c2 = g2.mul_cm31(two_is)
                == QM31::from_cm31(v[1].add(v[3]).mul(is)).add(alpha.mul_cm31(v[1].sub(v[3])));
            c1 && c2
        }
        Fiber::Ext(v) => {
            let c1 =
                g1.mul_cm31(two_s) == v[0].add(v[2]).mul_cm31(s).add(alpha.mul(v[0].sub(v[2])));
            let c2 =
                g2.mul_cm31(two_is) == v[1].add(v[3]).mul_cm31(is).add(alpha.mul(v[1].sub(v[3])));
            c1 && c2
        }
    };
    let rhs = g1.add(g2).mul_cm31(s2).add(alpha2.mul(g1.sub(g2)));
    (
        ok,
        CarriedDeferred {
            two_s2: s2.double(),
            rhs,
        },
    )
}

/// Externally supplied evaluation claim "w(z) = v" for the multilinear
/// reading of C1. It is absorbed as a PUBLIC INPUT (never proof bytes) after
/// C2 and before gamma. The proof carries C2's evaluation at the same point;
/// the interleaved relation sumcheck enforces their gamma-combination.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvaluationClaim {
    /// Evaluation point, one coordinate per variable (len == log_rows).
    pub z: Vec<QM31>,
    /// Claimed value of the multilinear at z.
    pub v: QM31,
}

impl EvaluationClaim {
    /// Canonical absorption bytes: z coordinates then v, LE.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = vec![0u8; (self.z.len() + 1) * 16];
        for (k, zi) in self.z.iter().enumerate() {
            zi.write_le_bytes(&mut out[k * 16..k * 16 + 16]);
        }
        let tail = self.z.len() * 16;
        self.v.write_le_bytes(&mut out[tail..tail + 16]);
        out
    }
}

/// Host/SBF-pinned outputs of [`ood_sample_relation_probe`] for the frozen
/// lr10/four-round measurement shape. These are a probe-local conformance
/// pin; they do not replace or modify the production transcript KAT.
pub const OOD_SAMPLE_PROBE_S1_EXPECTED: [u8; 16] = [
    0xb1, 0x5f, 0x05, 0x55, 0xd1, 0xf6, 0xb3, 0x1b, 0x38, 0x6d, 0x0c, 0x65, 0x0c, 0x09, 0xcc, 0x76,
];
pub const OOD_SAMPLE_PROBE_S2_EXPECTED: [u8; 16] = [
    0xfe, 0x80, 0x15, 0x42, 0xf7, 0x2b, 0xf7, 0x76, 0xfc, 0x0b, 0xaa, 0x75, 0x50, 0x53, 0x09, 0x07,
];

#[inline(always)]
fn sample_ood_point(transcript: &mut Transcript) -> Result<QM31, VerifyError> {
    match transcript.challenge_ood_qm31() {
        Ok(point) => Ok(point),
        Err(OodSampleError::ChallengeSampleExhausted) => Err(VerifyError::ChallengeSampleExhausted),
        Err(OodSampleError::SubfieldSampleExhausted) => Err(VerifyError::OodSampleExhausted),
    }
}

#[inline(always)]
fn absorb_ood_value_and_accumulate(
    transcript: &mut Transcript,
    point: QM31,
    encoded_value: &[u8; OOD_VALUE_LEN],
    relation_value: &mut QM31,
    relation_weights: &mut WeightAccumulator,
) -> Result<(), VerifyError> {
    let value = QM31::from_le_bytes(encoded_value).ok_or(VerifyError::NonCanonicalValue)?;
    transcript.absorb(label::OOD_VALUE, encoded_value);
    let mix = transcript
        .challenge_qm31()
        .map_err(|_| VerifyError::ChallengeSampleExhausted)?;
    *relation_value = relation_value.add(mix.mul(value));
    relation_weights.add_geometric(mix, point);
    Ok(())
}

/// Execute one canonical `(beta, y, mu)` OOD relation sample. Production
/// verification and the isolated SBF A/B probe share this exact kernel so
/// the probe prices the same sampler, canonical decode, transcript absorbs,
/// relation update, and structured-weight insertion.
#[doc(hidden)]
#[inline(always)]
pub fn accumulate_canonical_ood_sample(
    transcript: &mut Transcript,
    encoded_value: &[u8; OOD_VALUE_LEN],
    relation_value: &mut QM31,
    relation_weights: &mut WeightAccumulator,
) -> Result<(), VerifyError> {
    let point = sample_ood_point(transcript)?;
    absorb_ood_value_and_accumulate(
        transcript,
        point,
        encoded_value,
        relation_value,
        relation_weights,
    )
}

fn ood_probe_value(index: u32, lane: u32) -> QM31 {
    let limb = |offset: u32| M31(1 + index.wrapping_mul(131).wrapping_add(offset) % 1_000_003);
    QM31 {
        c0: CM31 {
            a: limb(lane * 17),
            b: limb(lane * 17 + 3),
        },
        c1: CM31 {
            a: limb(lane * 17 + 7),
            b: limb(lane * 17 + 11),
        },
    }
}

// Fixed canonical encodings of `ood_probe_value(index, 3)` for index 0..8.
// Production receives these bytes from the proof; keeping them pre-encoded
// prevents the s=2 A/B row from paying four probe-only value constructions
// and serializations that the production verifier never performs.
const OOD_PROBE_ENCODED_VALUES: [[u8; OOD_VALUE_LEN]; 8] = [
    [0x34, 0, 0, 0, 0x37, 0, 0, 0, 0x3b, 0, 0, 0, 0x3f, 0, 0, 0],
    [0xb7, 0, 0, 0, 0xba, 0, 0, 0, 0xbe, 0, 0, 0, 0xc2, 0, 0, 0],
    [
        0x3a, 0x01, 0, 0, 0x3d, 0x01, 0, 0, 0x41, 0x01, 0, 0, 0x45, 0x01, 0, 0,
    ],
    [
        0xbd, 0x01, 0, 0, 0xc0, 0x01, 0, 0, 0xc4, 0x01, 0, 0, 0xc8, 0x01, 0, 0,
    ],
    [
        0x40, 0x02, 0, 0, 0x43, 0x02, 0, 0, 0x47, 0x02, 0, 0, 0x4b, 0x02, 0, 0,
    ],
    [
        0xc3, 0x02, 0, 0, 0xc6, 0x02, 0, 0, 0xca, 0x02, 0, 0, 0xce, 0x02, 0, 0,
    ],
    [
        0x46, 0x03, 0, 0, 0x49, 0x03, 0, 0, 0x4d, 0x03, 0, 0, 0x51, 0x03, 0, 0,
    ],
    [
        0xc9, 0x03, 0, 0, 0xcc, 0x03, 0, 0, 0xd0, 0x03, 0, 0, 0xd4, 0x03, 0, 0,
    ],
];

/// Isolated verifier-work probe for one versus two sequential OOD samples.
///
/// The fixed shape matches the payment target: log_rows=10, four arity-4
/// folds, a four-coefficient terminal polynomial, and one already-live
/// multilinear evaluation-claim component. It deliberately excludes proof
/// openings and query derivation so the A/B delta cannot be contaminated by
/// transcript-induced Merkle/query variance.
#[doc(hidden)]
pub fn ood_sample_relation_probe(hash: HashFn, samples_per_round: u8) -> Result<QM31, VerifyError> {
    const LOG_ROWS: u32 = 10;
    const ROUNDS: u8 = 4;
    if samples_per_round != 1 && samples_per_round != 2 {
        return Err(VerifyError::BadHeader);
    }

    let claim = EvaluationClaim {
        z: (0..LOG_ROWS)
            .map(|coordinate| ood_probe_value(coordinate, 1))
            .collect(),
        v: ood_probe_value(97, 2),
    };
    let mut relation_weights = WeightAccumulator::from_claim(LOG_ROWS, Some(&claim));
    let mut relation_value = claim.v;
    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, b"aspis-s2-ood-relation-cu-probe-v1");
    transcript.absorb(label::STATEMENT, &[0x5au8; 32]);

    for layer in 0..ROUNDS {
        transcript.absorb(label::ROOT, &[0x10 + layer; 32]);
        for sample in 0..samples_per_round {
            let encoded_value =
                &OOD_PROBE_ENCODED_VALUES[usize::from(layer) * 2 + usize::from(sample)];
            accumulate_canonical_ood_sample(
                &mut transcript,
                encoded_value,
                &mut relation_value,
                &mut relation_weights,
            )?;
        }

        // A constant degree-0 message is still a valid member of the
        // verifier's degree-6 envelope. Its boundary is made exactly equal
        // to the accumulated relation so the probe follows the accepting
        // verifier branch before folding every live weight component.
        let mut sumcheck = [QM31::ZERO; 7];
        sumcheck[0] = relation_value.mul_m31(M31_QUARTER);
        if sumcheck_boundary(&sumcheck) != relation_value {
            return Err(VerifyError::SumcheckBoundaryMismatch { layer });
        }
        let mut sumcheck_bytes = [0u8; SUMCHECK_BYTES];
        for (index, coefficient) in sumcheck.iter().enumerate() {
            coefficient.write_le_bytes(&mut sumcheck_bytes[index * 16..index * 16 + 16]);
        }
        transcript.absorb(label::SUMCHECK_POLY, &sumcheck_bytes);
        let alpha = transcript
            .challenge_qm31()
            .map_err(|_| VerifyError::ChallengeSampleExhausted)?;
        relation_value = evaluate_sumcheck(&sumcheck, alpha);
        relation_weights.fold(alpha);
    }

    let final_values: [QM31; 4] =
        core::array::from_fn(|index| ood_probe_value(200 + index as u32, 4));
    let terminal = relation_weights.dot(&final_values);
    Ok(terminal.add(relation_value))
}

/// Verify a proof against a statement digest. `hash` is the SHA-256 backend
/// (syscall on SBF, sha2 on host).
pub fn verify(proof: &[u8], statement_digest: &[u8; 32], hash: HashFn) -> Result<(), VerifyError> {
    verify_with_claim_and_trace(proof, statement_digest, None, hash, None)
}

/// Verify a claim-carrying proof.
pub fn verify_with_claim(
    proof: &[u8],
    statement_digest: &[u8; 32],
    claim: Option<&EvaluationClaim>,
    hash: HashFn,
) -> Result<(), VerifyError> {
    verify_with_claim_and_trace(proof, statement_digest, claim, hash, None)
}

/// Verify with optional diagnostic trace events. The trace hook is for SBF CU
/// profiling only; normal verification calls `verify`.
pub fn verify_with_trace(
    proof: &[u8],
    statement_digest: &[u8; 32],
    hash: HashFn,
    trace_fn: Option<TraceFn>,
) -> Result<(), VerifyError> {
    verify_with_claim_and_trace(proof, statement_digest, None, hash, trace_fn)
}

pub fn verify_with_claim_and_trace(
    proof: &[u8],
    statement_digest: &[u8; 32],
    claim: Option<&EvaluationClaim>,
    hash: HashFn,
    trace_fn: Option<TraceFn>,
) -> Result<(), VerifyError> {
    verify_inner(
        proof,
        statement_digest,
        claim,
        hash,
        trace_fn,
        OrderingPolicy::Canonical,
        DenominatorBackend::CircleConjugate,
    )
}

/// Verify with an injected base-field inversion backend. The verifier uses
/// it once per fold round through CM31 batch inversion; host callers keep the
/// software default while SBF can select the native modular-exponentiation
/// syscall.
pub fn verify_with_claim_trace_and_inverse(
    proof: &[u8],
    statement_digest: &[u8; 32],
    claim: Option<&EvaluationClaim>,
    hash: HashFn,
    trace_fn: Option<TraceFn>,
    inverse: M31InverseFn,
) -> Result<(), VerifyError> {
    verify_inner(
        proof,
        statement_digest,
        claim,
        hash,
        trace_fn,
        OrderingPolicy::Canonical,
        DenominatorBackend::BatchInverse(inverse),
    )
}

/// Deliberately insecure schedules used only to prove that the canonical
/// challenge-order tests have teeth. This API does not exist unless the
/// explicit test feature is enabled.
#[cfg(feature = "insecure-test-ordering")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InsecureOrdering {
    ChiBeforeC1,
    GammaBeforeClaims,
    OodAfterFoldChallenge,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OrderingPolicy {
    Canonical,
    #[cfg(feature = "insecure-test-ordering")]
    ChiBeforeC1,
    #[cfg(feature = "insecure-test-ordering")]
    GammaBeforeClaims,
    #[cfg(feature = "insecure-test-ordering")]
    OodAfterFoldChallenge,
}

impl OrderingPolicy {
    fn chi_before_c1(self) -> bool {
        #[cfg(feature = "insecure-test-ordering")]
        if self == Self::ChiBeforeC1 {
            return true;
        }
        false
    }

    fn gamma_before_claims(self) -> bool {
        #[cfg(feature = "insecure-test-ordering")]
        if self == Self::GammaBeforeClaims {
            return true;
        }
        false
    }

    fn ood_after_fold_challenge(self) -> bool {
        #[cfg(feature = "insecure-test-ordering")]
        if self == Self::OodAfterFoldChallenge {
            return true;
        }
        false
    }
}

#[cfg(feature = "insecure-test-ordering")]
pub fn verify_with_insecure_ordering(
    proof: &[u8],
    statement_digest: &[u8; 32],
    claim: Option<&EvaluationClaim>,
    hash: HashFn,
    ordering: InsecureOrdering,
) -> Result<(), VerifyError> {
    let policy = match ordering {
        InsecureOrdering::ChiBeforeC1 => OrderingPolicy::ChiBeforeC1,
        InsecureOrdering::GammaBeforeClaims => OrderingPolicy::GammaBeforeClaims,
        InsecureOrdering::OodAfterFoldChallenge => OrderingPolicy::OodAfterFoldChallenge,
    };
    verify_inner(
        proof,
        statement_digest,
        claim,
        hash,
        None,
        policy,
        DenominatorBackend::CircleConjugate,
    )
}

fn verify_inner(
    proof: &[u8],
    statement_digest: &[u8; 32],
    claim: Option<&EvaluationClaim>,
    hash: HashFn,
    trace_fn: Option<TraceFn>,
    ordering: OrderingPolicy,
    denominator_backend: DenominatorBackend,
) -> Result<(), VerifyError> {
    trace(trace_fn, TraceEvent::Start);
    let header = Header::parse(proof).ok_or(VerifyError::BadHeader)?;
    let profile = profile_by_id(header.profile_id).ok_or(VerifyError::UnknownProfile)?;
    if header.log_rows != profile.log_rows
        || header.log_blowup != profile.log_blowup
        || header.query_count != profile.query_count
        || header.grinding_bits != profile.grinding_bits
        || header.num_rounds != profile.num_rounds()
        || header.final_poly_log_len != FINAL_POLY_LOG_LEN
    {
        return Err(VerifyError::HeaderProfileMismatch);
    }
    let fold_payload = FoldPayload::from_u8(header.fold_payload).ok_or(VerifyError::BadHeader)?;
    let merkle_mode = MerkleMode::from_u8(header.merkle_mode).ok_or(VerifyError::BadHeader)?;
    // Claim flag and supplied claim must agree, and the point dimension must
    // match the profile — before anything is derived. Version 3 requires C2
    // for claim-carrying proofs so gamma can bind both evaluations.
    match (header.has_claim(), claim) {
        (false, None) => {}
        (true, Some(claim)) => {
            if claim.z.len() != profile.log_rows as usize {
                return Err(VerifyError::ClaimShape);
            }
        }
        (true, None) => return Err(VerifyError::ClaimMissing),
        (false, Some(_)) => return Err(VerifyError::ClaimUnexpected),
    }
    if header.has_claim() && !header.has_second_phase() {
        return Err(VerifyError::BadHeader);
    }
    trace(trace_fn, TraceEvent::HeaderParsed);

    let num_rounds = profile.num_rounds();
    let query_count = profile.query_count as usize;

    let mut cursor = Cursor::new(proof);
    let header_bytes = cursor.take(HEADER_LEN).ok_or(VerifyError::BadLength)?;

    // ---- transcript phase ----
    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, header_bytes);
    transcript.absorb(label::STATEMENT, statement_digest);

    // The insecure chi-before-C1 policy deliberately squeezes these values
    // before C1. Canonical verification takes the same two squeezes only
    // after the first root has been absorbed.
    if header.has_second_phase() && ordering.chi_before_c1() {
        transcript
            .challenge_qm31()
            .map_err(|_| VerifyError::ChallengeSampleExhausted)?;
        transcript
            .challenge_qm31()
            .map_err(|_| VerifyError::ChallengeSampleExhausted)?;
    }

    let mut roots = Vec::with_capacity(num_rounds as usize);
    let mut alphas = Vec::with_capacity(num_rounds as usize);
    let mut relation_weights = WeightAccumulator::empty(profile.log_rows);
    let mut relation_value = QM31::ZERO;
    let mut second_phase_root = None;
    let mut gamma = None;
    for layer in 0..num_rounds {
        let root = cursor.take_hash().ok_or(VerifyError::BadLength)?;
        transcript.absorb(label::ROOT, &root);
        roots.push(root);

        if layer == 0 && header.has_second_phase() {
            if !ordering.chi_before_c1() {
                // lambda and chi: both are verifier-derived only after C1.
                transcript
                    .challenge_qm31()
                    .map_err(|_| VerifyError::ChallengeSampleExhausted)?;
                transcript
                    .challenge_qm31()
                    .map_err(|_| VerifyError::ChallengeSampleExhausted)?;
            }

            let c2_root = cursor.take_hash().ok_or(VerifyError::BadLength)?;
            transcript.absorb(label::SECOND_PHASE_ROOT, &c2_root);
            second_phase_root = Some(c2_root);

            let early_gamma = if ordering.gamma_before_claims() {
                Some(
                    transcript
                        .challenge_qm31()
                        .map_err(|_| VerifyError::ChallengeSampleExhausted)?,
                )
            } else {
                None
            };

            let second_phase_claim = if let Some(main_claim) = claim {
                transcript.absorb(label::CLAIM, &main_claim.to_bytes());
                let bytes = cursor.take(OOD_VALUE_LEN).ok_or(VerifyError::BadLength)?;
                let value = QM31::from_le_bytes(bytes).ok_or(VerifyError::NonCanonicalValue)?;
                transcript.absorb(label::SECOND_PHASE_CLAIM, bytes);
                Some(value)
            } else {
                None
            };

            let sampled_gamma = match early_gamma {
                Some(value) => value,
                None => transcript
                    .challenge_qm31()
                    .map_err(|_| VerifyError::ChallengeSampleExhausted)?,
            };
            gamma = Some(sampled_gamma);

            if let (Some(main_claim), Some(helper_claim)) = (claim, second_phase_claim) {
                relation_weights = WeightAccumulator::from_claim(profile.log_rows, claim);
                relation_value = main_claim.v.add(sampled_gamma.mul(helper_claim));
            }
        }

        // Canonical schedule: beta -> y -> mu. The deliberately weakened
        // test-only policy inserts alpha after beta and before y; both paths
        // share the exact y/mu relation-and-weight kernel.
        let early_alpha = if ordering.ood_after_fold_challenge() {
            let point = sample_ood_point(&mut transcript)?;
            let alpha = transcript
                .challenge_qm31()
                .map_err(|_| VerifyError::ChallengeSampleExhausted)?;
            let bytes: &[u8; OOD_VALUE_LEN] = cursor
                .take(OOD_VALUE_LEN)
                .ok_or(VerifyError::BadLength)?
                .try_into()
                .map_err(|_| VerifyError::BadLength)?;
            absorb_ood_value_and_accumulate(
                &mut transcript,
                point,
                bytes,
                &mut relation_value,
                &mut relation_weights,
            )?;
            Some(alpha)
        } else {
            let bytes: &[u8; OOD_VALUE_LEN] = cursor
                .take(OOD_VALUE_LEN)
                .ok_or(VerifyError::BadLength)?
                .try_into()
                .map_err(|_| VerifyError::BadLength)?;
            accumulate_canonical_ood_sample(
                &mut transcript,
                bytes,
                &mut relation_value,
                &mut relation_weights,
            )?;
            None
        };
        // This marker now denotes the complete beta/y/mu relation sample.
        trace(trace_fn, TraceEvent::LayerOodDone(layer as u8));

        let sumcheck_bytes = cursor.take(SUMCHECK_BYTES).ok_or(VerifyError::BadLength)?;
        let mut sumcheck: SumcheckPolynomial = [QM31::ZERO; 7];
        for (index, chunk) in sumcheck_bytes.chunks_exact(16).enumerate() {
            sumcheck[index] = QM31::from_le_bytes(chunk).ok_or(VerifyError::NonCanonicalValue)?;
        }
        if sumcheck_boundary(&sumcheck) != relation_value {
            return Err(VerifyError::SumcheckBoundaryMismatch { layer: layer as u8 });
        }
        transcript.absorb(label::SUMCHECK_POLY, sumcheck_bytes);
        trace(trace_fn, TraceEvent::LayerSumcheckDone(layer as u8));

        let alpha = match early_alpha {
            Some(value) => value,
            None => transcript
                .challenge_qm31()
                .map_err(|_| VerifyError::ChallengeSampleExhausted)?,
        };
        relation_value = evaluate_sumcheck(&sumcheck, alpha);
        relation_weights.fold(alpha);
        alphas.push(alpha);
    }

    let final_poly_len = profile.final_poly_len() as usize;
    let final_poly_bytes = cursor
        .take(final_poly_len * 16)
        .ok_or(VerifyError::BadLength)?;
    transcript.absorb(label::FINAL_POLY, final_poly_bytes);
    let mut final_poly = Vec::with_capacity(final_poly_len);
    for chunk in final_poly_bytes.chunks_exact(16) {
        final_poly.push(QM31::from_le_bytes(chunk).ok_or(VerifyError::NonCanonicalValue)?);
    }
    if relation_weights.dot(&final_poly) != relation_value {
        return Err(VerifyError::EvaluationRelationMismatch);
    }

    let nonce = cursor.take_u64().ok_or(VerifyError::BadLength)?;
    if !transcript.grinding_ok(nonce, profile.grinding_bits) {
        return Err(VerifyError::GrindingFailed);
    }
    transcript.absorb(label::GRIND_NONCE, &nonce.to_le_bytes());
    trace(trace_fn, TraceEvent::TranscriptReady);

    let mut domain_table = DomainPowerTable::new(profile);
    let queries = transcript.challenge_queries(query_count, domain_table.geometry.fiber_count);
    trace(trace_fn, TraceEvent::QueriesReady);

    // ---- opening + fold phase ----
    // per-query running domain index i_r (i_0 = sampled fiber index)
    let mut index: Vec<u32> = queries.clone();
    // raw mode: expected incoming value per query; carried mode: deferred check3
    let mut expected: Vec<QM31> = vec![QM31::ZERO; query_count];
    let mut deferred: Vec<Option<CarriedDeferred>> = Vec::new();
    if fold_payload == FoldPayload::ProofCarriedRoundLocal {
        deferred = (0..query_count).map(|_| None).collect();
    }

    let mut fiber_index: Vec<u32> = Vec::with_capacity(query_count);
    let mut slot: Vec<u32> = Vec::with_capacity(query_count);
    let mut unique: Vec<u32> = Vec::with_capacity(query_count);
    let mut fibers: Vec<Fiber> = Vec::with_capacity(query_count);
    let mut helper_fibers: Vec<[QM31; 4]> = Vec::with_capacity(query_count);
    let mut carried: Vec<(QM31, QM31)> = Vec::with_capacity(query_count);
    let mut entries: Vec<(u32, [u8; 32])> = Vec::with_capacity(query_count);
    let mut merkle_level: Vec<(u32, [u8; 32])> = Vec::with_capacity(query_count);
    let mut merkle_next: Vec<(u32, [u8; 32])> = Vec::with_capacity(query_count);
    let mut s_values: Vec<CM31> = Vec::with_capacity(query_count);
    let mut folded: Vec<QM31> = Vec::with_capacity(query_count);
    let mut denoms: Vec<CM31> = Vec::with_capacity(query_count * 3);
    let mut invs: Vec<CM31> = Vec::with_capacity(query_count * 3);

    for layer in 0..num_rounds {
        trace(trace_fn, TraceEvent::LayerStart(layer as u8));
        let geom = domain_table.geometry;
        let alpha = alphas[layer as usize];
        let alpha2 = alpha.square();
        let fiber_mask = geom.fiber_count - 1;

        // geometry per query
        fiber_index.clear();
        slot.clear();
        for i in &index {
            fiber_index.push(*i & fiber_mask);
            slot.push(*i >> geom.log_fiber_count);
        }
        unique.clear();
        unique.extend_from_slice(&fiber_index);
        unique.sort_unstable();
        unique.dedup();

        let unique_count = cursor.take_u16().ok_or(VerifyError::BadLength)? as usize;
        if unique_count != unique.len() {
            return Err(VerifyError::UniqueCountMismatch { layer: layer as u8 });
        }
        let value_bytes = fiber_value_bytes(layer);
        let values_section = cursor
            .take(unique_count * value_bytes)
            .ok_or(VerifyError::BadLength)?;
        fibers.clear();
        for k in 0..unique_count {
            fibers.push(parse_fiber(
                &values_section[k * value_bytes..(k + 1) * value_bytes],
                layer,
            )?);
        }

        // C2 is opened only in the first layer. Authenticate its QM31
        // fibers separately, then form exactly the gamma-RLC polynomial that
        // the transcript relation and all later folds refer to.
        let second_phase_values_section = if layer == 0 && header.has_second_phase() {
            let helper_value_bytes = 4 * 16;
            let section = cursor
                .take(unique_count * helper_value_bytes)
                .ok_or(VerifyError::BadLength)?;
            helper_fibers.clear();
            for index in 0..unique_count {
                helper_fibers.push(parse_extension_fiber(
                    &section[index * helper_value_bytes..(index + 1) * helper_value_bytes],
                )?);
            }
            let gamma = gamma.ok_or(VerifyError::BadHeader)?;
            for index in 0..unique_count {
                fibers[index] =
                    combine_first_phase_fibers(&fibers[index], helper_fibers[index], gamma)?;
            }
            Some(section)
        } else {
            None
        };

        carried.clear();
        if fold_payload == FoldPayload::ProofCarriedRoundLocal {
            let carried_section = cursor
                .take(unique_count * 32)
                .ok_or(VerifyError::BadLength)?;
            for chunk in carried_section.chunks_exact(32) {
                let g1 =
                    QM31::from_le_bytes(&chunk[0..16]).ok_or(VerifyError::NonCanonicalValue)?;
                let g2 =
                    QM31::from_le_bytes(&chunk[16..32]).ok_or(VerifyError::NonCanonicalValue)?;
                carried.push((g1, g2));
            }
        }

        // Merkle verification over the unique C1 fiber leaves.
        let root = &roots[layer as usize];
        let depth = geom.log_fiber_count;
        verify_merkle_section(
            &mut cursor,
            hash,
            merkle_mode,
            root,
            depth,
            &unique,
            values_section,
            value_bytes,
            layer as u8,
            layer as u8,
            &mut entries,
            &mut merkle_level,
            &mut merkle_next,
        )?;

        if let Some(section) = second_phase_values_section {
            let c2_root = second_phase_root.as_ref().ok_or(VerifyError::BadHeader)?;
            verify_merkle_section(
                &mut cursor,
                hash,
                merkle_mode,
                c2_root,
                depth,
                &unique,
                section,
                4 * 16,
                SECOND_PHASE_LAYER_TAG,
                SECOND_PHASE_LAYER_TAG,
                &mut entries,
                &mut merkle_level,
                &mut merkle_next,
            )?;
        }
        trace(trace_fn, TraceEvent::LayerMerkleDone(layer as u8));

        // Slot consistency for the incoming value (layers >= 1).
        for q in 0..query_count {
            let k = unique.binary_search(&fiber_index[q]).unwrap();
            if layer > 0 {
                let opened = fibers[k].get(slot[q]);
                match fold_payload {
                    FoldPayload::RawFibers => {
                        if opened != expected[q] {
                            return Err(VerifyError::SlotMismatch { layer: layer as u8 });
                        }
                    }
                    FoldPayload::ProofCarriedRoundLocal => {
                        let d = deferred[q].as_ref().unwrap();
                        if opened.mul_cm31(d.two_s2) != d.rhs {
                            return Err(VerifyError::CarriedFoldMismatch {
                                layer: layer as u8 - 1,
                            });
                        }
                    }
                }
            }
        }

        // Fold each unique fiber once (round_batch_inversion in raw mode).
        s_values.clear();
        for &fidx in &unique {
            s_values.push(domain_table.point(fidx));
        }
        folded.clear();
        folded.resize(unique.len(), QM31::ZERO);
        match fold_payload {
            FoldPayload::RawFibers => {
                invs.clear();
                match denominator_backend {
                    DenominatorBackend::CircleConjugate => {
                        // Every s is derived from the unit circle, hence
                        // s^-1 = conjugate(s). The constant iota is -i, so
                        // iota^-1 = i and inv(2*iota*s) is just a swap/negate
                        // of inv(2s). No batch inversion or denominator
                        // materialization is needed.
                        for &s in &s_values {
                            let inv_s = s.conjugate();
                            let inv_2s = inv_s.half();
                            invs.push(inv_2s);
                            invs.push(inv_2s.mul_i());
                            invs.push(inv_s.square().half());
                        }
                    }
                    DenominatorBackend::BatchInverse(inverse) => {
                        denoms.clear();
                        for &s in &s_values {
                            denoms.push(s.double());
                            denoms.push(s.mul(geom.iota).double());
                            denoms.push(s.square().double());
                        }
                        invs.resize(denoms.len(), CM31::ZERO);
                        cm31_batch_inverse_with(&denoms, &mut invs, inverse);
                    }
                }
                for (k, fiber) in fibers.iter().enumerate() {
                    folded[k] = fold_fiber(
                        fiber,
                        alpha,
                        alpha2,
                        invs[k * 3],
                        invs[k * 3 + 1],
                        invs[k * 3 + 2],
                    );
                }
            }
            FoldPayload::ProofCarriedRoundLocal => {
                for (k, fiber) in fibers.iter().enumerate() {
                    let (g1, g2) = carried[k];
                    let (ok, d) =
                        carried_checks(fiber, g1, g2, alpha, alpha2, s_values[k], geom.iota);
                    if !ok {
                        return Err(VerifyError::CarriedFoldMismatch { layer: layer as u8 });
                    }
                    // store per-fiber deferred into every query hitting it
                    for q in 0..query_count {
                        if fiber_index[q] == unique[k] {
                            deferred[q] = Some(CarriedDeferred {
                                two_s2: d.two_s2,
                                rhs: d.rhs,
                            });
                        }
                    }
                }
            }
        }
        if fold_payload == FoldPayload::RawFibers {
            for q in 0..query_count {
                let k = unique.binary_search(&fiber_index[q]).unwrap();
                expected[q] = folded[k];
            }
        }

        index[..query_count].copy_from_slice(&fiber_index[..query_count]);
        domain_table.fold_layer();
        trace(trace_fn, TraceEvent::LayerFoldDone(layer as u8));
    }

    // ---- final polynomial check ----
    trace(trace_fn, TraceEvent::FinalCheckStart);
    // After all arity-4 folds the q transcript queries land in a tiny final
    // domain (16 points for the frozen blowup-2 profiles). Cache each cubic
    // evaluation by index instead of repeating it for colliding queries.
    folded.clear();
    folded.resize(domain_table.geometry.domain_size as usize, QM31::ZERO);
    slot.clear();
    slot.resize(domain_table.geometry.domain_size as usize, 0);
    for q in 0..query_count {
        let final_index = index[q] as usize;
        if slot[final_index] == 0 {
            let x = domain_table.point(index[q]);
            // Horner over QM31 coefficients at a CM31 point (late lift).
            let mut acc = *final_poly.last().unwrap();
            for c in final_poly.iter().rev().skip(1) {
                acc = acc.mul_cm31(x).add(*c);
            }
            folded[final_index] = acc;
            slot[final_index] = 1;
        }
        let acc = folded[final_index];
        match fold_payload {
            FoldPayload::RawFibers => {
                if acc != expected[q] {
                    return Err(VerifyError::FinalPolyMismatch);
                }
            }
            FoldPayload::ProofCarriedRoundLocal => {
                let d = deferred[q].as_ref().unwrap();
                if acc.mul_cm31(d.two_s2) != d.rhs {
                    return Err(VerifyError::FinalPolyMismatch);
                }
            }
        }
    }

    if !cursor.is_empty() {
        return Err(VerifyError::TrailingBytes);
    }
    trace(trace_fn, TraceEvent::Done);
    Ok(())
}

#[cfg(test)]
mod probe_tests {
    use super::*;
    use core::sync::atomic::{AtomicUsize, Ordering};

    static HASH_CALLS: AtomicUsize = AtomicUsize::new(0);

    fn host_hash(inputs: &[&[u8]]) -> [u8; 32] {
        use sha2::{Digest, Sha256};
        let mut hasher = Sha256::new();
        for input in inputs {
            hasher.update(input);
        }
        hasher.finalize().into()
    }

    fn counting_host_hash(inputs: &[&[u8]]) -> [u8; 32] {
        HASH_CALLS.fetch_add(1, Ordering::SeqCst);
        host_hash(inputs)
    }

    fn encoded_probe_output(samples_per_round: u8) -> [u8; 16] {
        let value = ood_sample_relation_probe(host_hash, samples_per_round)
            .expect("fixed probe transcript must not exhaust");
        let mut encoded = [0u8; 16];
        value.write_le_bytes(&mut encoded);
        encoded
    }

    #[test]
    fn ood_sample_probe_sinks_are_pinned() {
        assert_eq!(
            encoded_probe_output(1),
            OOD_SAMPLE_PROBE_S1_EXPECTED,
            "s=1 OOD probe sink drifted; re-pin only for a deliberate probe-kernel change"
        );
        assert_eq!(
            encoded_probe_output(2),
            OOD_SAMPLE_PROBE_S2_EXPECTED,
            "s=2 OOD probe sink drifted; re-pin only for a deliberate probe-kernel change"
        );
    }

    #[test]
    fn preencoded_ood_probe_values_match_the_reference_formula() {
        for (index, expected) in OOD_PROBE_ENCODED_VALUES.iter().enumerate() {
            let mut actual = [0u8; OOD_VALUE_LEN];
            ood_probe_value(index as u32, 3).write_le_bytes(&mut actual);
            assert_eq!(&actual, expected);
        }
    }

    #[test]
    fn ood_sample_probe_rejects_non_protocol_counts() {
        assert_eq!(
            ood_sample_relation_probe(host_hash, 0),
            Err(VerifyError::BadHeader)
        );
        assert_eq!(
            ood_sample_relation_probe(host_hash, 3),
            Err(VerifyError::BadHeader)
        );
    }

    #[test]
    fn second_samples_add_exactly_twenty_no_retry_hash_calls() {
        HASH_CALLS.store(0, Ordering::SeqCst);
        ood_sample_relation_probe(counting_host_hash, 1).unwrap();
        let s1_calls = HASH_CALLS.load(Ordering::SeqCst);
        HASH_CALLS.store(0, Ordering::SeqCst);
        ood_sample_relation_probe(counting_host_hash, 2).unwrap();
        let s2_calls = HASH_CALLS.load(Ordering::SeqCst);
        assert_eq!(s2_calls - s1_calls, 20);
    }
}
