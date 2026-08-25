//! SHA-256 Fiat-Shamir transcript, byte-exact between host and SBF.
//!
//! The hash backend is injected as a plain function pointer so this crate
//! stays no_std and dependency-free: the host passes a sha2-backed function,
//! the SBF program passes `solana_program::hash::hashv`.
//!
//! Stage 1 Fiat-Shamir ordering (audited per design section 8.1): absorb C1,
//! sample lambda and chi, absorb C2, absorb claimed evaluations, sample
//! gamma, then run the per-round OOD/sumcheck/fold transcript. Absorb the
//! final polynomial and grinding witness before deriving query positions.

use crate::circle::{secure_ood_circle_point_from_parameter, SecureCirclePoint};
use crate::field::{M31, QM31};

/// Pinned expected digest of `transcript_kat` — computed once on the host
/// (sha2 backend) and asserted bit-identical on host (`transcript_kat_pinned`
/// test) and on SBF (`TranscriptKat` program instruction, syscall backend).
/// Never edit this constant except as part of a deliberate, named transcript
/// protocol change.
pub const TRANSCRIPT_KAT_EXPECTED: [u8; 32] = [
    0x26, 0xf0, 0x91, 0x71, 0xa5, 0x96, 0x80, 0xc0, 0x65, 0x27, 0x3a, 0xc5, 0x7b, 0x20, 0xbf, 0x91,
    0x8b, 0x69, 0xeb, 0xb4, 0x0e, 0x64, 0x5f, 0x2f, 0x67, 0xad, 0x63, 0xe6, 0x20, 0x65, 0xc5, 0x91,
];

/// Pinned v4/s=2 PCS-scaffold transcript schedule. This diagnostic covers
/// the two-sample PCS schedule plus one C2 root followed by two helper
/// evaluations before gamma; it is not the final payment-v4 pin.
/// It is deliberately separate from [`TRANSCRIPT_KAT_EXPECTED`]: v3 remains
/// supported, so no later schedule may launder a change through a silent
/// re-pin.
pub const TRANSCRIPT_KAT_V4_S2_PCS_SCAFFOLD_EXPECTED: [u8; 32] = [
    0x74, 0xb6, 0x5c, 0x82, 0x5a, 0x6f, 0xee, 0xc2, 0x85, 0x0b, 0x30, 0x56, 0xa1, 0x6c, 0xc2, 0xb6,
    0xd0, 0xf7, 0x31, 0x8e, 0x78, 0x6a, 0x44, 0xec, 0x16, 0x53, 0x04, 0x98, 0x0f, 0x8b, 0x5f, 0x07,
];

/// Pinned profile-15 payment transcript, including the round-specific batch
/// work record inserted immediately before gamma.  Wire tag 20 recomputes
/// this vector with the Solana SHA-256 syscall backend.
pub const TRANSCRIPT_KAT_FINAL_PAYMENT_V4_EXPECTED: [u8; 32] = [
    0x76, 0x0b, 0xff, 0x52, 0x4d, 0x28, 0x3a, 0xdf, 0x2a, 0xa1, 0xa9, 0xdb, 0x38, 0xf2, 0x13, 0x7d,
    0x38, 0xdb, 0xd4, 0x19, 0xdf, 0xdd, 0xd4, 0x36, 0xe1, 0x32, 0x25, 0x52, 0xed, 0x76, 0x15, 0xfc,
];

/// hashv-shaped backend: hash the concatenation of the input slices.
pub type HashFn = fn(&[&[u8]]) -> [u8; 32];

/// Pure grinding predicate over an already-computed digest.
///
/// The first eight digest bytes are interpreted in big-endian order. Zero
/// work accepts every digest; positive deployed difficulties accept exactly
/// the heads below `2^(64 - bits)`.
pub fn digest_has_leading_zero_bits(digest: [u8; 32], bits: u8) -> bool {
    if bits == 0 {
        return true;
    }
    let head = u64::from_be_bytes([
        digest[0], digest[1], digest[2], digest[3], digest[4], digest[5], digest[6], digest[7],
    ]);
    head < (1u64 << (64 - bits as u32))
}

pub mod label {
    pub const PROFILE: u8 = 1;
    pub const STATEMENT: u8 = 2;
    pub const ROOT: u8 = 3;
    pub const FINAL_POLY: u8 = 4;
    pub const GRIND_NONCE: u8 = 5;
    /// Externally supplied main-column (z, v) evaluation claim. In a
    /// claim-carrying proof it is absorbed after C2 and before gamma.
    pub const CLAIM: u8 = 6;
    /// Prover-supplied evaluation at the transcript-derived out-of-domain
    /// point for the current committed layer. It must precede that layer's
    /// fold challenge.
    pub const OOD_VALUE: u8 = 7;
    /// Degree-6 interleaved linear-relation sumcheck polynomial. It is
    /// absorbed before the fold challenge used to reduce that relation.
    pub const SUMCHECK_POLY: u8 = 8;
    /// Second-phase helper commitment, absorbed only after lambda and chi
    /// have been squeezed from a transcript already binding C1.
    pub const SECOND_PHASE_ROOT: u8 = 9;
    /// Proof-carried helper evaluation at the public claim point. It and the
    /// main claim are both absorbed before gamma.
    pub const SECOND_PHASE_CLAIM: u8 = 10;
    /// Fixed genuine-circle C1 basis discriminator.
    pub const M31_CIRCLE_BASIS: u8 = 11;
    /// Circle-layer root record. The salted v5 profile uses
    /// `layer_u8 || root32 || public_fs_salt32`.
    pub const M31_CIRCLE_ROUND_ROOT: u8 = 12;
    /// Dedicated combined C2 helper root. The salted v5 profile uses
    /// `root32 || public_fs_salt32`.
    pub const M31_CIRCLE_C2_ROOT: u8 = 13;
    /// External `z || xor11(z)` MLE points.
    pub const M31_CIRCLE_STATEMENT_POINTS: u8 = 14;
    /// Fixed point-major, column-major block of 102 statement values.
    pub const M31_CIRCLE_STATEMENT_EVALUATIONS: u8 = 15;
    /// `layer || sample || value` for the layer-zero circle OOD relation.
    pub const M31_CIRCLE_OOD_VALUE: u8 = 16;
    /// `layer || sample || value` for later line OOD relations.
    pub const M31_LINE_OOD_VALUE: u8 = 17;
    /// `layer || seven QM31 coefficients` for the candidate relation sumcheck.
    pub const M31_CIRCLE_RELATION_SUMCHECK: u8 = 18;
    /// Four natural-order terminal line-tensor coefficients.
    pub const M31_CIRCLE_FINAL_TENSOR_POLY: u8 = 19;
    /// `layer || nonce_le` work witness checked after the layer sumcheck and
    /// before sampling that layer's powers-generator fold challenge.
    pub const M31_CIRCLE_FOLD_POW_NONCE: u8 = 20;
    /// Version/count framing for the frozen 252-entry payment constraint
    /// registry, absorbed after C2 and before its batching challenge.
    pub const M31_PAYMENT_CONSTRAINT_REGISTRY: u8 = 21;
    /// The two public zero claims `sum(h1)=sum(h2)=0`.
    pub const M31_PAYMENT_HELPER_SUMS: u8 = 22;
    /// `round || c0 || c2 || ... || c10` for the ten-round payment
    /// zerocheck. Its ten challenges become the PCS MLE point `z`.
    pub const M31_PAYMENT_ZEROCHECK_SUMCHECK: u8 = 23;
    /// Initial degree-10 sumcheck mask claim. A dedicated hiding profile
    /// absorbs every mask-oracle root before this field, then samples the
    /// nonzero affine-combination challenge.
    pub const M31_PAYMENT_HIDING_MASK_CLAIM: u8 = 24;
    /// Fixed mask-oracle count/degree framing followed by the nonzero lane
    /// batching challenge kappa. Every mask root is absorbed before this.
    pub const M31_PAYMENT_HIDING_MASK_ORACLES: u8 = 25;
    /// Mask-column powers-generator challenge delta, sampled after the same
    /// roots and independently from kappa.
    pub const M31_PAYMENT_HIDING_MASK_DELTA: u8 = 26;
    /// Two-point `(delta aggregate, H_z aggregate)` claims, followed by tau
    /// and the outer gamma challenge for the single-codeword merge.
    pub const M31_PAYMENT_HIDING_MASK_AGGREGATES: u8 = 27;
    /// `nonce_le` work witness checked after every statement-evaluation row
    /// and before the powers-generator batching challenge gamma.  This work
    /// belongs to the batching BCS round; later fold/query nonces cannot be
    /// credited to it.
    pub const M31_PAYMENT_BATCH_POW_NONCE: u8 = 28;
    /// `round || c0 || ... || c27` for the production-neutral state-only
    /// degree-27 zerocheck scaffold.  This label is deliberately distinct
    /// from the frozen degree-10 payment transcript (label 23).
    pub const M31_STATE_ONLY_ZEROCHECK_SUMCHECK: u8 = 29;
    /// Public state-only hiding context, including the statement digest,
    /// fresh proof nonce, and both layout fingerprints. It is absorbed before
    /// either masked C1/C2 commitment; private mask entropy is never absorbed.
    pub const M31_STATE_ONLY_HIDING_PRECOMMIT: u8 = 30;
    /// Initial state-only mask claim and fixed degree framing. This is
    /// absorbed only after every masked commitment, then the nonzero affine
    /// combination challenge is sampled.
    pub const M31_STATE_ONLY_HIDING_MASK_CLAIM: u8 = 31;
    /// Frozen state-only lane/copy/layout registry, absorbed after C2 and
    /// before theta, the zerocheck equality point, and mu are sampled.
    pub const M31_STATE_ONLY_CONSTRAINT_REGISTRY: u8 = 32;
    /// The single public state-only copy-helper sum claim `sum(h1)=0`.
    pub const M31_STATE_ONLY_HELPER_SUM: u8 = 33;
    /// Profile-21 diagnostic: dedicated two-lane natural-line commitment to
    /// the pre-delta source words X and F. This root precedes every challenge
    /// used to form their target functionals or affine combination.
    pub const M31_STATE_ONLY_SWITCH_XF_ROOT: u8 = 34;
    /// Profile-21 diagnostic: the ordered pair `(tX, muF)` after the target
    /// covector is fixed and before the source-code powers work witness.
    pub const M31_STATE_ONLY_SWITCH_TARGETS: u8 = 35;
    /// Profile-21 diagnostic: dedicated source-code powers-generator work
    /// nonce, checked and absorbed before delta. Final-round work cannot be
    /// credited to this earlier BCS round.
    pub const M31_STATE_ONLY_SWITCH_SOURCE_POW_NONCE: u8 = 36;
    /// Profile-21 diagnostic: forced natural coefficients
    /// `U = F + delta X`, absorbed immediately after delta.
    pub const M31_STATE_ONLY_SWITCH_U: u8 = 37;
    /// Profile-21 diagnostic: translated root-one commitment, fixed before
    /// its two OOD samples and the final query work witness.
    pub const M31_STATE_ONLY_SWITCH_TRANSLATED_ROOT: u8 = 38;
    /// Profile-21 diagnostic: final positioned work witness before q16 is
    /// sampled without replacement.
    pub const M31_STATE_ONLY_SWITCH_FINAL_POW_NONCE: u8 = 39;
    /// Profile-21 direct-binding guard: sorted transcript-derived line
    /// positions and their authenticated translated-word values. A fresh
    /// batching scalar is sampled only after this record is fixed.
    pub const M31_STATE_ONLY_SWITCH_QUERY_VALUES: u8 = 40;
    /// `round || c0 || c1 || c2` for the eight-round degree-two batch
    /// evaluation sumcheck binding disclosed U coefficients to all q values.
    pub const M31_STATE_ONLY_SWITCH_BATCH_EVAL_SUMCHECK: u8 = 41;
    /// Profile-21 complete post-delta relation seam target tau, absorbed after
    /// disclosed U and before the translated W1 root. Literal q16 binding
    /// ties this claimed scalar to the authenticated W1/U difference word.
    pub const M31_STATE_ONLY_SWITCH_TAU: u8 = 42;
    /// Spend's three evaluations of the committed zero-factor D lane.
    /// They are logically absorbed beside the ordinary statement evaluations,
    /// before batch grinding and gamma, even though the append-only wire puts
    /// them in the profile extension.
    pub const M31_STATE_ONLY_ZERO_FACTOR_D_CLAIMS: u8 = 43;
    /// Domain-separate the selected post-final-nonce q18 candidate.  The
    /// canonical spend selector range is 0..3 (three candidates).
    pub const M31_STATE_ONLY_QUERY_CANDIDATE: u8 = 44;
    /// Additive fixed-log-10 PCS shape descriptor. Later proof families
    /// absorb exact widths, tags, rate, point count, and query count here
    /// before sampling their powers-generator challenge.
    pub const M31_CIRCLE_PCS_SHAPE: u8 = 45;
    /// Profile-24 PCS suffix magic, wire version, flags, and fixed front
    /// geometry. This precedes the generic shape so future suffix semantics
    /// cannot reuse the same Fiat-Shamir schedule.
    pub const M31_PROFILE24_PCS_SUFFIX_HEADER: u8 = 46;
    /// V6 program identity and frozen release binding. The profile record,
    /// program id and release id precede the live statement and proof-attempt
    /// identifier, so a proof cannot be replayed into another deployment.
    pub const V6_DEPLOYMENT_CONTEXT: u8 = 47;
    /// `round || c0 || c2 || ... || c27` for V6's compact semantic
    /// sumcheck. `c1` is reconstructed from the running boundary claim.
    pub const V6_COMPACT_SEMANTIC_ROUND: u8 = 48;
    /// Three point-major rows of all 29 committed V6 lanes.
    pub const V6_POINT_CLAIMS: u8 = 49;
    /// V6's post-gamma copy-inactive claim, fixed before `kappa`.
    pub const V6_INACTIVE_CLAIM: u8 = 50;
    /// One of the two layer-zero circle OOD values: `sample || value`.
    pub const V6_CIRCLE_OOD_VALUE: u8 = 51;
    /// `round || c0 || c1 || c2 || c3 || c5 || c6` for a V6 relation
    /// reduction. `c4` is reconstructed from `4*(c0+c4)=claim`.
    pub const V6_COMPACT_RELATION_ROUND: u8 = 52;
    /// The complete disclosed 256-element coefficient vector, encoded as
    /// canonical 16-byte QM31 values for transcript hashing.
    pub const V6_FINAL256: u8 = 53;
    /// V6 compact-query domain record `selector || counter`.
    pub const V6_QUERY_CANDIDATE: u8 = 54;
    /// Domain separator immediately after the accepted V6 q16 draw and
    /// before the random linear-combination challenge for the sixteen fold
    /// equalities.
    pub const V6_QUERY_BATCH_CHALLENGE: u8 = 55;
    /// Canonical QM31 encoding of the verifier-computed random combination of
    /// the sixteen authenticated folded query values.
    pub const V6_QUERY_BATCH_CLAIM: u8 = 56;
}

const DOM_ABSORB: u8 = 0x00;
const DOM_SQUEEZE: u8 = 0x01;
const DOM_ADVANCE: u8 = 0x02;
const DOM_GRIND: u8 = 0x03;

/// Maximum candidate draws per QM31 limb before the transcript is declared
/// exhausted. Per-limb exhaustion probability (2^-31)^8 = 2^-248.
pub const CHALLENGE_RETRY_LIMIT: u32 = 8;

/// Maximum exact-uniform QM31 draws used when a protocol challenge must be
/// nonzero. Exhaustion has probability `|QM31|^-3` apart from the separately
/// bounded per-limb rejection event.
pub const NONZERO_QM31_RETRY_LIMIT: u32 = 3;

/// Maximum field draws used to obtain a point outside the CM31 subfield.
/// A random QM31 point lands in CM31 with probability 1/|CM31| ~= 2^-62;
/// exhausting all three attempts is therefore below 2^-186.
pub const OOD_RETRY_LIMIT: u32 = 3;

/// Maximum exact-uniform parameters tried for one secure circle OOD point.
/// Rejections cover the rational map's two poles and the CM31 parameter
/// subfield. This sampler is for the layer-zero circle polynomial only;
/// later line layers continue to use [`Transcript::challenge_ood_qm31`].
pub const CIRCLE_POINT_RETRY_LIMIT: u32 = 3;

/// The bounded rejection-sampling loop ran out of retries (a 2^-248-per-limb
/// completeness event). The verifier maps this to proof rejection.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ChallengeSampleExhausted;

/// Failure of bounded exact-uniform query sampling without replacement.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum QuerySampleError {
    /// Masking is exact only when the domain size is a nonzero power of two.
    BoundNotPowerOfTwo { bound: u32 },
    /// A without-replacement sample cannot contain more points than its domain.
    CountExceedsBound { count: usize, bound: u32 },
    /// The configured candidate-draw cap was reached before `count` distinct
    /// positions were accepted. This is an explicit completeness abort.
    DrawLimitExhausted { accepted: usize, max_draws: usize },
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum OodSampleError {
    /// The exact-uniform field sampler exhausted its per-limb retry bound.
    ChallengeSampleExhausted,
    /// Three independently sampled QM31 points all landed in CM31.
    SubfieldSampleExhausted,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CirclePointSampleError {
    /// The exact-uniform QM31 parameter sampler exhausted its limb retry.
    ChallengeSampleExhausted,
    /// Every bounded parameter candidate was either in CM31 or a pole of the
    /// rational circle map.
    ParameterSampleExhausted,
}

#[derive(Clone)]
pub struct Transcript {
    state: [u8; 32],
    hash: HashFn,
}

impl Transcript {
    pub fn new(hash: HashFn) -> Transcript {
        Transcript {
            state: [0u8; 32],
            hash,
        }
    }

    #[inline(never)]
    pub fn absorb(&mut self, label: u8, data: &[u8]) {
        // Most transcript records are short. Packing their fixed state and
        // framing into one buffer reduces SBF slice translation while the
        // large point/final vectors retain the zero-copy hashv path.
        const PACKED_ABSORB_BYTES: usize = 192;
        if data.len() <= PACKED_ABSORB_BYTES - 34 {
            let mut input = [0u8; PACKED_ABSORB_BYTES];
            input[..32].copy_from_slice(&self.state);
            input[32] = DOM_ABSORB;
            input[33] = label;
            input[34..34 + data.len()].copy_from_slice(data);
            self.state = (self.hash)(&[&input[..34 + data.len()]]);
        } else {
            self.state = (self.hash)(&[&self.state, &[DOM_ABSORB, label], data]);
        }
    }

    /// Internal evidence hook for candidate schedule teeth. This is not a
    /// transcript challenge, wire field, or production KAT surface.
    pub const fn diagnostic_state(&self) -> [u8; 32] {
        self.state
    }

    /// Squeeze one 32-byte block and advance the state.
    #[inline(never)]
    pub fn squeeze_block(&mut self) -> [u8; 32] {
        let mut squeeze = [0u8; 33];
        squeeze[..32].copy_from_slice(&self.state);
        squeeze[32] = DOM_SQUEEZE;
        let out = (self.hash)(&[&squeeze]);
        squeeze[32] = DOM_ADVANCE;
        self.state = (self.hash)(&[&squeeze]);
        out
    }

    /// Sample a QM31 challenge by per-limb rejection sampling (exactly
    /// uniform; soundness-note §3 T9).
    ///
    /// Each limb draw takes 31 bits of a LE u32 and REJECTS the single
    /// non-canonical value P, redrawing from fresh transcript bytes: retries
    /// consume the next word of the block stream, and a spent block is
    /// replaced via `squeeze_block`, which advances the duplex state — no
    /// input is ever re-hashed, so retries cannot repeat a rejected value
    /// deterministically. The retry loop is bounded (`CHALLENGE_RETRY_LIMIT`)
    /// and exhaustion is an error the verifier surfaces as proof rejection:
    /// per-limb exhaustion probability is (2^-31)^8 = 2^-248, a completeness
    /// event (soundness-note §6), the correct trade on a CU-metered chain
    /// versus an unmetered loop.
    ///
    /// In the non-rejecting case (all real transcripts, whp) this consumes
    /// exactly one block and produces the same limbs as the pre-fix sampler
    /// except on a P-hit, where the old code folded P to 0 (the ~2^-31
    /// per-limb bias this fix removes).
    pub fn challenge_qm31(&mut self) -> Result<QM31, ChallengeSampleExhausted> {
        let mut limbs = [M31::ZERO; 4];
        let mut block = self.squeeze_block();
        let mut word_index = 0usize;
        for limb in limbs.iter_mut() {
            let mut accepted = false;
            for _ in 0..CHALLENGE_RETRY_LIMIT {
                if word_index == 8 {
                    block = self.squeeze_block();
                    word_index = 0;
                }
                let word = u32::from_le_bytes(
                    block[word_index * 4..word_index * 4 + 4]
                        .try_into()
                        .unwrap(),
                );
                word_index += 1;
                let masked = word & crate::field::P;
                if masked != crate::field::P {
                    *limb = M31(masked);
                    accepted = true;
                    break;
                }
            }
            if !accepted {
                return Err(ChallengeSampleExhausted);
            }
        }
        Ok(QM31 {
            c0: crate::field::CM31 {
                a: limbs[0],
                b: limbs[1],
            },
            c1: crate::field::CM31 {
                a: limbs[2],
                b: limbs[3],
            },
        })
    }

    /// Sample exactly uniformly from `QM31 ∖ {0}` with a bounded
    /// rejection loop. Every rejected zero consumes fresh transcript blocks;
    /// exhaustion is a completeness rejection, never a zero fallback.
    pub fn challenge_nonzero_qm31(&mut self) -> Result<QM31, ChallengeSampleExhausted> {
        for _ in 0..NONZERO_QM31_RETRY_LIMIT {
            let value = self.challenge_qm31()?;
            if value != QM31::ZERO {
                return Ok(value);
            }
        }
        Err(ChallengeSampleExhausted)
    }

    /// Sample exactly uniformly from QM31 \ CM31. Since every evaluation
    /// domain used by Aspis lies in CM31, this makes the point genuinely
    /// out-of-domain by construction instead of relying on a negligible
    /// collision probability. The bounded outer retry is a completeness
    /// trade (below 2^-186), not a soundness term.
    pub fn challenge_ood_qm31(&mut self) -> Result<QM31, OodSampleError> {
        for _ in 0..OOD_RETRY_LIMIT {
            let point = self
                .challenge_qm31()
                .map_err(|_| OodSampleError::ChallengeSampleExhausted)?;
            if point.c1 != crate::field::CM31::ZERO {
                return Ok(point);
            }
        }
        Err(OodSampleError::SubfieldSampleExhausted)
    }

    /// Sample a secure layer-zero circle OOD point through an exact-uniform
    /// QM31 parameter `t` and the rational map. The bounded policy rejects
    /// `t in CM31` and `1+t^2=0`; the pure map reports those reasons in
    /// [`crate::circle::CirclePointError`], while this transcript API exposes
    /// one bounded-candidate exhaustion result. No inversion path panics.
    pub fn challenge_secure_circle_point(
        &mut self,
    ) -> Result<SecureCirclePoint, CirclePointSampleError> {
        for _ in 0..CIRCLE_POINT_RETRY_LIMIT {
            let parameter = self
                .challenge_qm31()
                .map_err(|_| CirclePointSampleError::ChallengeSampleExhausted)?;
            if let Ok(point) = secure_ood_circle_point_from_parameter(parameter) {
                return Ok(point);
            }
        }
        Err(CirclePointSampleError::ParameterSampleExhausted)
    }

    /// Derive `count` query positions in [0, bound) where bound is a power of
    /// two (exact-uniform masking, no modulo bias).
    pub fn challenge_queries(&mut self, count: usize, bound: u32) -> alloc::vec::Vec<u32> {
        debug_assert!(bound.is_power_of_two());
        let mask = bound - 1;
        let mut out = alloc::vec::Vec::with_capacity(count);
        'outer: loop {
            let block = self.squeeze_block();
            for word in block.chunks_exact(4) {
                if out.len() == count {
                    break 'outer;
                }
                let word = u32::from_le_bytes(word.try_into().unwrap());
                out.push(word & mask);
            }
            if out.len() == count {
                break;
            }
        }
        out
    }

    /// Derive an ordered exact-uniform sample without replacement from
    /// `[0, bound)`, where `bound` is a power of two.
    ///
    /// Candidate words use the same mask and block stream as
    /// [`Self::challenge_queries`]. Duplicate candidates are rejected while
    /// preserving the order of first occurrence. Consequently, whenever the
    /// first `count` candidates are already distinct, this method returns the
    /// same query bytes and leaves the transcript in exactly the same state as
    /// the legacy with-replacement method. The bounded draw cap turns an
    /// exceptionally collision-heavy transcript into an explicit proof
    /// rejection instead of an unmetered loop.
    pub fn challenge_queries_without_replacement(
        &mut self,
        count: usize,
        bound: u32,
        max_draws: usize,
    ) -> Result<alloc::vec::Vec<u32>, QuerySampleError> {
        if !bound.is_power_of_two() {
            return Err(QuerySampleError::BoundNotPowerOfTwo { bound });
        }
        if count > bound as usize {
            return Err(QuerySampleError::CountExceedsBound { count, bound });
        }
        if count == 0 {
            return Ok(alloc::vec::Vec::new());
        }
        let mask = bound - 1;
        let mut out = alloc::vec::Vec::with_capacity(count);
        let mut draws = 0usize;
        'outer: while draws < max_draws {
            let block = self.squeeze_block();
            for word in block.chunks_exact(4) {
                if out.len() == count || draws == max_draws {
                    break 'outer;
                }
                draws += 1;
                let candidate = u32::from_le_bytes(word.try_into().unwrap()) & mask;
                if !out.contains(&candidate) {
                    out.push(candidate);
                }
            }
        }
        if out.len() == count {
            Ok(out)
        } else {
            Err(QuerySampleError::DrawLimitExhausted {
                accepted: out.len(),
                max_draws,
            })
        }
    }

    /// Grinding check: hash(state, DOM_GRIND, nonce) must have
    /// `bits` leading zero bits. Verifier-side cost: one hash call.
    pub fn grinding_ok(&self, nonce: u64, bits: u8) -> bool {
        let digest = (self.hash)(&[&self.state, &[DOM_GRIND], &nonce.to_le_bytes()]);
        digest_has_leading_zero_bits(digest, bits)
    }
}

/// Known-answer transcript vector (soundness-note appendix): absorb a fixed
/// pattern, sample the full challenge menu (QM31 rejection sampler, grinding
/// check, query derivation), and fold every output into one digest. The
/// pinned expected value lives in the host test `transcript_kat_pinned` and
/// is asserted bit-identical on SBF via the program's `TranscriptKat`
/// instruction — a silent host/chain sampler divergence costs a test
/// failure here instead of a week.
pub fn transcript_kat(hash: HashFn) -> [u8; 32] {
    let mut t = Transcript::new(hash);
    t.absorb(label::PROFILE, b"aspis-transcript-kat-v3-c2");
    t.absorb(label::STATEMENT, &[0xA5; 32]);
    let mut acc = [0u8; 32];

    // Canonical two-phase prefix: C1 -> (lambda, chi) -> C2 -> claimed
    // evaluations -> gamma. Each squeezed value contributes to the KAT
    // digest, so deleting or moving any one of them is a loud re-pin.
    t.absorb(label::ROOT, &[0u8; 32]);
    for _ in 0..2 {
        let challenge = t
            .challenge_qm31()
            .expect("kat: phase challenge sampler exhausted (2^-248 per limb)");
        let mut bytes = [0u8; 16];
        challenge.write_le_bytes(&mut bytes);
        acc = hash(&[&acc, &bytes]);
    }
    t.absorb(label::SECOND_PHASE_ROOT, &[0x22; 32]);
    t.absorb(label::CLAIM, &[0x33; 176]);
    t.absorb(label::SECOND_PHASE_CLAIM, &[0x44; 16]);
    let gamma = t
        .challenge_qm31()
        .expect("kat: gamma sampler exhausted (2^-248 per limb)");
    let mut gamma_bytes = [0u8; 16];
    gamma.write_le_bytes(&mut gamma_bytes);
    acc = hash(&[&acc, &gamma_bytes]);

    for i in 0..8u8 {
        if i > 0 {
            t.absorb(label::ROOT, &[i; 32]);
        }
        let ood_point = t
            .challenge_ood_qm31()
            .expect("kat: OOD sampler exhausted (<2^-186)");
        let mut point_bytes = [0u8; 16];
        ood_point.write_le_bytes(&mut point_bytes);
        acc = hash(&[&acc, &point_bytes]);
        t.absorb(label::OOD_VALUE, &[0x40 + i; 16]);
        let mix = t
            .challenge_qm31()
            .expect("kat: claim-mix sampler exhausted (2^-248 per limb)");
        let mut mix_bytes = [0u8; 16];
        mix.write_le_bytes(&mut mix_bytes);
        acc = hash(&[&acc, &mix_bytes]);
        t.absorb(
            label::SUMCHECK_POLY,
            &[0x80 + i; crate::sumcheck::SUMCHECK_BYTES],
        );
        let alpha = t
            .challenge_qm31()
            .expect("kat: sampler exhausted (2^-248 per limb)");
        let mut bytes = [0u8; 16];
        alpha.write_le_bytes(&mut bytes);
        acc = hash(&[&acc, &bytes]);
    }
    t.absorb(label::FINAL_POLY, &[0x77; 64]);
    let grind = t.grinding_ok(0xDEAD_BEEF, 8);
    acc = hash(&[&acc, &[grind as u8]]);
    t.absorb(label::GRIND_NONCE, &0xDEAD_BEEFu64.to_le_bytes());
    for q in t.challenge_queries(16, 1 << 10) {
        acc = hash(&[&acc, &q.to_le_bytes()]);
    }
    acc
}

/// V4/s=2 PCS-scaffold known-answer transcript vector.
///
/// V4 extends the v3 two-phase prefix by absorbing a second helper evaluation
/// under the same combined C2 root before gamma. Each committed layer then
/// carries two sequential `(beta, y, mu)` triples before the single relation
/// sumcheck polynomial and fold challenge. Keeping this function distinct
/// makes both supported schedules independently auditable.
pub fn transcript_kat_v4_s2_pcs_scaffold(hash: HashFn) -> [u8; 32] {
    let mut t = Transcript::new(hash);
    t.absorb(label::PROFILE, b"aspis-transcript-kat-v4-s2-c2");
    t.absorb(label::STATEMENT, &[0xA5; 32]);
    let mut acc = [0u8; 32];

    t.absorb(label::ROOT, &[0u8; 32]);
    for _ in 0..2 {
        let challenge = t
            .challenge_qm31()
            .expect("v4 kat: phase challenge sampler exhausted (2^-248 per limb)");
        let mut bytes = [0u8; 16];
        challenge.write_le_bytes(&mut bytes);
        acc = hash(&[&acc, &bytes]);
    }
    t.absorb(label::SECOND_PHASE_ROOT, &[0x22; 32]);
    t.absorb(label::CLAIM, &[0x33; 176]);
    t.absorb(label::SECOND_PHASE_CLAIM, &[0x44; 16]);
    t.absorb(label::SECOND_PHASE_CLAIM, &[0x45; 16]);
    let gamma = t
        .challenge_qm31()
        .expect("v4 kat: gamma sampler exhausted (2^-248 per limb)");
    let mut gamma_bytes = [0u8; 16];
    gamma.write_le_bytes(&mut gamma_bytes);
    acc = hash(&[&acc, &gamma_bytes]);

    for layer in 0..8u8 {
        if layer > 0 {
            t.absorb(label::ROOT, &[layer; 32]);
        }
        for sample in 0..2u8 {
            let ood_point = t
                .challenge_ood_qm31()
                .expect("v4 kat: OOD sampler exhausted (<2^-186)");
            let mut point_bytes = [0u8; 16];
            ood_point.write_le_bytes(&mut point_bytes);
            acc = hash(&[&acc, &point_bytes]);

            t.absorb(label::OOD_VALUE, &[0x40 + 2 * layer + sample; 16]);
            let mix = t
                .challenge_qm31()
                .expect("v4 kat: claim-mix sampler exhausted (2^-248 per limb)");
            let mut mix_bytes = [0u8; 16];
            mix.write_le_bytes(&mut mix_bytes);
            acc = hash(&[&acc, &mix_bytes]);
        }
        t.absorb(
            label::SUMCHECK_POLY,
            &[0x80 + layer; crate::sumcheck::SUMCHECK_BYTES],
        );
        let alpha = t
            .challenge_qm31()
            .expect("v4 kat: sampler exhausted (2^-248 per limb)");
        let mut alpha_bytes = [0u8; 16];
        alpha.write_le_bytes(&mut alpha_bytes);
        acc = hash(&[&acc, &alpha_bytes]);
    }

    t.absorb(label::FINAL_POLY, &[0x77; 64]);
    let grind = t.grinding_ok(0xDEAD_BEEF, 8);
    acc = hash(&[&acc, &[grind as u8]]);
    t.absorb(label::GRIND_NONCE, &0xDEAD_BEEFu64.to_le_bytes());
    for query in t.challenge_queries(16, 1 << 10) {
        acc = hash(&[&acc, &query.to_le_bytes()]);
    }
    acc
}

/// Full payment-v4 schedule KAT.
///
/// The byte payloads are deterministic fixtures, while every challenge and
/// query uses the production sampler.  The KAT's purpose is schedule and
/// host/SBF parity: it pins C1 -> lambda/chi -> C2 -> payment zerocheck -> all
/// statement rows -> batch work -> gamma, followed by the exact two-OOD,
/// per-fold-work, final-work, distinct-query tail.
pub fn transcript_kat_final_payment_v4(hash: HashFn) -> [u8; 32] {
    fn fold_value(hash: HashFn, acc: &mut [u8; 32], value: QM31) {
        let mut bytes = [0u8; 16];
        value.write_le_bytes(&mut bytes);
        *acc = hash(&[acc, &bytes]);
    }

    let mut t = Transcript::new(hash);
    let mut acc = [0u8; 32];

    t.absorb(label::PROFILE, b"aspis-payment-v4-kat");
    t.absorb(label::M31_CIRCLE_BASIS, b"aspis:c1:m31-circle:v0");
    t.absorb(label::STATEMENT, &[0xa5; 32]);
    let mut root_record = [0x11u8; 33];
    root_record[0] = 0;
    t.absorb(label::M31_CIRCLE_ROUND_ROOT, &root_record);
    for _ in 0..2 {
        fold_value(
            hash,
            &mut acc,
            t.challenge_qm31().expect("payment KAT phase sampler"),
        );
    }
    t.absorb(label::M31_CIRCLE_C2_ROOT, &[0x22; 32]);

    let registry = [2u8, 252, 0, 67, 0, 10, 10, 10];
    t.absorb(label::M31_PAYMENT_CONSTRAINT_REGISTRY, &registry);
    t.absorb(label::M31_PAYMENT_HELPER_SUMS, &[0u8; 32]);
    fold_value(
        hash,
        &mut acc,
        t.challenge_qm31().expect("payment KAT theta sampler"),
    );
    for _ in 0..10 {
        fold_value(
            hash,
            &mut acc,
            t.challenge_qm31().expect("payment KAT zero-point sampler"),
        );
    }
    fold_value(
        hash,
        &mut acc,
        t.challenge_qm31().expect("payment KAT mu sampler"),
    );

    t.absorb(label::M31_PAYMENT_HIDING_MASK_CLAIM, &[0x31; 16]);
    fold_value(
        hash,
        &mut acc,
        t.challenge_qm31().expect("payment KAT eta sampler"),
    );
    let mut z = [QM31::ZERO; 10];
    for round in 0..10usize {
        let mut record = [0u8; 161];
        record[0] = round as u8;
        record[1..].fill(0x40 + round as u8);
        t.absorb(label::M31_PAYMENT_ZEROCHECK_SUMCHECK, &record);
        z[round] = t.challenge_qm31().expect("payment KAT sumcheck sampler");
        fold_value(hash, &mut acc, z[round]);
    }

    let mut points = [0u8; 320];
    for (point, mut coordinates) in [z, z].into_iter().enumerate() {
        if point == 1 {
            for coordinate in [6usize, 8, 9] {
                coordinates[coordinate] = QM31::ONE.sub(coordinates[coordinate]);
            }
        }
        for (coordinate, value) in coordinates.into_iter().enumerate() {
            value.write_le_bytes(&mut points[(point * 10 + coordinate) * 16..][..16]);
        }
    }
    t.absorb(label::M31_CIRCLE_STATEMENT_POINTS, &points);
    t.absorb(label::M31_CIRCLE_STATEMENT_EVALUATIONS, &[0x52; 1_632]);

    let batch_nonce = 0x6261_7463_685f_706fu64;
    let batch_ok = t.grinding_ok(batch_nonce, 8);
    acc = hash(&[&acc, &[batch_ok as u8]]);
    t.absorb(
        label::M31_PAYMENT_BATCH_POW_NONCE,
        &batch_nonce.to_le_bytes(),
    );
    fold_value(
        hash,
        &mut acc,
        t.challenge_qm31().expect("payment KAT gamma sampler"),
    );
    fold_value(
        hash,
        &mut acc,
        t.challenge_qm31().expect("payment KAT point-scale sampler"),
    );

    for layer in 0..4usize {
        if layer > 0 {
            let mut record = [0x60 + layer as u8; 33];
            record[0] = layer as u8;
            t.absorb(label::M31_CIRCLE_ROUND_ROOT, &record);
        }
        for sample in 0..2usize {
            if layer == 0 {
                let point = t
                    .challenge_secure_circle_point()
                    .expect("payment KAT circle sampler");
                fold_value(hash, &mut acc, point.x);
                fold_value(hash, &mut acc, point.y);
            } else {
                fold_value(
                    hash,
                    &mut acc,
                    t.challenge_ood_qm31().expect("payment KAT line sampler"),
                );
            }
            let mut record = [0x70 + (2 * layer + sample) as u8; 18];
            record[0] = layer as u8;
            record[1] = sample as u8;
            t.absorb(
                if layer == 0 {
                    label::M31_CIRCLE_OOD_VALUE
                } else {
                    label::M31_LINE_OOD_VALUE
                },
                &record,
            );
            fold_value(
                hash,
                &mut acc,
                t.challenge_qm31().expect("payment KAT OOD mix sampler"),
            );
        }
        let mut sumcheck = [0x80 + layer as u8; 113];
        sumcheck[0] = layer as u8;
        t.absorb(label::M31_CIRCLE_RELATION_SUMCHECK, &sumcheck);
        let fold_nonce = 0x666f_6c64_0000_0000u64 | layer as u64;
        let fold_ok = t.grinding_ok(fold_nonce, 8);
        acc = hash(&[&acc, &[fold_ok as u8]]);
        let mut record = [0u8; 9];
        record[0] = layer as u8;
        record[1..].copy_from_slice(&fold_nonce.to_le_bytes());
        t.absorb(label::M31_CIRCLE_FOLD_POW_NONCE, &record);
        fold_value(
            hash,
            &mut acc,
            t.challenge_qm31().expect("payment KAT fold sampler"),
        );
    }

    t.absorb(label::M31_CIRCLE_FINAL_TENSOR_POLY, &[0x91; 64]);
    let final_nonce = 0x7175_6572_795f_706fu64;
    let final_ok = t.grinding_ok(final_nonce, 8);
    acc = hash(&[&acc, &[final_ok as u8]]);
    t.absorb(label::GRIND_NONCE, &final_nonce.to_le_bytes());
    for query in t
        .challenge_queries_without_replacement(36, 1 << 12, 64)
        .expect("payment KAT distinct-query sampler")
    {
        acc = hash(&[&acc, &query.to_le_bytes()]);
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{CM31, P};

    const CIRCLE_S2_FIXTURE_EXPECTED: [u8; 32] = [
        8, 72, 150, 167, 42, 224, 50, 159, 107, 60, 253, 10, 218, 217, 96, 40, 11, 204, 190, 117,
        157, 189, 68, 117, 30, 223, 188, 172, 120, 178, 4, 85,
    ];

    fn test_hash(inputs: &[&[u8]]) -> [u8; 32] {
        use sha2::{Digest, Sha256};
        let mut h = Sha256::new();
        for i in inputs {
            h.update(i);
        }
        h.finalize().into()
    }

    /// Return the transcript state from either the original two-slice hashv
    /// spelling or the allocation-free packed spelling used by production.
    /// Test-only adversarial backends model the concatenated hash input, so
    /// they must not depend on how that byte string is split into slices.
    fn framed_state<'a>(inputs: &'a [&'a [u8]], domain: u8) -> Option<&'a [u8]> {
        match inputs {
            [state, frame] if state.len() == 32 && *frame == [domain] => Some(*state),
            [packed] if packed.len() == 33 && packed[32] == domain => Some(&packed[..32]),
            _ => None,
        }
    }

    fn grinding_input_probe(inputs: &[&[u8]]) -> [u8; 32] {
        assert_eq!(inputs.len(), 3);
        assert_eq!(inputs[0], &[0u8; 32]);
        assert_eq!(inputs[1], &[DOM_GRIND]);
        assert_eq!(inputs[2], &0x0102_0304_0506_0708u64.to_le_bytes());
        let mut digest = [0u8; 32];
        digest[..8].copy_from_slice(&(u32::MAX as u64).to_be_bytes());
        digest
    }

    #[test]
    fn grinding_digest_predicate_has_exact_boundaries_and_byte_order() {
        for bits in [37u8, 34, 33, 30, 25, 32] {
            let threshold = 1u64 << (64 - bits as u32);
            let mut below = [0u8; 32];
            below[..8].copy_from_slice(&(threshold - 1).to_be_bytes());
            let mut at = [0u8; 32];
            at[..8].copy_from_slice(&threshold.to_be_bytes());
            assert!(digest_has_leading_zero_bits(below, bits));
            assert!(!digest_has_leading_zero_bits(at, bits));
        }

        assert!(digest_has_leading_zero_bits([0xff; 32], 0));

        let mut canonical = [0u8; 32];
        canonical[..8].copy_from_slice(&(u32::MAX as u64).to_be_bytes());
        let mut byte_reversed = canonical;
        byte_reversed[..8].reverse();
        assert!(digest_has_leading_zero_bits(canonical, 32));
        assert!(!digest_has_leading_zero_bits(byte_reversed, 32));
    }

    #[test]
    fn grinding_ok_hashes_exact_state_domain_and_little_endian_nonce_chunks() {
        let transcript = Transcript::new(grinding_input_probe);
        assert!(transcript.grinding_ok(0x0102_0304_0506_0708, 32));
    }

    #[test]
    fn transcript_kat_pinned() {
        let digest = transcript_kat(test_hash);
        let mut hex = alloc::string::String::new();
        for b in digest {
            use core::fmt::Write;
            let _ = write!(hex, "{b:02x}");
        }
        assert_eq!(
            digest, TRANSCRIPT_KAT_EXPECTED,
            "transcript KAT drifted; computed {hex} — a deliberate protocol \
             change must re-pin TRANSCRIPT_KAT_EXPECTED and say so in the log"
        );
    }

    #[test]
    fn transcript_kat_v4_s2_pcs_scaffold_pinned() {
        let digest = transcript_kat_v4_s2_pcs_scaffold(test_hash);
        let mut hex = alloc::string::String::new();
        for byte in digest {
            use core::fmt::Write;
            let _ = write!(hex, "{byte:02x}");
        }
        assert_eq!(
            digest, TRANSCRIPT_KAT_V4_S2_PCS_SCAFFOLD_EXPECTED,
            "v4/s2 two-helper PCS-scaffold transcript KAT drifted; computed {hex} — update this diagnostic pin and its ledger entry only as one named protocol change"
        );
    }

    #[test]
    fn transcript_kat_final_payment_v4_pinned() {
        let digest = transcript_kat_final_payment_v4(test_hash);
        let mut hex = alloc::string::String::new();
        for byte in digest {
            use core::fmt::Write;
            let _ = write!(hex, "{byte:02x}");
        }
        assert_eq!(
            digest, TRANSCRIPT_KAT_FINAL_PAYMENT_V4_EXPECTED,
            "final payment-v4 transcript KAT drifted; computed {hex}"
        );
    }

    /// Adversarial backend: every squeezed word masks to P, so every draw is
    /// rejected and the bounded loop must exhaust with an error, not spin.
    fn all_p_hash(_inputs: &[&[u8]]) -> [u8; 32] {
        [0xFF; 32]
    }

    #[test]
    fn sampler_exhaustion_is_bounded_error() {
        let mut t = Transcript::new(all_p_hash);
        assert_eq!(t.challenge_qm31(), Err(ChallengeSampleExhausted));
    }

    #[test]
    fn ordered_queries_without_replacement_are_unique_bounded_and_deterministic() {
        let mut first = Transcript::new(test_hash);
        first.absorb(label::PROFILE, b"ordered-query-sampler-v1");
        let mut second = first.clone();
        let first_queries = first
            .challenge_queries_without_replacement(36, 1 << 12, 64)
            .unwrap();
        let second_queries = second
            .challenge_queries_without_replacement(36, 1 << 12, 64)
            .unwrap();
        assert_eq!(first_queries, second_queries);
        assert_eq!(first.diagnostic_state(), second.diagnostic_state());
        assert_eq!(first_queries.len(), 36);
        assert!(first_queries.iter().all(|query| *query < 1 << 12));
        for (index, query) in first_queries.iter().enumerate() {
            assert!(!first_queries[..index].contains(query));
        }
    }

    #[test]
    fn no_collision_without_replacement_sampling_is_legacy_byte_and_state_identical() {
        let mut legacy = Transcript::new(test_hash);
        legacy.absorb(label::PROFILE, b"query-sampler-no-collision-kat-v1");
        let mut distinct = legacy.clone();
        let legacy_queries = legacy.challenge_queries(36, 1 << 12);
        for (index, query) in legacy_queries.iter().enumerate() {
            assert!(
                !legacy_queries[..index].contains(query),
                "fixture unexpectedly contains a collision at {index}"
            );
        }
        let distinct_queries = distinct
            .challenge_queries_without_replacement(36, 1 << 12, 64)
            .unwrap();
        assert_eq!(distinct_queries, legacy_queries);
        assert_eq!(distinct.diagnostic_state(), legacy.diagnostic_state());
    }

    /// Adversarial query stream whose first two candidates collide. The
    /// sampler must skip the duplicate, consume the next block, and retain
    /// the order of the first occurrence of every accepted position.
    fn duplicate_query_prefix_hash(inputs: &[&[u8]]) -> [u8; 32] {
        if let Some(state) = framed_state(inputs, DOM_SQUEEZE) {
            let first = state[0] == 0;
            let words = if first {
                [7u32, 7, 8, 9, 10, 11, 12, 13]
            } else {
                [14u32, 15, 16, 17, 18, 19, 20, 21]
            };
            let mut block = [0u8; 32];
            for (index, word) in words.into_iter().enumerate() {
                block[index * 4..index * 4 + 4].copy_from_slice(&word.to_le_bytes());
            }
            block
        } else if let Some(state) = framed_state(inputs, DOM_ADVANCE) {
            let mut state: [u8; 32] = state.try_into().unwrap();
            state[0] = state[0].wrapping_add(1);
            state
        } else {
            test_hash(inputs)
        }
    }

    #[test]
    fn without_replacement_sampler_skips_an_adversarial_duplicate_prefix() {
        let mut transcript = Transcript::new(duplicate_query_prefix_hash);
        let queries = transcript
            .challenge_queries_without_replacement(8, 1 << 12, 16)
            .unwrap();
        assert_eq!(queries, [7, 8, 9, 10, 11, 12, 13, 14]);
        assert_eq!(transcript.diagnostic_state()[0], 2);
    }

    fn all_zero_hash(_inputs: &[&[u8]]) -> [u8; 32] {
        [0u8; 32]
    }

    fn zero_then_nonzero_hash(inputs: &[&[u8]]) -> [u8; 32] {
        if let Some(state) = framed_state(inputs, DOM_SQUEEZE) {
            let mut block = [0u8; 32];
            if state[0] != 0 {
                for (word, chunk) in block.chunks_exact_mut(4).enumerate() {
                    chunk.copy_from_slice(&(word as u32 + 1).to_le_bytes());
                }
            }
            block
        } else if let Some(state) = framed_state(inputs, DOM_ADVANCE) {
            let mut state: [u8; 32] = state.try_into().unwrap();
            state[0] = state[0].wrapping_add(1);
            state
        } else {
            test_hash(inputs)
        }
    }

    #[test]
    fn nonzero_qm31_sampler_rejects_zero_with_fresh_state_and_is_bounded() {
        let mut accepts_second = Transcript::new(zero_then_nonzero_hash);
        let value = accepts_second.challenge_nonzero_qm31().unwrap();
        assert_eq!(
            value,
            QM31 {
                c0: CM31::new(M31(1), M31(2)),
                c1: CM31::new(M31(3), M31(4)),
            }
        );
        assert_eq!(accepts_second.diagnostic_state()[0], 2);

        let mut exhausts = Transcript::new(all_zero_hash);
        assert_eq!(
            exhausts.challenge_nonzero_qm31(),
            Err(ChallengeSampleExhausted)
        );
    }

    #[test]
    fn without_replacement_query_sampler_has_explicit_bounded_exhaustion() {
        let mut transcript = Transcript::new(all_zero_hash);
        assert_eq!(
            transcript.challenge_queries_without_replacement(2, 8, 8),
            Err(QuerySampleError::DrawLimitExhausted {
                accepted: 1,
                max_draws: 8,
            })
        );
        let mut invalid = Transcript::new(test_hash);
        assert_eq!(
            invalid.challenge_queries_without_replacement(1, 7, 8),
            Err(QuerySampleError::BoundNotPowerOfTwo { bound: 7 })
        );
        assert_eq!(
            invalid.challenge_queries_without_replacement(9, 8, 16),
            Err(QuerySampleError::CountExceedsBound { count: 9, bound: 8 })
        );
    }

    fn cm31_only_hash(inputs: &[&[u8]]) -> [u8; 32] {
        if framed_state(inputs, DOM_SQUEEZE).is_some() {
            let mut block = [0u8; 32];
            block[0..4].copy_from_slice(&1u32.to_le_bytes());
            block[4..8].copy_from_slice(&2u32.to_le_bytes());
            // c1 limbs stay zero: every candidate is in the CM31 subfield.
            block
        } else {
            test_hash(inputs)
        }
    }

    #[test]
    fn ood_sampler_rejects_subfield_points_with_a_bound() {
        let mut t = Transcript::new(cm31_only_hash);
        assert_eq!(
            t.challenge_ood_qm31(),
            Err(OodSampleError::SubfieldSampleExhausted)
        );

        let mut circle = Transcript::new(cm31_only_hash);
        assert_eq!(
            circle.challenge_secure_circle_point(),
            Err(CirclePointSampleError::ParameterSampleExhausted)
        );
    }

    fn singular_circle_hash(inputs: &[&[u8]]) -> [u8; 32] {
        if framed_state(inputs, DOM_SQUEEZE).is_some() {
            let mut block = [0u8; 32];
            // t = i in CM31, hence 1+t^2 = 0. The pure helper reports the
            // singularity; the bounded transcript sampler retries then errs.
            block[4..8].copy_from_slice(&1u32.to_le_bytes());
            block
        } else {
            test_hash(inputs)
        }
    }

    #[test]
    fn circle_sampler_bounds_singular_parameter_retries() {
        let mut transcript = Transcript::new(singular_circle_hash);
        assert_eq!(
            transcript.challenge_secure_circle_point(),
            Err(CirclePointSampleError::ParameterSampleExhausted)
        );
    }

    /// Backend that rejects exactly the first draw: word 0 masks to P, the
    /// retry must consume the NEXT word (fresh bytes), not re-hash.
    fn first_word_p_hash(inputs: &[&[u8]]) -> [u8; 32] {
        if framed_state(inputs, DOM_SQUEEZE).is_some() {
            // DOM_SQUEEZE block: word0 = P (rejected), then 1, 2, 3, 4, ...
            let mut block = [0u8; 32];
            block[0..4].copy_from_slice(&0x7FFF_FFFFu32.to_le_bytes());
            for (w, chunk) in block[4..].chunks_exact_mut(4).enumerate() {
                chunk.copy_from_slice(&(w as u32 + 1).to_le_bytes());
            }
            block
        } else {
            test_hash(inputs)
        }
    }

    #[test]
    fn sampler_rejects_p_and_uses_fresh_word() {
        let mut t = Transcript::new(first_word_p_hash);
        let alpha = t.challenge_qm31().expect("must accept on retry");
        assert_eq!(
            alpha,
            QM31 {
                c0: CM31 {
                    a: M31(1),
                    b: M31(2)
                },
                c1: CM31 {
                    a: M31(3),
                    b: M31(4)
                },
            }
        );
        // and no limb can ever be the folded-P artifact of the old sampler
        assert!(alpha.c0.a.0 < P);
    }

    fn point_bytes(point: SecureCirclePoint) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        point.x.write_le_bytes(&mut bytes[..16]);
        point.y.write_le_bytes(&mut bytes[16..]);
        bytes
    }

    fn circle_s2_fixture(weakened: bool) -> (SecureCirclePoint, SecureCirclePoint, [u8; 32]) {
        let mut transcript = Transcript::new(test_hash);
        transcript.absorb(label::PROFILE, b"aspis-circle-s2-sampler-fixture-v0");
        transcript.absorb(label::ROOT, &[0x31; 32]);

        let first = transcript
            .challenge_secure_circle_point()
            .expect("fixture first circle parameter must accept");
        let (second, first_mix, second_mix) = if weakened {
            // Deliberately wrong: squeeze the second point before the first
            // claimed value and mix bind the transcript.
            let second = transcript
                .challenge_secure_circle_point()
                .expect("weakened fixture second circle parameter must accept");
            transcript.absorb(label::OOD_VALUE, &[0x41; 16]);
            let first_mix = transcript.challenge_qm31().unwrap();
            transcript.absorb(label::OOD_VALUE, &[0x42; 16]);
            let second_mix = transcript.challenge_qm31().unwrap();
            (second, first_mix, second_mix)
        } else {
            transcript.absorb(label::OOD_VALUE, &[0x41; 16]);
            let first_mix = transcript.challenge_qm31().unwrap();
            let second = transcript
                .challenge_secure_circle_point()
                .expect("fixture second circle parameter must accept");
            transcript.absorb(label::OOD_VALUE, &[0x42; 16]);
            let second_mix = transcript.challenge_qm31().unwrap();
            (second, first_mix, second_mix)
        };

        let first_bytes = point_bytes(first);
        let second_bytes = point_bytes(second);
        let mut first_mix_bytes = [0u8; 16];
        let mut second_mix_bytes = [0u8; 16];
        first_mix.write_le_bytes(&mut first_mix_bytes);
        second_mix.write_le_bytes(&mut second_mix_bytes);
        let digest = test_hash(&[
            &first_bytes,
            &first_mix_bytes,
            &second_bytes,
            &second_mix_bytes,
        ]);
        (first, second, digest)
    }

    #[test]
    fn two_sequential_circle_samples_fixture_is_pinned() {
        let (first, second, digest) = circle_s2_fixture(false);
        assert_ne!(first, second);
        for point in [first, second] {
            assert_eq!(point.x.square().add(point.y.square()), QM31::ONE);
            assert!(point.x.c1 != CM31::ZERO || point.y.c1 != CM31::ZERO);
        }
        assert_eq!(digest, CIRCLE_S2_FIXTURE_EXPECTED);
    }

    #[test]
    fn weakened_two_sample_ordering_has_teeth() {
        let (canonical_first, canonical_second, canonical_digest) = circle_s2_fixture(false);
        let (weakened_first, weakened_second, weakened_digest) = circle_s2_fixture(true);
        assert_eq!(canonical_first, weakened_first);
        assert_ne!(canonical_second, weakened_second);
        assert_ne!(canonical_digest, weakened_digest);
    }
}
