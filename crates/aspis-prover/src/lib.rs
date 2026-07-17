//! Host-only prover for the Aspis Stage 1 substrate.
//!
//! Commits evaluations of a polynomial (degree < 2^log_rows, M31
//! coefficients) over a coset of a 2^k subgroup of the M31 circle group in
//! CM31, folds it WHIR-style two variables per round to an explicit final
//! polynomial, supplies a transcript-bound evaluation at one derived OOD
//! point per committed layer, and packages openings in the envelope
//! `aspis-core` parses. A degree-6 relation sumcheck is interleaved before
//! each fold challenge, enforcing both OOD and external evaluation claims.
//!
//! The prover mirrors the verifier's transcript step-for-step; any
//! divergence is caught by the parity tests (10/10 accept on host must equal
//! accept on SBF for identical bytes).

pub mod circle_candidate;
pub mod circle_candidate_openings;
pub mod pow;
pub mod state_only_candidate;
pub mod state_only_candidate_prefix;
pub mod state_only_circle_relation;
pub mod state_only_entropy;
pub mod state_only_good_spend;
pub mod state_only_hiding;
pub mod state_only_hiding_rank;
pub mod state_only_private_openings;
pub mod state_only_proof;
pub mod state_only_spend;
pub mod state_only_spend_candidate;
pub mod state_only_spend_openings;
pub mod state_only_spend_release;
pub mod state_only_zerocheck;

/// Provisional Aspis v5 masking component (A): the block-form circle mask.
/// Feature-gated (`v5-mask`, default OFF) and entirely outside the v4 path.
#[cfg(feature = "v5-mask")]
pub mod v5_mask;

#[cfg(test)]
mod state_only_spend_privacy_regressions;

use aspis_core::field::{cm31_batch_inverse, CM31, M31, QM31};
use aspis_core::merkle::{leaf_hash, node_hash, node_hash4};
use aspis_core::params::{FoldPayload, MerkleMode, Profile, FINAL_POLY_LOG_LEN};
use aspis_core::proof::{
    fiber_value_bytes, Header, EXACT_WIDE_C1_COLUMNS, FLAG_EVALUATION_CLAIM, FLAG_EXACT_WIDE_C1,
    FLAG_M31_CIRCLE_C1_DIAGNOSTIC, FLAG_SECOND_PHASE, HEADER_LEN, SECOND_PHASE_LAYER_TAG,
    VERSION_V3, VERSION_V4_S2,
};
use aspis_core::sumcheck::{
    polynomial_for_base, polynomial_for_extension, WeightAccumulator, SUMCHECK_BYTES,
};
use aspis_core::transcript::{label, Transcript};
use aspis_core::verify::{domain_point, layer_geometry, EvaluationClaim};
use aspis_core::HashFn;

/// sha2-backed hashv, byte-compatible with the Solana SHA-256 syscall.
pub fn host_hashv(inputs: &[&[u8]]) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    for input in inputs {
        hasher.update(input);
    }
    hasher.finalize().into()
}

pub const HOST_HASH: HashFn = host_hashv;

fn find_grinding_nonce(transcript: &Transcript, bits: u8) -> u64 {
    pow::find_grinding_nonce(transcript, bits)
}

/// Radix-2 DIT NTT over CM31 using root `omega` of order `values.len()`.
/// In-place, natural order in, natural order out (bit-reversal applied).
fn ntt_cm31(values: &mut [CM31], omega: CM31) {
    let n = values.len();
    debug_assert!(n.is_power_of_two());
    // bit reversal
    let bits = n.trailing_zeros();
    for i in 0..n {
        let j = (i as u32).reverse_bits() >> (32 - bits);
        let j = j as usize;
        if j > i {
            values.swap(i, j);
        }
    }
    // butterflies
    let mut len = 2usize;
    while len <= n {
        let w_len = omega.pow((n / len) as u64);
        for start in (0..n).step_by(len) {
            let mut w = CM31::ONE;
            for k in 0..len / 2 {
                let a = values[start + k];
                let b = values[start + k + len / 2].mul(w);
                values[start + k] = a.add(b);
                values[start + k + len / 2] = a.sub(b);
                w = w.mul(w_len);
            }
        }
        len <<= 1;
    }
}

/// Evaluate the polynomial with coefficients `coeffs` (lifted M31) over the
/// coset offset*<omega> in natural index order.
fn coset_evaluate(coeffs: &[M31], offset: CM31, omega: CM31, domain_size: usize) -> Vec<CM31> {
    let mut values = vec![CM31::ZERO; domain_size];
    let mut scale = CM31::ONE;
    for (j, c) in coeffs.iter().enumerate() {
        values[j] = scale.mul_m31(*c);
        scale = scale.mul(offset);
    }
    ntt_cm31(&mut values, omega);
    values
}

/// Merkle tree over fiber-packed leaves; levels[0] = leaf hashes.
struct FiberTree {
    levels: Vec<Vec<[u8; 32]>>,
    radix4: bool,
}

impl FiberTree {
    fn build(
        hash: HashFn,
        layer: u8,
        leaf_bytes: &[Vec<u8>],
        merkle_mode: MerkleMode,
    ) -> FiberTree {
        let radix4 = merkle_mode == MerkleMode::Radix4MinimalSubtree;
        let mut levels = vec![leaf_bytes
            .iter()
            .map(|bytes| leaf_hash(hash, layer, bytes))
            .collect::<Vec<_>>()];
        while levels.last().unwrap().len() > 1 {
            let prev = levels.last().unwrap();
            if radix4 {
                assert_eq!(prev.len() % 4, 0);
                let mut next = Vec::with_capacity(prev.len() / 4);
                for children in prev.chunks_exact(4) {
                    next.push(node_hash4(hash, children.try_into().unwrap()));
                }
                levels.push(next);
            } else {
                assert_eq!(prev.len() % 2, 0);
                let mut next = Vec::with_capacity(prev.len() / 2);
                for pair in prev.chunks_exact(2) {
                    next.push(node_hash(hash, &pair[0], &pair[1]));
                }
                levels.push(next);
            }
        }
        FiberTree { levels, radix4 }
    }

    fn root(&self) -> [u8; 32] {
        self.levels.last().unwrap()[0]
    }

    fn single_path(&self, mut index: u32) -> Vec<[u8; 32]> {
        assert!(!self.radix4);
        let mut path = Vec::with_capacity(self.levels.len() - 1);
        for level in &self.levels[..self.levels.len() - 1] {
            path.push(level[(index ^ 1) as usize]);
            index >>= 1;
        }
        path
    }

    /// Frontier nodes for sorted unique indices, in the deterministic
    /// traversal order `verify_minimal_subtree` consumes.
    fn minimal_subtree(&self, indices: &[u32]) -> Vec<[u8; 32]> {
        if self.radix4 {
            return self.radix4_minimal_subtree(indices);
        }
        let mut nodes = Vec::new();
        let mut level_indices: Vec<u32> = indices.to_vec();
        for level in &self.levels[..self.levels.len() - 1] {
            let mut next = Vec::new();
            let mut i = 0;
            while i < level_indices.len() {
                let idx = level_indices[i];
                if idx & 1 == 0 {
                    if i + 1 < level_indices.len() && level_indices[i + 1] == idx + 1 {
                        i += 2;
                    } else {
                        nodes.push(level[(idx + 1) as usize]);
                        i += 1;
                    }
                } else {
                    nodes.push(level[(idx - 1) as usize]);
                    i += 1;
                }
                next.push(idx >> 1);
            }
            level_indices = next;
        }
        nodes
    }

    fn radix4_minimal_subtree(&self, indices: &[u32]) -> Vec<[u8; 32]> {
        let mut nodes = Vec::new();
        let mut level_indices = indices.to_vec();
        for level in &self.levels[..self.levels.len() - 1] {
            let mut next = Vec::new();
            let mut position = 0usize;
            while position < level_indices.len() {
                let parent = level_indices[position] >> 2;
                let mut present = 0u8;
                while position < level_indices.len() && level_indices[position] >> 2 == parent {
                    present |= 1u8 << (level_indices[position] & 3);
                    position += 1;
                }
                for slot in 0..4u32 {
                    if present & (1u8 << slot) == 0 {
                        nodes.push(level[(parent * 4 + slot) as usize]);
                    }
                }
                next.push(parent);
            }
            level_indices = next;
        }
        nodes
    }
}

/// One committed layer retained for the opening phase.
struct LayerData {
    /// per-fiber leaf bytes (fiber i = values at {i, i+F, i+2F, i+3F})
    leaf_bytes: Vec<Vec<u8>>,
    tree: FiberTree,
    /// C2's QM31 fibers/tree exist only at layer zero.
    second_phase_leaf_bytes: Option<Vec<Vec<u8>>>,
    second_phase_tree: Option<FiberTree>,
    /// per-fiber carried payload (g1, g2) for proof_carried_round_local
    carried: Vec<(QM31, QM31)>,
}

pub struct ProveOptions {
    pub fold_payload: FoldPayload,
    pub merkle_mode: MerkleMode,
}

#[derive(Clone, Copy)]
enum OodBehavior {
    Honest,
    LieAt(u32),
    AbsorbAfterAlpha,
    SecondAbsorbAfterAlpha,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum OrderingBehavior {
    Canonical,
    ChiBeforeC1,
    GammaBeforeClaims,
    GammaBeforeSecondHelperClaim,
}

/// Produce a proof for the committed polynomial `coeffs` (len must be
/// 2^log_rows, M31, any content — the v0 slice binds bytes, not a statement)
/// against `statement_digest`.
pub fn prove(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    options: &ProveOptions,
    hash: HashFn,
) -> Vec<u8> {
    prove_inner(
        profile,
        coeffs,
        statement_digest,
        None,
        options,
        hash,
        VERSION_V3,
        false,
        None,
        None,
        OrderingBehavior::Canonical,
        OodBehavior::Honest,
    )
}

/// Produce a claim-carrying two-phase proof. C1 is absorbed before lambda and
/// chi; a deterministic Stage-1 helper is committed as C2; the main and C2
/// evaluations are absorbed before gamma; and their gamma-RLC is enforced by
/// the relation sumcheck. The helper is plumbing/cost scaffolding, not the
/// Stage-2 LogUp relation.
pub fn prove_with_claim(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    claim: &EvaluationClaim,
    options: &ProveOptions,
    hash: HashFn,
) -> Vec<u8> {
    prove_inner(
        profile,
        coeffs,
        statement_digest,
        Some(claim),
        options,
        hash,
        VERSION_V3,
        true,
        Some(&synthetic_second_phase_coefficients),
        None,
        OrderingBehavior::Canonical,
        OodBehavior::Honest,
    )
}

/// Produce the two-phase Stage-1 plumbing/cost proof without an external
/// evaluation claim. The helper is deterministic but challenge-dependent;
/// the verifier treats C2 generically and authenticates/recombines it.
pub fn prove_with_synthetic_second_phase(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    options: &ProveOptions,
    hash: HashFn,
) -> Vec<u8> {
    prove_inner(
        profile,
        coeffs,
        statement_digest,
        None,
        options,
        hash,
        VERSION_V3,
        true,
        Some(&synthetic_second_phase_coefficients),
        None,
        OrderingBehavior::Canonical,
        OodBehavior::Honest,
    )
}

/// Generic second-phase prover interface. The builder runs only after C1 is
/// transcript-bound and receives the resulting `(lambda, chi)` challenges.
/// Stage 2 can supply its LogUp helper here without changing the proof
/// envelope or verifier schedule.
pub fn prove_with_second_phase_builder<F>(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    claim: Option<&EvaluationClaim>,
    options: &ProveOptions,
    hash: HashFn,
    build_helper: F,
) -> Vec<u8>
where
    F: Fn(&[M31], QM31, QM31) -> Vec<QM31>,
{
    prove_inner(
        profile,
        coeffs,
        statement_digest,
        claim,
        options,
        hash,
        VERSION_V3,
        true,
        Some(&build_helper),
        None,
        OrderingBehavior::Canonical,
        OodBehavior::Honest,
    )
}

/// Produce an explicit v4 proof with two sequential `(beta, y, mu)` OOD
/// samples in every round. [`prove`] remains pinned to the byte-compatible
/// v3 envelope.
pub fn prove_v4(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    options: &ProveOptions,
    hash: HashFn,
) -> Vec<u8> {
    prove_inner(
        profile,
        coeffs,
        statement_digest,
        None,
        options,
        hash,
        VERSION_V4_S2,
        false,
        None,
        None,
        OrderingBehavior::Canonical,
        OodBehavior::Honest,
    )
}

/// V4/s=2 analogue of [`prove_with_claim`]. Its single C2 root commits two
/// helper columns; both evaluations are absorbed before gamma and their
/// `gamma, gamma^2` RLC is enforced by the relation sumcheck.
pub fn prove_with_claim_v4(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    claim: &EvaluationClaim,
    options: &ProveOptions,
    hash: HashFn,
) -> Vec<u8> {
    prove_inner(
        profile,
        coeffs,
        statement_digest,
        Some(claim),
        options,
        hash,
        VERSION_V4_S2,
        true,
        None,
        Some(&synthetic_second_phase_coefficients_v4),
        OrderingBehavior::Canonical,
        OodBehavior::Honest,
    )
}

/// Diagnostic-only v4 exact-wide PCS scaffold. Column zero is the honest
/// claimed polynomial; columns 1..48 are authenticated zero columns. The
/// verifier still parses and combines all 49 CM31 lanes and the two nonzero
/// synthetic QM31 helpers, but production verification rejects this flag
/// until the final two-point/102-value statement semantics are implemented.
pub fn prove_exact_wide_v4_scaffold_for_measurement(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    claim: &EvaluationClaim,
    options: &ProveOptions,
    hash: HashFn,
) -> Vec<u8> {
    prove_inner_with_shape(
        profile,
        coeffs,
        statement_digest,
        Some(claim),
        options,
        hash,
        VERSION_V4_S2,
        true,
        None,
        Some(&synthetic_second_phase_coefficients_v4),
        OrderingBehavior::Canonical,
        OodBehavior::Honest,
        true,
        false,
    )
}

/// Deliberately malformed-basis prover used only to prove the M31 diagnostic
/// framing guard has teeth. It emits the new flag and a fully self-consistent
/// transcript while retaining the legacy scalar CM31 leaf semantics. A
/// canonical verifier must reject it; the feature-gated weakened verifier
/// intentionally accepts it.
#[cfg(feature = "insecure-test-framing")]
pub fn prove_with_claim_v4_m31_circle_flag_legacy_basis_for_tests(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    claim: &EvaluationClaim,
    options: &ProveOptions,
    hash: HashFn,
) -> Vec<u8> {
    assert_eq!(options.fold_payload, FoldPayload::RawFibers);
    assert_eq!(options.merkle_mode, MerkleMode::Radix4MinimalSubtree);
    prove_inner_with_shape(
        profile,
        coeffs,
        statement_digest,
        Some(claim),
        options,
        hash,
        VERSION_V4_S2,
        true,
        None,
        Some(&synthetic_second_phase_coefficients_v4),
        OrderingBehavior::Canonical,
        OodBehavior::Honest,
        false,
        true,
    )
}

/// V4/s=2 analogue of [`prove_with_synthetic_second_phase`], with two
/// synthetic helpers packed into each 128-byte C2 leaf.
pub fn prove_with_synthetic_second_phase_v4(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    options: &ProveOptions,
    hash: HashFn,
) -> Vec<u8> {
    prove_inner(
        profile,
        coeffs,
        statement_digest,
        None,
        options,
        hash,
        VERSION_V4_S2,
        true,
        None,
        Some(&synthetic_second_phase_coefficients_v4),
        OrderingBehavior::Canonical,
        OodBehavior::Honest,
    )
}

/// V4/s=2 analogue of [`prove_with_second_phase_builder`]. The builder must
/// return `(helper_1, helper_2)`; both vectors must match `coeffs.len()`.
pub fn prove_with_second_phase_builder_v4<F>(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    claim: Option<&EvaluationClaim>,
    options: &ProveOptions,
    hash: HashFn,
    build_helper: F,
) -> Vec<u8>
where
    F: Fn(&[M31], QM31, QM31) -> (Vec<QM31>, Vec<QM31>),
{
    prove_inner(
        profile,
        coeffs,
        statement_digest,
        claim,
        options,
        hash,
        VERSION_V4_S2,
        true,
        None,
        Some(&build_helper),
        OrderingBehavior::Canonical,
        OodBehavior::Honest,
    )
}

/// Adversarial prover for the gamma-order test ONLY: squeezes gamma before
/// absorbing the main/C2 claimed evaluations. The canonical verifier must
/// reject. Never call outside tests.
#[doc(hidden)]
pub fn prove_with_gamma_before_claims_for_tests(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    claim: &EvaluationClaim,
    options: &ProveOptions,
    hash: HashFn,
) -> Vec<u8> {
    prove_inner(
        profile,
        coeffs,
        statement_digest,
        Some(claim),
        options,
        hash,
        VERSION_V3,
        true,
        Some(&synthetic_second_phase_coefficients),
        None,
        OrderingBehavior::GammaBeforeClaims,
        OodBehavior::Honest,
    )
}

/// Backward-compatible test helper name; this is now the precise
/// gamma-before-claims adversarial vector.
#[doc(hidden)]
pub fn prove_with_misordered_claim_for_tests(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    claim: &EvaluationClaim,
    options: &ProveOptions,
    hash: HashFn,
) -> Vec<u8> {
    prove_with_gamma_before_claims_for_tests(
        profile,
        coeffs,
        statement_digest,
        claim,
        options,
        hash,
    )
}

/// Adversarial prover for the C1-order test ONLY: squeezes lambda and chi
/// before C1 is absorbed. The canonical verifier must reject.
#[doc(hidden)]
pub fn prove_with_chi_before_c1_for_tests(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    options: &ProveOptions,
    hash: HashFn,
) -> Vec<u8> {
    prove_inner(
        profile,
        coeffs,
        statement_digest,
        None,
        options,
        hash,
        VERSION_V3,
        true,
        Some(&synthetic_second_phase_coefficients),
        None,
        OrderingBehavior::ChiBeforeC1,
        OodBehavior::Honest,
    )
}

/// Adversarial prover for the OOD challenge-order test ONLY: samples the
/// layer fold challenge before absorbing the claimed OOD value. The
/// canonical verifier must reject. Never call outside tests.
#[doc(hidden)]
pub fn prove_with_misordered_ood_for_tests(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    options: &ProveOptions,
    hash: HashFn,
) -> Vec<u8> {
    prove_inner(
        profile,
        coeffs,
        statement_digest,
        None,
        options,
        hash,
        VERSION_V3,
        false,
        None,
        None,
        OrderingBehavior::Canonical,
        OodBehavior::AbsorbAfterAlpha,
    )
}

/// V4 adversarial prover used to prove the second-triple ordering test has
/// teeth. It completes the first OOD triple, samples the second beta, then
/// squeezes alpha before absorbing the second y and deriving its mu. The
/// canonical verifier must reject; only the explicitly weakened test
/// verifier follows this schedule.
#[doc(hidden)]
pub fn prove_v4_with_misordered_second_ood_for_tests(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    options: &ProveOptions,
    hash: HashFn,
) -> Vec<u8> {
    prove_inner(
        profile,
        coeffs,
        statement_digest,
        None,
        options,
        hash,
        VERSION_V4_S2,
        true,
        None,
        Some(&synthetic_second_phase_coefficients_v4),
        OrderingBehavior::Canonical,
        OodBehavior::SecondAbsorbAfterAlpha,
    )
}

/// V4 adversarial prover used to prove both helper evaluations must precede
/// gamma. It absorbs the main claim and helper claim 1, squeezes gamma, then
/// absorbs helper claim 2. Canonical verification must reject these bytes;
/// only the matching deliberately weakened test verifier accepts them.
#[doc(hidden)]
pub fn prove_v4_with_gamma_before_second_helper_claim_for_tests(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    claim: &EvaluationClaim,
    options: &ProveOptions,
    hash: HashFn,
) -> Vec<u8> {
    prove_inner(
        profile,
        coeffs,
        statement_digest,
        Some(claim),
        options,
        hash,
        VERSION_V4_S2,
        true,
        None,
        Some(&synthetic_second_phase_coefficients_v4),
        OrderingBehavior::GammaBeforeSecondHelperClaim,
        OodBehavior::Honest,
    )
}

/// Adversarial prover for the explicit enforcement-caveat test ONLY: places
/// a false but transcript-consistent OOD value in one round. The verifier's
/// relation sumcheck must reject it at that round's boundary.
#[doc(hidden)]
pub fn prove_with_lying_ood_for_tests(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    lying_layer: u32,
    options: &ProveOptions,
    hash: HashFn,
) -> Vec<u8> {
    assert!(lying_layer < profile.num_rounds());
    prove_inner(
        profile,
        coeffs,
        statement_digest,
        None,
        options,
        hash,
        VERSION_V3,
        false,
        None,
        None,
        OrderingBehavior::Canonical,
        OodBehavior::LieAt(lying_layer),
    )
}

/// Multilinear evaluation of the coefficient table at z (big-endian variable
/// order: z[0] pairs with the highest coefficient-index bit). Used to form
/// honest claims; also the future sumcheck/fold-interleave ingredient.
pub fn multilinear_eval(coeffs: &[M31], z: &[QM31]) -> QM31 {
    assert_eq!(coeffs.len(), 1usize << z.len());
    // fold one variable at a time, last coordinate first (bit 0)
    let mut layer: Vec<QM31> = coeffs
        .iter()
        .map(|c| QM31::from_cm31(CM31::from_m31(*c)))
        .collect();
    for zi in z.iter().rev() {
        layer = (0..layer.len() / 2)
            .map(|j| layer[2 * j].add(zi.mul(layer[2 * j + 1].sub(layer[2 * j]))))
            .collect();
    }
    layer[0]
}

fn multilinear_eval_extension(coeffs: &[QM31], z: &[QM31]) -> QM31 {
    assert_eq!(coeffs.len(), 1usize << z.len());
    let mut layer = coeffs.to_vec();
    for zi in z.iter().rev() {
        layer = (0..layer.len() / 2)
            .map(|index| layer[2 * index].add(zi.mul(layer[2 * index + 1].sub(layer[2 * index]))))
            .collect();
    }
    layer[0]
}

/// Deterministic challenge-dependent helper used to exercise the generic C2
/// proof boundary before Stage 2 supplies the actual LogUp helper. Its exact
/// algebra is intentionally not assigned statement soundness.
fn synthetic_second_phase_coefficients(coeffs: &[M31], lambda: QM31, chi: QM31) -> Vec<QM31> {
    let cross = lambda.mul(chi);
    coeffs
        .iter()
        .enumerate()
        .map(|(index, coefficient)| {
            let main = QM31::from_cm31(CM31::from_m31(*coefficient));
            let index_value = QM31::from_cm31(CM31::from_m31(M31((index + 1) as u32)));
            lambda.mul(main).add(chi.mul(index_value)).add(cross)
        })
        .collect()
}

/// V4 commits two challenge-dependent helper columns in one C2 tree. These
/// remain plumbing/cost scaffolding; neither vector is assigned the future
/// payment statement's semantics.
fn synthetic_second_phase_coefficients_v4(
    coeffs: &[M31],
    lambda: QM31,
    chi: QM31,
) -> (Vec<QM31>, Vec<QM31>) {
    let helper_1 = synthetic_second_phase_coefficients(coeffs, lambda, chi);
    let offset = lambda.square().add(chi.square());
    let helper_2 = coeffs
        .iter()
        .enumerate()
        .map(|(index, coefficient)| {
            let main = QM31::from_cm31(CM31::from_m31(*coefficient));
            let index_value = QM31::from_cm31(CM31::from_m31(M31((index + 1) as u32)));
            chi.mul(main).add(lambda.mul(index_value)).add(offset)
        })
        .collect();
    (helper_1, helper_2)
}

fn evaluate_m31_coefficients(coeffs: &[M31], point: QM31) -> QM31 {
    coeffs.iter().rev().fold(QM31::ZERO, |acc, coefficient| {
        acc.mul(point)
            .add(QM31::from_cm31(CM31::from_m31(*coefficient)))
    })
}

fn evaluate_qm31_coefficients(coeffs: &[QM31], point: QM31) -> QM31 {
    coeffs.iter().rev().fold(QM31::ZERO, |acc, coefficient| {
        acc.mul(point).add(*coefficient)
    })
}

type SecondPhaseBuilder<'a> = dyn Fn(&[M31], QM31, QM31) -> Vec<QM31> + 'a;
type SecondPhaseBuilderV4<'a> = dyn Fn(&[M31], QM31, QM31) -> (Vec<QM31>, Vec<QM31>) + 'a;

#[allow(clippy::too_many_arguments)]
fn prove_inner(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    claim: Option<&EvaluationClaim>,
    options: &ProveOptions,
    hash: HashFn,
    proof_version: u8,
    second_phase: bool,
    second_phase_builder: Option<&SecondPhaseBuilder<'_>>,
    second_phase_builder_v4: Option<&SecondPhaseBuilderV4<'_>>,
    ordering: OrderingBehavior,
    ood_behavior: OodBehavior,
) -> Vec<u8> {
    prove_inner_with_shape(
        profile,
        coeffs,
        statement_digest,
        claim,
        options,
        hash,
        proof_version,
        second_phase,
        second_phase_builder,
        second_phase_builder_v4,
        ordering,
        ood_behavior,
        false,
        false,
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_inner_with_shape(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    claim: Option<&EvaluationClaim>,
    options: &ProveOptions,
    hash: HashFn,
    proof_version: u8,
    second_phase: bool,
    second_phase_builder: Option<&SecondPhaseBuilder<'_>>,
    second_phase_builder_v4: Option<&SecondPhaseBuilderV4<'_>>,
    ordering: OrderingBehavior,
    ood_behavior: OodBehavior,
    exact_wide_c1: bool,
    m31_circle_as_legacy: bool,
) -> Vec<u8> {
    assert!(proof_version == VERSION_V3 || proof_version == VERSION_V4_S2);
    assert_eq!(coeffs.len(), 1usize << profile.log_rows);
    assert!(claim.is_none() || second_phase);
    assert!(!exact_wide_c1 || (proof_version == VERSION_V4_S2 && second_phase));
    assert!(!m31_circle_as_legacy || (proof_version == VERSION_V4_S2 && second_phase));
    assert!(!(exact_wide_c1 && m31_circle_as_legacy));
    match proof_version {
        VERSION_V3 => {
            assert_eq!(second_phase, second_phase_builder.is_some());
            assert!(second_phase_builder_v4.is_none());
        }
        VERSION_V4_S2 => {
            assert_eq!(second_phase, second_phase_builder_v4.is_some());
            assert!(second_phase_builder.is_none());
        }
        _ => unreachable!(),
    }
    let num_rounds = profile.num_rounds();
    let query_count = profile.query_count as usize;

    let header = Header {
        version: proof_version,
        profile_id: profile.id,
        log_rows: profile.log_rows,
        log_blowup: profile.log_blowup,
        query_count: profile.query_count,
        grinding_bits: profile.grinding_bits,
        fold_payload: options.fold_payload as u8,
        merkle_mode: options.merkle_mode as u8,
        num_rounds,
        final_poly_log_len: FINAL_POLY_LOG_LEN,
        flags: (if claim.is_some() {
            FLAG_EVALUATION_CLAIM
        } else {
            0
        }) | (if second_phase { FLAG_SECOND_PHASE } else { 0 })
            | (if exact_wide_c1 { FLAG_EXACT_WIDE_C1 } else { 0 })
            | (if m31_circle_as_legacy {
                FLAG_M31_CIRCLE_C1_DIAGNOSTIC
            } else {
                0
            }),
    };
    let mut header_bytes = [0u8; HEADER_LEN];
    header.write(&mut header_bytes);

    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, &header_bytes);
    transcript.absorb(label::STATEMENT, statement_digest);

    let early_phase_challenges = if second_phase && ordering == OrderingBehavior::ChiBeforeC1 {
        Some((
            transcript
                .challenge_qm31()
                .expect("prover lambda sampler exhausted (2^-248 per limb)"),
            transcript
                .challenge_qm31()
                .expect("prover chi sampler exhausted (2^-248 per limb)"),
        ))
    } else {
        None
    };

    // ---- commit phase ----
    let geom0 = layer_geometry(profile, 0);
    let layer0_values = coset_evaluate(
        coeffs,
        geom0.offset,
        geom0.omega,
        geom0.domain_size as usize,
    );

    let mut ext_coeffs: Vec<QM31> = Vec::new(); // populated after first fold
    let mut layers: Vec<LayerData> = Vec::new();
    let mut roots: Vec<[u8; 32]> = Vec::new();
    let mut ood_values: Vec<Vec<[u8; 16]>> = Vec::new();
    let mut sumcheck_polynomials: Vec<[u8; SUMCHECK_BYTES]> = Vec::new();
    let mut relation_weights = WeightAccumulator::empty(profile.log_rows);
    let mut second_phase_root: Option<[u8; 32]> = None;
    let mut second_phase_claim_bytes: Vec<[u8; 16]> = Vec::new();

    for layer in 0..num_rounds {
        let geom = layer_geometry(profile, layer);
        let fiber_count = geom.fiber_count as usize;
        let value_bytes = if layer == 0 && m31_circle_as_legacy {
            fiber_value_bytes(layer)
        } else {
            header.first_phase_leaf_len(layer)
        };

        // These are the values of the polynomial actually folded this round.
        // At layer zero C1 is base-valued, while a two-phase proof folds the
        // gamma-combination of C1 and C2 in QM31.
        let mut fold_base_values: Option<Vec<CM31>> = None;
        let mut fold_ext_values: Option<Vec<QM31>> = None;
        if layer == 0 && !second_phase {
            fold_base_values = Some(layer0_values.clone());
        } else if layer > 0 {
            fold_ext_values = Some(coset_evaluate_qm31(
                &ext_coeffs,
                geom.offset,
                geom.omega,
                geom.domain_size as usize,
            ));
        }

        let mut leaf_bytes = Vec::with_capacity(fiber_count);
        for f in 0..fiber_count {
            let mut bytes = vec![0u8; value_bytes];
            for m in 0..4 {
                let idx = f + m * fiber_count;
                if layer == 0 {
                    let offset = if exact_wide_c1 {
                        (m * EXACT_WIDE_C1_COLUMNS) * 8
                    } else {
                        m * 8
                    };
                    // The exact-wide measurement scaffold commits column 0
                    // honestly and leaves columns 1..48 at the Vec's zero
                    // initialization. The verifier still authenticates,
                    // parses and multiplies every lane.
                    layer0_values[idx].write_le_bytes(&mut bytes[offset..offset + 8]);
                } else {
                    fold_ext_values.as_ref().unwrap()[idx]
                        .write_le_bytes(&mut bytes[m * 16..m * 16 + 16]);
                }
            }
            leaf_bytes.push(bytes);
        }
        let tree = FiberTree::build(hash, layer as u8, &leaf_bytes, options.merkle_mode);
        let root = tree.root();
        transcript.absorb(label::ROOT, &root);
        roots.push(root);

        let mut second_phase_leaf_bytes = None;
        let mut second_phase_tree = None;
        if layer == 0 && second_phase {
            let (lambda, chi) = early_phase_challenges.unwrap_or_else(|| {
                (
                    transcript
                        .challenge_qm31()
                        .expect("prover lambda sampler exhausted (2^-248 per limb)"),
                    transcript
                        .challenge_qm31()
                        .expect("prover chi sampler exhausted (2^-248 per limb)"),
                )
            });
            let (helper_coeffs_1, helper_coeffs_2) = if proof_version == VERSION_V4_S2 {
                let (helper_1, helper_2) = second_phase_builder_v4.unwrap()(coeffs, lambda, chi);
                (helper_1, Some(helper_2))
            } else {
                (second_phase_builder.unwrap()(coeffs, lambda, chi), None)
            };
            assert_eq!(helper_coeffs_1.len(), coeffs.len());
            if let Some(helper_2) = &helper_coeffs_2 {
                assert_eq!(helper_2.len(), coeffs.len());
            }
            let helper_values_1 = coset_evaluate_qm31(
                &helper_coeffs_1,
                geom.offset,
                geom.omega,
                geom.domain_size as usize,
            );
            let helper_values_2 = helper_coeffs_2.as_ref().map(|helper_2| {
                coset_evaluate_qm31(helper_2, geom.offset, geom.omega, geom.domain_size as usize)
            });
            let mut helper_leaves = Vec::with_capacity(fiber_count);
            for fiber in 0..fiber_count {
                let mut bytes = vec![0u8; header.second_phase_leaf_len()];
                for slot in 0..4 {
                    let index = fiber + slot * fiber_count;
                    helper_values_1[index].write_le_bytes(&mut bytes[slot * 16..slot * 16 + 16]);
                    if let Some(helper_2) = &helper_values_2 {
                        let offset = (4 + slot) * 16;
                        helper_2[index].write_le_bytes(&mut bytes[offset..offset + 16]);
                    }
                }
                helper_leaves.push(bytes);
            }
            let helper_tree = FiberTree::build(
                hash,
                SECOND_PHASE_LAYER_TAG,
                &helper_leaves,
                options.merkle_mode,
            );
            let helper_root = helper_tree.root();
            transcript.absorb(label::SECOND_PHASE_ROOT, &helper_root);
            second_phase_root = Some(helper_root);

            let mut early_gamma = if ordering == OrderingBehavior::GammaBeforeClaims {
                Some(
                    transcript
                        .challenge_qm31()
                        .expect("prover gamma sampler exhausted (2^-248 per limb)"),
                )
            } else {
                None
            };

            if let Some(main_claim) = claim {
                transcript.absorb(label::CLAIM, &main_claim.to_bytes());
            }
            let helper_claim_1 = claim.map(|main_claim| {
                let value = multilinear_eval_extension(&helper_coeffs_1, &main_claim.z);
                let mut bytes = [0u8; 16];
                value.write_le_bytes(&mut bytes);
                transcript.absorb(label::SECOND_PHASE_CLAIM, &bytes);
                second_phase_claim_bytes.push(bytes);
                value
            });
            if helper_claim_1.is_some()
                && ordering == OrderingBehavior::GammaBeforeSecondHelperClaim
            {
                early_gamma = Some(
                    transcript
                        .challenge_qm31()
                        .expect("prover gamma sampler exhausted (2^-248 per limb)"),
                );
            }
            let helper_claim_2 = match (claim, helper_coeffs_2.as_ref()) {
                (Some(main_claim), Some(helper_2)) => {
                    let value = multilinear_eval_extension(helper_2, &main_claim.z);
                    let mut bytes = [0u8; 16];
                    value.write_le_bytes(&mut bytes);
                    transcript.absorb(label::SECOND_PHASE_CLAIM, &bytes);
                    second_phase_claim_bytes.push(bytes);
                    Some(value)
                }
                _ => None,
            };

            let gamma = early_gamma.unwrap_or_else(|| {
                transcript
                    .challenge_qm31()
                    .expect("prover gamma sampler exhausted (2^-248 per limb)")
            });

            let helper_weight_1 = if exact_wide_c1 { gamma.pow(49) } else { gamma };
            let helper_weight_2 = helper_weight_1.mul(gamma);
            ext_coeffs = (0..coeffs.len())
                .map(|index| {
                    let mut combined = QM31::from_cm31(CM31::from_m31(coeffs[index]))
                        .add(helper_weight_1.mul(helper_coeffs_1[index]));
                    if let Some(helper_2) = &helper_coeffs_2 {
                        combined = combined.add(helper_weight_2.mul(helper_2[index]));
                    }
                    combined
                })
                .collect();
            fold_ext_values = Some(
                (0..layer0_values.len())
                    .map(|index| {
                        let mut combined = QM31::from_cm31(layer0_values[index])
                            .add(helper_weight_1.mul(helper_values_1[index]));
                        if let Some(helper_2) = &helper_values_2 {
                            combined = combined.add(helper_weight_2.mul(helper_2[index]));
                        }
                        combined
                    })
                    .collect(),
            );
            relation_weights = WeightAccumulator::from_claim(profile.log_rows, claim);
            debug_assert_eq!(claim.is_some(), helper_claim_1.is_some());
            debug_assert_eq!(
                helper_coeffs_2.is_some() && claim.is_some(),
                helper_claim_2.is_some()
            );
            second_phase_leaf_bytes = Some(helper_leaves);
            second_phase_tree = Some(helper_tree);
        }

        let mut round_ood_values = Vec::with_capacity(header.ood_samples_per_round());
        let mut early_alpha = None;
        for sample in 0..header.ood_samples_per_round() {
            let ood_point = transcript
                .challenge_ood_qm31()
                .expect("prover OOD sampler exhausted (<2^-186)");
            let mut ood_value = if layer == 0 && !second_phase {
                evaluate_m31_coefficients(coeffs, ood_point)
            } else {
                evaluate_qm31_coefficients(&ext_coeffs, ood_point)
            };
            if sample == 0
                && matches!(ood_behavior, OodBehavior::LieAt(lying_layer) if lying_layer == layer)
            {
                ood_value = ood_value.add(QM31::ONE);
            }
            let mut ood_bytes = [0u8; 16];
            ood_value.write_le_bytes(&mut ood_bytes);
            round_ood_values.push(ood_bytes);

            // The adversarial-order variants deliberately derive alpha
            // after the selected beta and before its y/mu absorption.
            let misorder_this_sample = (sample == 0
                && matches!(ood_behavior, OodBehavior::AbsorbAfterAlpha))
                || (sample == 1 && matches!(ood_behavior, OodBehavior::SecondAbsorbAfterAlpha));
            if misorder_this_sample {
                debug_assert!(early_alpha.is_none());
                early_alpha = Some(
                    transcript
                        .challenge_qm31()
                        .expect("prover transcript sampler exhausted (2^-248 per limb)"),
                );
            }
            transcript.absorb(label::OOD_VALUE, &ood_bytes);

            let mix = transcript
                .challenge_qm31()
                .expect("prover claim-mix sampler exhausted (2^-248 per limb)");
            relation_weights.add_geometric(mix, ood_point);
        }
        ood_values.push(round_ood_values);

        let sumcheck = if layer == 0 && !second_phase {
            polynomial_for_base(coeffs, &relation_weights)
        } else {
            polynomial_for_extension(&ext_coeffs, &relation_weights)
        };
        let mut sumcheck_bytes = [0u8; SUMCHECK_BYTES];
        for (index, coefficient) in sumcheck.iter().enumerate() {
            coefficient.write_le_bytes(&mut sumcheck_bytes[index * 16..index * 16 + 16]);
        }
        transcript.absorb(label::SUMCHECK_POLY, &sumcheck_bytes);
        sumcheck_polynomials.push(sumcheck_bytes);

        let alpha = early_alpha.unwrap_or_else(|| {
            transcript
                .challenge_qm31()
                .expect("prover transcript sampler exhausted (2^-248 per limb)")
        });
        relation_weights.fold(alpha);

        // fold coefficients: two half-folds with alpha then alpha^2
        if layer == 0 && !second_phase {
            let step1: Vec<QM31> = (0..coeffs.len() / 2)
                .map(|j| {
                    QM31::from_cm31(CM31::from_m31(coeffs[2 * j]))
                        .add(alpha.mul_cm31(CM31::from_m31(coeffs[2 * j + 1])))
                })
                .collect();
            let alpha2 = alpha.mul(alpha);
            ext_coeffs = (0..step1.len() / 2)
                .map(|j| step1[2 * j].add(alpha2.mul(step1[2 * j + 1])))
                .collect();
        } else {
            let step1: Vec<QM31> = (0..ext_coeffs.len() / 2)
                .map(|j| ext_coeffs[2 * j].add(alpha.mul(ext_coeffs[2 * j + 1])))
                .collect();
            let alpha2 = alpha.mul(alpha);
            ext_coeffs = (0..step1.len() / 2)
                .map(|j| step1[2 * j].add(alpha2.mul(step1[2 * j + 1])))
                .collect();
        }

        // carried payload (per fiber): the two intra-round folded values
        let mut carried = Vec::new();
        if options.fold_payload == FoldPayload::ProofCarriedRoundLocal {
            carried = compute_carried(
                &geom,
                &fold_base_values,
                &fold_ext_values,
                alpha,
                fiber_count,
            );
        }

        layers.push(LayerData {
            leaf_bytes,
            tree,
            second_phase_leaf_bytes,
            second_phase_tree,
            carried,
        });
    }

    assert_eq!(ext_coeffs.len(), profile.final_poly_len() as usize);
    let mut final_poly_bytes = vec![0u8; ext_coeffs.len() * 16];
    for (k, c) in ext_coeffs.iter().enumerate() {
        c.write_le_bytes(&mut final_poly_bytes[k * 16..k * 16 + 16]);
    }
    transcript.absorb(label::FINAL_POLY, &final_poly_bytes);

    // ---- grinding ----
    let nonce = find_grinding_nonce(&transcript, profile.grinding_bits);
    transcript.absorb(label::GRIND_NONCE, &nonce.to_le_bytes());

    // ---- query phase ----
    let queries = transcript.challenge_queries(query_count, geom0.fiber_count);

    let mut proof = Vec::new();
    proof.extend_from_slice(&header_bytes);
    for (layer, ((root, round_ood_values), sumcheck)) in roots
        .iter()
        .zip(&ood_values)
        .zip(&sumcheck_polynomials)
        .enumerate()
    {
        proof.extend_from_slice(root);
        if layer == 0 && second_phase {
            proof.extend_from_slice(second_phase_root.as_ref().unwrap());
            debug_assert_eq!(
                second_phase_claim_bytes.len(),
                if claim.is_some() {
                    header.second_phase_claim_count()
                } else {
                    0
                }
            );
            for bytes in &second_phase_claim_bytes {
                proof.extend_from_slice(bytes);
            }
        }
        for ood_value in round_ood_values {
            proof.extend_from_slice(ood_value);
        }
        proof.extend_from_slice(sumcheck);
    }
    proof.extend_from_slice(&final_poly_bytes);
    proof.extend_from_slice(&nonce.to_le_bytes());

    let mut index: Vec<u32> = queries;
    for layer in 0..num_rounds {
        let geom = layer_geometry(profile, layer);
        let fiber_mask = geom.fiber_count - 1;
        let fiber_index: Vec<u32> = index.iter().map(|i| i & fiber_mask).collect();
        let mut unique = fiber_index.clone();
        unique.sort_unstable();
        unique.dedup();

        let data = &layers[layer as usize];
        proof.extend_from_slice(&(unique.len() as u16).to_le_bytes());
        for &f in &unique {
            proof.extend_from_slice(&data.leaf_bytes[f as usize]);
        }
        if let Some(helper_leaves) = &data.second_phase_leaf_bytes {
            for &f in &unique {
                proof.extend_from_slice(&helper_leaves[f as usize]);
            }
        }
        if options.fold_payload == FoldPayload::ProofCarriedRoundLocal {
            for &f in &unique {
                let (g1, g2) = data.carried[f as usize];
                let mut bytes = [0u8; 32];
                g1.write_le_bytes(&mut bytes[0..16]);
                g2.write_le_bytes(&mut bytes[16..32]);
                proof.extend_from_slice(&bytes);
            }
        }
        match options.merkle_mode {
            MerkleMode::SinglePaths => {
                for &f in &unique {
                    for node in data.tree.single_path(f) {
                        proof.extend_from_slice(&node);
                    }
                }
            }
            MerkleMode::MinimalSubtree | MerkleMode::Radix4MinimalSubtree => {
                let nodes = data.tree.minimal_subtree(&unique);
                proof.extend_from_slice(&(nodes.len() as u32).to_le_bytes());
                for node in nodes {
                    proof.extend_from_slice(&node);
                }
            }
        }
        if let Some(helper_tree) = &data.second_phase_tree {
            match options.merkle_mode {
                MerkleMode::SinglePaths => {
                    for &f in &unique {
                        for node in helper_tree.single_path(f) {
                            proof.extend_from_slice(&node);
                        }
                    }
                }
                MerkleMode::MinimalSubtree | MerkleMode::Radix4MinimalSubtree => {
                    let nodes = helper_tree.minimal_subtree(&unique);
                    proof.extend_from_slice(&(nodes.len() as u32).to_le_bytes());
                    for node in nodes {
                        proof.extend_from_slice(&node);
                    }
                }
            }
        }
        index = fiber_index;
    }

    proof
}

/// Evaluate QM31 coefficients over a CM31 coset (component-wise NTT would
/// also work; direct generic NTT keeps it simple).
fn coset_evaluate_qm31(
    coeffs: &[QM31],
    offset: CM31,
    omega: CM31,
    domain_size: usize,
) -> Vec<QM31> {
    let mut values = vec![QM31::ZERO; domain_size];
    let mut scale = CM31::ONE;
    for (j, c) in coeffs.iter().enumerate() {
        values[j] = c.mul_cm31(scale);
        scale = scale.mul(offset);
    }
    // radix-2 NTT over QM31 with CM31 twiddles
    let n = values.len();
    let bits = n.trailing_zeros();
    for i in 0..n {
        let j = ((i as u32).reverse_bits() >> (32 - bits)) as usize;
        if j > i {
            values.swap(i, j);
        }
    }
    let mut len = 2usize;
    while len <= n {
        let w_len = omega.pow((n / len) as u64);
        for start in (0..n).step_by(len) {
            let mut w = CM31::ONE;
            for k in 0..len / 2 {
                let a = values[start + k];
                let b = values[start + k + len / 2].mul_cm31(w);
                values[start + k] = a.add(b);
                values[start + k + len / 2] = a.sub(b);
                w = w.mul(w_len);
            }
        }
        len <<= 1;
    }
    values
}

/// Per-fiber intra-round folded values (g1, g2) for the carried payload.
fn compute_carried(
    geom: &aspis_core::verify::LayerGeometry,
    base_values: &Option<Vec<CM31>>,
    ext_values: &Option<Vec<QM31>>,
    alpha: QM31,
    fiber_count: usize,
) -> Vec<(QM31, QM31)> {
    // batch the denominators exactly like the verifier's raw mode
    let mut denoms = Vec::with_capacity(fiber_count * 2);
    for f in 0..fiber_count {
        let s = domain_point(geom, f as u32);
        denoms.push(s.double());
        denoms.push(s.mul(geom.iota).double());
    }
    let mut invs = vec![CM31::ZERO; denoms.len()];
    cm31_batch_inverse(&denoms, &mut invs);

    let half = aspis_core::field::M31_HALF;
    (0..fiber_count)
        .map(|f| {
            let get = |m: usize| -> QM31 {
                let idx = f + m * fiber_count;
                match (base_values, ext_values) {
                    (Some(v), None) => QM31::from_cm31(v[idx]),
                    (None, Some(v)) => v[idx],
                    _ => unreachable!(),
                }
            };
            let (v0, v1, v2, v3) = (get(0), get(1), get(2), get(3));
            let g1 = v0
                .add(v2)
                .mul_m31(half)
                .add(alpha.mul(v0.sub(v2).mul_cm31(invs[f * 2])));
            let g2 = v1
                .add(v3)
                .mul_m31(half)
                .add(alpha.mul(v1.sub(v3).mul_cm31(invs[f * 2 + 1])));
            (g1, g2)
        })
        .collect()
}

/// Convenience: deterministic test polynomial from a seed.
pub fn seeded_coeffs(log_rows: u32, seed: u64) -> Vec<M31> {
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1);
    (0..1usize << log_rows)
        .map(|_| {
            // xorshift64*
            state ^= state >> 12;
            state ^= state << 25;
            state ^= state >> 27;
            let v = (state.wrapping_mul(0x2545_F491_4F6C_DD1D) >> 33) as u32 & 0x7fff_ffff;
            M31(if v == aspis_core::field::P { 0 } else { v })
        })
        .collect()
}
