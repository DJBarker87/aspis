//! Host-only prover for the Aspis v0 substrate.
//!
//! Commits evaluations of a polynomial (degree < 2^log_rows, M31
//! coefficients) over a coset of a 2^k subgroup of the M31 circle group in
//! CM31, folds it WHIR-style two variables per round to an explicit final
//! polynomial, and packages openings in the envelope `aspis-core` parses.
//!
//! The prover mirrors the verifier's transcript step-for-step; any
//! divergence is caught by the parity tests (10/10 accept on host must equal
//! accept on SBF for identical bytes).

use aspis_core::field::{cm31_batch_inverse, CM31, M31, QM31};
use aspis_core::merkle::{leaf_hash, node_hash};
use aspis_core::params::{FoldPayload, MerkleMode, Profile, FINAL_POLY_LOG_LEN};
use aspis_core::proof::{fiber_value_bytes, Header, HEADER_LEN};
use aspis_core::transcript::{label, Transcript};
use aspis_core::verify::{domain_point, layer_geometry, EvaluationClaim};
use aspis_core::HashFn;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;

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
    if bits <= 20 {
        let mut nonce = 0u64;
        while !transcript.grinding_ok(nonce, bits) {
            nonce += 1;
        }
        return nonce;
    }

    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
        .max(1);
    let found = Arc::new(AtomicBool::new(false));
    let result = Arc::new(AtomicU64::new(0));

    std::thread::scope(|scope| {
        for worker in 0..workers {
            let found = Arc::clone(&found);
            let result = Arc::clone(&result);
            let transcript = transcript.clone();
            scope.spawn(move || {
                let mut nonce = worker as u64;
                let stride = workers as u64;
                while !found.load(Ordering::Relaxed) {
                    if transcript.grinding_ok(nonce, bits) {
                        if !found.swap(true, Ordering::AcqRel) {
                            result.store(nonce, Ordering::Release);
                        }
                        break;
                    }
                    nonce = nonce.wrapping_add(stride);
                }
            });
        }
    });

    result.load(Ordering::Acquire)
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
}

impl FiberTree {
    fn build(hash: HashFn, layer: u8, leaf_bytes: &[Vec<u8>]) -> FiberTree {
        let mut levels = vec![leaf_bytes
            .iter()
            .map(|bytes| leaf_hash(hash, layer, bytes))
            .collect::<Vec<_>>()];
        while levels.last().unwrap().len() > 1 {
            let prev = levels.last().unwrap();
            let mut next = Vec::with_capacity(prev.len() / 2);
            for pair in prev.chunks_exact(2) {
                next.push(node_hash(hash, &pair[0], &pair[1]));
            }
            levels.push(next);
        }
        FiberTree { levels }
    }

    fn root(&self) -> [u8; 32] {
        self.levels.last().unwrap()[0]
    }

    fn single_path(&self, mut index: u32) -> Vec<[u8; 32]> {
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
}

/// One committed layer retained for the opening phase.
struct LayerData {
    /// per-fiber leaf bytes (fiber i = values at {i, i+F, i+2F, i+3F})
    leaf_bytes: Vec<Vec<u8>>,
    tree: FiberTree,
    /// per-fiber carried payload (g1, g2) for proof_carried_round_local
    carried: Vec<(QM31, QM31)>,
}

pub struct ProveOptions {
    pub fold_payload: FoldPayload,
    pub merkle_mode: MerkleMode,
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
    prove_inner(profile, coeffs, statement_digest, None, options, hash, false)
}

/// Produce a claim-carrying proof: the externally supplied (z, v) is absorbed
/// as a public input in the canonical position (after the statement digest,
/// before any root). See `aspis_core::verify::EvaluationClaim` for the
/// binding-only caveat at this revision.
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
        false,
    )
}

/// Adversarial prover for the challenge-order test suite ONLY: absorbs the
/// claim AFTER the commitment roots instead of the canonical position. The
/// verifier (canonical order) must reject its output. Never call this
/// outside tests.
#[doc(hidden)]
pub fn prove_with_misordered_claim_for_tests(
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
        true,
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

#[allow(clippy::too_many_arguments)]
fn prove_inner(
    profile: &Profile,
    coeffs: &[M31],
    statement_digest: &[u8; 32],
    claim: Option<&EvaluationClaim>,
    options: &ProveOptions,
    hash: HashFn,
    misorder_claim: bool,
) -> Vec<u8> {
    assert_eq!(coeffs.len(), 1usize << profile.log_rows);
    let num_rounds = profile.num_rounds();
    let query_count = profile.query_count as usize;

    let header = Header {
        profile_id: profile.id,
        log_rows: profile.log_rows,
        log_blowup: profile.log_blowup,
        query_count: profile.query_count,
        grinding_bits: profile.grinding_bits,
        fold_payload: options.fold_payload as u8,
        merkle_mode: options.merkle_mode as u8,
        num_rounds,
        final_poly_log_len: FINAL_POLY_LOG_LEN,
        claim_flag: claim.is_some() as u8,
    };
    let mut header_bytes = [0u8; HEADER_LEN];
    header.write(&mut header_bytes);

    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, &header_bytes);
    transcript.absorb(label::STATEMENT, statement_digest);
    if let (Some(claim), false) = (claim, misorder_claim) {
        transcript.absorb(label::CLAIM, &claim.to_bytes());
    }

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
    let mut alphas: Vec<QM31> = Vec::new();

    for layer in 0..num_rounds {
        let geom = layer_geometry(profile, layer);
        let fiber_count = geom.fiber_count as usize;
        let value_bytes = fiber_value_bytes(layer);

        let (base_values, ext_values): (Option<Vec<CM31>>, Option<Vec<QM31>>) = if layer == 0 {
            (Some(layer0_values.clone()), None)
        } else {
            // evaluate current ext_coeffs over this layer's domain
            let values = coset_evaluate_qm31(
                &ext_coeffs,
                geom.offset,
                geom.omega,
                geom.domain_size as usize,
            );
            (None, Some(values))
        };

        let mut leaf_bytes = Vec::with_capacity(fiber_count);
        for f in 0..fiber_count {
            let mut bytes = vec![0u8; value_bytes];
            for m in 0..4 {
                let idx = f + m * fiber_count;
                match (&base_values, &ext_values) {
                    (Some(v), None) => v[idx].write_le_bytes(&mut bytes[m * 8..m * 8 + 8]),
                    (None, Some(v)) => v[idx].write_le_bytes(&mut bytes[m * 16..m * 16 + 16]),
                    _ => unreachable!(),
                }
            }
            leaf_bytes.push(bytes);
        }
        let tree = FiberTree::build(hash, layer as u8, &leaf_bytes);
        let root = tree.root();
        transcript.absorb(label::ROOT, &root);
        roots.push(root);
        let alpha = transcript
            .challenge_qm31()
            .expect("prover transcript sampler exhausted (2^-248 per limb)");
        alphas.push(alpha);

        // fold coefficients: two half-folds with alpha then alpha^2
        if layer == 0 {
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
            carried = compute_carried(&geom, &base_values, &ext_values, alpha, fiber_count);
        }

        layers.push(LayerData {
            leaf_bytes,
            tree,
            carried,
        });
    }

    assert_eq!(ext_coeffs.len(), profile.final_poly_len() as usize);
    let mut final_poly_bytes = vec![0u8; ext_coeffs.len() * 16];
    for (k, c) in ext_coeffs.iter().enumerate() {
        c.write_le_bytes(&mut final_poly_bytes[k * 16..k * 16 + 16]);
    }
    if let (Some(claim), true) = (claim, misorder_claim) {
        // adversarial order for the challenge-order test suite: claim lands
        // after the roots instead of the canonical public-input position
        transcript.absorb(label::CLAIM, &claim.to_bytes());
    }
    transcript.absorb(label::FINAL_POLY, &final_poly_bytes);

    // ---- grinding ----
    let nonce = find_grinding_nonce(&transcript, profile.grinding_bits);
    transcript.absorb(label::GRIND_NONCE, &nonce.to_le_bytes());

    // ---- query phase ----
    let queries = transcript.challenge_queries(query_count, geom0.fiber_count);

    let mut proof = Vec::new();
    proof.extend_from_slice(&header_bytes);
    for root in &roots {
        proof.extend_from_slice(root);
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
            MerkleMode::MinimalSubtree => {
                let nodes = data.tree.minimal_subtree(&unique);
                proof.extend_from_slice(&(nodes.len() as u32).to_le_bytes());
                for node in nodes {
                    proof.extend_from_slice(&node);
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
