//! The on-chain verifier logic (also the host reference — byte-exact shared
//! code path).
//!
//! What this proves, stated precisely (v0, pre-Stage-1): transcript-bound
//! local fold consistency of a committed evaluation table down to an explicit
//! final polynomial, with grinding, against a bound statement digest. It is
//! NOT yet the full WHIR paper path: no out-of-domain samples, no
//! sumcheck/fold interleaving, no externally supplied evaluation claim. The
//! soundness delta is characterized and closed in Stage 1.

use alloc::vec;
use alloc::vec::Vec;

use crate::field::{cm31_batch_inverse, CM31, M31_HALF, QM31};
use crate::merkle::{leaf_hash, verify_minimal_subtree, verify_single_path};
use crate::params::{
    profile_by_id, FoldPayload, MerkleMode, Profile, CIRCLE_GEN, CIRCLE_LOG_ORDER,
    FINAL_POLY_LOG_LEN, FOLD_VARS,
};
use crate::proof::{fiber_value_bytes, Cursor, Header, HEADER_LEN};
use crate::transcript::{label, HashFn, Transcript};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum VerifyError {
    BadHeader,
    UnknownProfile,
    HeaderProfileMismatch,
    BadLength,
    NonCanonicalValue,
    GrindingFailed,
    UniqueCountMismatch { layer: u8 },
    MerkleMismatch { layer: u8 },
    SlotMismatch { layer: u8 },
    CarriedFoldMismatch { layer: u8 },
    FinalPolyMismatch,
    TrailingBytes,
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
        }
    }
}

/// Per-layer domain geometry, derived from the circle group generator.
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

/// Sorted unique values of `indices`.
fn unique_sorted(indices: &[u32]) -> Vec<u32> {
    let mut v: Vec<u32> = indices.to_vec();
    v.sort_unstable();
    v.dedup();
    v
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
            let g1 = QM31::from_cm31(sum02.mul_m31(M31_HALF))
                .add(alpha.mul_cm31(dif02.mul(inv_2s)));
            let g2 = QM31::from_cm31(sum13.mul_m31(M31_HALF))
                .add(alpha.mul_cm31(dif13.mul(inv_2is)));
            (g1, g2)
        }
        Fiber::Ext(v) => {
            let sum02 = v[0].add(v[2]);
            let dif02 = v[0].sub(v[2]);
            let sum13 = v[1].add(v[3]);
            let dif13 = v[1].sub(v[3]);
            let g1 = sum02.mul_m31(M31_HALF).add(alpha.mul(dif02.mul_cm31(inv_2s)));
            let g2 = sum13.mul_m31(M31_HALF).add(alpha.mul(dif13.mul_cm31(inv_2is)));
            (g1, g2)
        }
    };
    let sum = g1.add(g2);
    let dif = g1.sub(g2);
    sum.mul_m31(M31_HALF)
        .add(alpha2.mul(dif.mul_cm31(inv_2s2)))
}

/// Division-free carried-payload checks for one fiber (proof_carried_round_local).
/// Returns (ok_of_intra_round_checks, deferred) where `deferred` carries what
/// check3 needs once the next layer's value is known:
///   h * 2s^2 == s^2*(g1+g2) + alpha^2*(g1-g2)
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
    let s2 = s.mul(s);
    let ok = match fiber {
        Fiber::Base(v) => {
            let c1 = g1.mul_cm31(two_s)
                == QM31::from_cm31(v[0].add(v[2]).mul(s)).add(alpha.mul_cm31(v[0].sub(v[2])));
            let c2 = g2.mul_cm31(two_is)
                == QM31::from_cm31(v[1].add(v[3]).mul(is)).add(alpha.mul_cm31(v[1].sub(v[3])));
            c1 && c2
        }
        Fiber::Ext(v) => {
            let c1 = g1.mul_cm31(two_s)
                == v[0].add(v[2]).mul_cm31(s).add(alpha.mul(v[0].sub(v[2])));
            let c2 = g2.mul_cm31(two_is)
                == v[1].add(v[3]).mul_cm31(is).add(alpha.mul(v[1].sub(v[3])));
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

/// Verify a proof against a statement digest. `hash` is the SHA-256 backend
/// (syscall on SBF, sha2 on host).
pub fn verify(proof: &[u8], statement_digest: &[u8; 32], hash: HashFn) -> Result<(), VerifyError> {
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
    let fold_payload =
        FoldPayload::from_u8(header.fold_payload).ok_or(VerifyError::BadHeader)?;
    let merkle_mode = MerkleMode::from_u8(header.merkle_mode).ok_or(VerifyError::BadHeader)?;

    let num_rounds = profile.num_rounds();
    let query_count = profile.query_count as usize;

    let mut cursor = Cursor::new(proof);
    let header_bytes = cursor.take(HEADER_LEN).ok_or(VerifyError::BadLength)?;

    // ---- transcript phase ----
    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, header_bytes);
    transcript.absorb(label::STATEMENT, statement_digest);

    let mut roots = Vec::with_capacity(num_rounds as usize);
    let mut alphas = Vec::with_capacity(num_rounds as usize);
    for _ in 0..num_rounds {
        let root = cursor.take_hash().ok_or(VerifyError::BadLength)?;
        transcript.absorb(label::ROOT, &root);
        roots.push(root);
        alphas.push(transcript.challenge_qm31());
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

    let nonce = cursor.take_u64().ok_or(VerifyError::BadLength)?;
    if !transcript.grinding_ok(nonce, profile.grinding_bits) {
        return Err(VerifyError::GrindingFailed);
    }
    transcript.absorb(label::GRIND_NONCE, &nonce.to_le_bytes());

    let geom0 = layer_geometry(profile, 0);
    let queries = transcript.challenge_queries(query_count, geom0.fiber_count);

    // ---- opening + fold phase ----
    // per-query running domain index i_r (i_0 = sampled fiber index)
    let mut index: Vec<u32> = queries.clone();
    // raw mode: expected incoming value per query; carried mode: deferred check3
    let mut expected: Vec<QM31> = vec![QM31::ZERO; query_count];
    let mut deferred: Vec<Option<CarriedDeferred>> = Vec::new();
    if fold_payload == FoldPayload::ProofCarriedRoundLocal {
        deferred = (0..query_count).map(|_| None).collect();
    }

    for layer in 0..num_rounds {
        let geom = layer_geometry(profile, layer);
        let alpha = alphas[layer as usize];
        let alpha2 = alpha.mul(alpha);
        let fiber_mask = geom.fiber_count - 1;

        // geometry per query
        let fiber_index: Vec<u32> = index.iter().map(|i| i & fiber_mask).collect();
        let slot: Vec<u32> = index.iter().map(|i| i >> geom.log_fiber_count).collect();
        let unique = unique_sorted(&fiber_index);

        let unique_count = cursor.take_u16().ok_or(VerifyError::BadLength)? as usize;
        if unique_count != unique.len() {
            return Err(VerifyError::UniqueCountMismatch { layer: layer as u8 });
        }
        let value_bytes = fiber_value_bytes(layer);
        let values_section = cursor
            .take(unique_count * value_bytes)
            .ok_or(VerifyError::BadLength)?;
        let mut fibers = Vec::with_capacity(unique_count);
        for k in 0..unique_count {
            fibers.push(parse_fiber(
                &values_section[k * value_bytes..(k + 1) * value_bytes],
                layer,
            )?);
        }

        let mut carried: Vec<(QM31, QM31)> = Vec::new();
        if fold_payload == FoldPayload::ProofCarriedRoundLocal {
            let carried_section = cursor
                .take(unique_count * 32)
                .ok_or(VerifyError::BadLength)?;
            for chunk in carried_section.chunks_exact(32) {
                let g1 = QM31::from_le_bytes(&chunk[0..16]).ok_or(VerifyError::NonCanonicalValue)?;
                let g2 =
                    QM31::from_le_bytes(&chunk[16..32]).ok_or(VerifyError::NonCanonicalValue)?;
                carried.push((g1, g2));
            }
        }

        // Merkle verification over the unique fiber leaves.
        let root = &roots[layer as usize];
        let depth = geom.log_fiber_count;
        match merkle_mode {
            MerkleMode::SinglePaths => {
                for (k, &fidx) in unique.iter().enumerate() {
                    let leaf = leaf_hash(
                        hash,
                        layer as u8,
                        &values_section[k * value_bytes..(k + 1) * value_bytes],
                    );
                    let path_bytes = cursor
                        .take(depth as usize * 32)
                        .ok_or(VerifyError::BadLength)?;
                    let path: Vec<[u8; 32]> = path_bytes
                        .chunks_exact(32)
                        .map(|c| <[u8; 32]>::try_from(c).unwrap())
                        .collect();
                    if !verify_single_path(hash, root, depth, fidx, leaf, &path) {
                        return Err(VerifyError::MerkleMismatch { layer: layer as u8 });
                    }
                }
            }
            MerkleMode::MinimalSubtree => {
                let node_count = cursor.take_u32().ok_or(VerifyError::BadLength)? as usize;
                let node_bytes = cursor.take(node_count * 32).ok_or(VerifyError::BadLength)?;
                let nodes: Vec<[u8; 32]> = node_bytes
                    .chunks_exact(32)
                    .map(|c| <[u8; 32]>::try_from(c).unwrap())
                    .collect();
                let entries: Vec<(u32, [u8; 32])> = unique
                    .iter()
                    .enumerate()
                    .map(|(k, &fidx)| {
                        (
                            fidx,
                            leaf_hash(
                                hash,
                                layer as u8,
                                &values_section[k * value_bytes..(k + 1) * value_bytes],
                            ),
                        )
                    })
                    .collect();
                if !verify_minimal_subtree(hash, root, depth, &entries, &nodes) {
                    return Err(VerifyError::MerkleMismatch { layer: layer as u8 });
                }
            }
        }

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
        let s_values: Vec<CM31> = unique
            .iter()
            .map(|&fidx| domain_point(&geom, fidx))
            .collect();
        let mut folded = vec![QM31::ZERO; unique.len()];
        match fold_payload {
            FoldPayload::RawFibers => {
                // gather denominators for the whole round, invert once
                let mut denoms = Vec::with_capacity(unique.len() * 3);
                for &s in &s_values {
                    denoms.push(s.double());
                    denoms.push(s.mul(geom.iota).double());
                    denoms.push(s.mul(s).double());
                }
                let mut invs = vec![CM31::ZERO; denoms.len()];
                cm31_batch_inverse(&denoms, &mut invs);
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

        index = fiber_index;
    }

    // ---- final polynomial check ----
    let final_geom = layer_geometry(profile, num_rounds);
    for q in 0..query_count {
        let x = domain_point(&final_geom, index[q]);
        // Horner over QM31 coefficients at a CM31 point (late lift)
        let mut acc = *final_poly.last().unwrap();
        for c in final_poly.iter().rev().skip(1) {
            acc = acc.mul_cm31(x).add(*c);
        }
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
    Ok(())
}
