//! Frozen Stage 0 profiles and protocol constants.
//!
//! Soundness labels are deliberately `heuristic` for every Stage 0 profile:
//! the numeric per-round soundness budget is a Stage 1 deliverable
//! (`docs/aspis-soundness-note.md`). Nothing here may be quoted as
//! `proven` or `conjectured` until that note exists.

use crate::field::CM31;
use crate::field::M31;

/// The M31 circle group: unit-norm elements of CM31, cyclic of order 2^31.
/// Generator (order exactly 2^31, cross-checked against the stwo constant);
/// its order is asserted by unit test `circle_generator_order`.
pub const CIRCLE_GEN: CM31 = CM31 {
    a: M31(2),
    b: M31(1_268_011_823),
};

/// log2 of the circle group order.
pub const CIRCLE_LOG_ORDER: u32 = 31;

/// Every round folds 2 variables (arity 4), matching the design's
/// `fold_vars = 2` configuration.
pub const FOLD_VARS: u32 = 2;
pub const FOLD_ARITY: u32 = 1 << FOLD_VARS;

/// Folding stops when 2^FINAL_POLY_LOG_LEN coefficients remain; they are
/// shipped in the clear.
pub const FINAL_POLY_LOG_LEN: u32 = 2;

/// Fold payload packaging carried by the proof.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FoldPayload {
    /// Proof carries only the committed raw fiber values; the verifier
    /// recomputes local folds using batched denominator inversions
    /// (`round_batch_inversion`). "Raw" describes payload packaging, not
    /// the field basis: in the current custom PCS, layer-zero wire symbols
    /// are CM31 coset evaluations of M31 coefficient vectors.
    RawFibers = 0,
    /// Proof additionally carries the two intra-round folded values per query
    /// per round; the verifier checks cross-multiplied fold relations with
    /// zero inversions. Bytes up, CU down: the Stage 0 measurement decides
    /// whether this stays in the frozen profile (design decision item 4).
    ProofCarriedRoundLocal = 1,
}

impl FoldPayload {
    pub fn from_u8(v: u8) -> Option<FoldPayload> {
        match v {
            0 => Some(FoldPayload::RawFibers),
            1 => Some(FoldPayload::ProofCarriedRoundLocal),
            _ => None,
        }
    }
}

/// Merkle opening packaging.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MerkleMode {
    /// One independent authentication path per query per layer.
    SinglePaths = 0,
    /// Deduplicated multiproof: shared subtree nodes shipped once
    /// (`minimal_subtree`).
    MinimalSubtree = 1,
    /// Domain-separated radix-4 tree with a deduplicated minimal-subtree
    /// opening. Two binary levels become one four-child SHA-256 compression.
    Radix4MinimalSubtree = 2,
}

impl MerkleMode {
    pub fn from_u8(v: u8) -> Option<MerkleMode> {
        match v {
            0 => Some(MerkleMode::SinglePaths),
            1 => Some(MerkleMode::MinimalSubtree),
            2 => Some(MerkleMode::Radix4MinimalSubtree),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Profile {
    pub id: u8,
    pub name: &'static str,
    /// log2 of the committed polynomial's coefficient count.
    pub log_rows: u32,
    /// log2 of the rate inverse (blowup).
    pub log_blowup: u32,
    pub query_count: u16,
    pub grinding_bits: u8,
    /// Honesty label carried into every artifact that quotes this profile.
    pub soundness_label: &'static str,
}

impl Profile {
    /// Evaluation domain size of the committed layer.
    pub const fn domain_size(&self) -> u32 {
        1 << (self.log_rows + self.log_blowup)
    }

    /// Number of committed layers (rounds). Folding runs until
    /// FINAL_POLY_LOG_LEN coefficients remain; log_rows must satisfy
    /// (log_rows - FINAL_POLY_LOG_LEN) % FOLD_VARS == 0.
    pub const fn num_rounds(&self) -> u32 {
        (self.log_rows - FINAL_POLY_LOG_LEN) / FOLD_VARS
    }

    pub const fn final_poly_len(&self) -> u32 {
        1 << FINAL_POLY_LOG_LEN
    }

    /// Domain size at layer r (r in 0..=num_rounds).
    pub const fn layer_domain_size(&self, r: u32) -> u32 {
        self.domain_size() >> (FOLD_VARS * r)
    }
}

/// Stage 0 frozen profiles.
///
/// Query/grinding shapes mirror the capacity-vs-Johnson asymmetry the design
/// doc requires to be stated wherever CU numbers are quoted: the capacity
/// profile assumes ~log_blowup bits per query, the Johnson profile roughly
/// half that. Both are HEURISTIC placeholders until the Stage 1 soundness
/// note derives real budgets.
pub const PROFILE_CAPACITY: Profile = Profile {
    id: 0,
    name: "capacity_lr12_q40_g16",
    log_rows: 12,
    log_blowup: 2,
    query_count: 40,
    grinding_bits: 16,
    soundness_label: "heuristic (capacity-conjecture shaped; Stage 1 budget pending)",
};

pub const PROFILE_JOHNSON: Profile = Profile {
    id: 1,
    name: "johnson_lr12_q80_g16",
    log_rows: 12,
    log_blowup: 2,
    query_count: 80,
    grinding_bits: 16,
    soundness_label: "heuristic (Johnson shaped; Stage 1 budget pending)",
};

/// Statement-sized witness profile from the design's CU table (log_rows=14).
pub const PROFILE_CAPACITY_LR14: Profile = Profile {
    id: 2,
    name: "capacity_lr14_q40_g16",
    log_rows: 14,
    log_blowup: 2,
    query_count: 40,
    grinding_bits: 16,
    soundness_label: "heuristic (capacity-conjecture shaped; Stage 1 budget pending)",
};

/// Diagnostic profiles for the g16 -> g32 grinding/query trade. These are not
/// frozen Stage 0 profiles; they exist to measure whether prover-side grinding
/// can buy back enough verifier queries to recover Stage 1 headroom.
pub const PROFILE_CAPACITY_G32_Q36: Profile = Profile {
    id: 3,
    name: "capacity_lr12_q36_g32",
    log_rows: 12,
    log_blowup: 2,
    query_count: 36,
    grinding_bits: 32,
    soundness_label: "heuristic diagnostic (capacity-conjecture shaped; g32 query trade)",
};

pub const PROFILE_CAPACITY_G32_Q32: Profile = Profile {
    id: 4,
    name: "capacity_lr12_q32_g32",
    log_rows: 12,
    log_blowup: 2,
    query_count: 32,
    grinding_bits: 32,
    soundness_label: "heuristic diagnostic (capacity-conjecture shaped; g32 query trade)",
};

/// Lower-row diagnostics for the wide-row statement layout decision. These
/// are Stage 0 measurement targets, not frozen soundness profiles.
pub const PROFILE_CAPACITY_LR10_Q40_G16: Profile = Profile {
    id: 5,
    name: "capacity_lr10_q40_g16",
    log_rows: 10,
    log_blowup: 2,
    query_count: 40,
    grinding_bits: 16,
    soundness_label: "heuristic diagnostic (lower-row layout target; Stage 1 budget pending)",
};

pub const PROFILE_CAPACITY_LR10_Q36_G16: Profile = Profile {
    id: 6,
    name: "capacity_lr10_q36_g16",
    log_rows: 10,
    log_blowup: 2,
    query_count: 36,
    grinding_bits: 16,
    soundness_label: "heuristic diagnostic (lower-row layout target; q36 verifier cost)",
};

pub const PROFILE_CAPACITY_LR10_Q32_G16: Profile = Profile {
    id: 7,
    name: "capacity_lr10_q32_g16",
    log_rows: 10,
    log_blowup: 2,
    query_count: 32,
    grinding_bits: 16,
    soundness_label: "heuristic diagnostic (lower-row layout target; q32 verifier cost)",
};

/// The literal ruled Stage 1 schedule (soundness-note §4): q36 with g32
/// grinding at the lr10 layout target. Exists so the §4 "measured" column can
/// be a measurement of THIS profile rather than a g16 verifier-cost proxy.
pub const PROFILE_CAPACITY_LR10_Q36_G32: Profile = Profile {
    id: 8,
    name: "capacity_lr10_q36_g32",
    log_rows: 10,
    log_blowup: 2,
    query_count: 36,
    grinding_bits: 32,
    soundness_label:
        "conjectured (capacity); external/OOD relations and Stage 1 C2 plumbing enforced",
};

/// Query/grinding-trade diagnostic (shrink hunt, `2026-07-10`): q34 at g16
/// for multi-seed verifier-cost measurement of the q36 -> q34 step. The
/// sound production pairing holds 2q + g = 104 (q34/g36); g16 here is the
/// affordable measurement proxy, exactly as in the variance study.
pub const PROFILE_CAPACITY_LR10_Q34_G16: Profile = Profile {
    id: 9,
    name: "capacity_lr10_q34_g16",
    log_rows: 10,
    log_blowup: 2,
    query_count: 34,
    grinding_bits: 16,
    soundness_label:
        "heuristic diagnostic (query/grinding trade measurement; production pairing is q34/g36)",
};

/// Literal Johnson-query diagnostic for the M31-leaf candidate. At the
/// pinned rho=1/4, eta=0.025 radius, q74 plus g32 is the first integer query
/// count whose query-round work factor exceeds 100 bits. This profile is a
/// measurement target, not a claim that every other soundness-ledger term
/// reaches 100 bits.
pub const PROFILE_JOHNSON_LR10_Q74_G32: Profile = Profile {
    id: 10,
    name: "johnson_lr10_q74_g32",
    log_rows: 10,
    log_blowup: 2,
    query_count: 74,
    grinding_bits: 32,
    soundness_label: "proven Johnson query-radius target; full-system ledger still required",
};

/// Natural radix-4-compatible low-rate Johnson diagnostic. With rho=1/16
/// and eta=sqrt(rho)/20=0.0125, q36/g32 gives 101.466 query-round bits while
/// preserving the four-fold, four-coefficient terminal shape.
pub const PROFILE_JOHNSON_LR10_B4_Q36_G32: Profile = Profile {
    id: 11,
    name: "johnson_lr10_b4_q36_g32",
    log_rows: 10,
    log_blowup: 4,
    query_count: 36,
    grinding_bits: 32,
    soundness_label:
        "proven Johnson query-radius target at rate 1/16; full-system ledger still required",
};

/// Hardened low-rate Johnson profile. The four fold-challenge work factors
/// are protocol constants carried by `RATE16_HARDENED_CANDIDATE_SHAPE`; this
/// header field records the independent final query-grinding difficulty.
pub const PROFILE_JOHNSON_LR10_B4_Q36_G36_POW: Profile = Profile {
    id: 12,
    name: "johnson_lr10_b4_q36_g36_foldpow",
    log_rows: 10,
    log_blowup: 4,
    query_count: 36,
    grinding_bits: 36,
    soundness_label:
        "proven Johnson parameter candidate with per-fold work; full transport ledger required",
};

/// Production payment profile. It shares the hardened rate-1/16 PCS
/// parameters but has a distinct id so an external-point diagnostic proof
/// can never be replayed as a payment-linked proof.
pub const PROFILE_PAYMENT_LR10_B4_Q36_G36_POW: Profile = Profile {
    id: 13,
    name: "payment_lr10_b4_q36_g36_foldpow",
    log_rows: 10,
    log_blowup: 4,
    query_count: 36,
    grinding_bits: 36,
    soundness_label:
        "payment-linked rate-1/16 Johnson candidate with per-fold work; full transport and hiding required",
};

pub const PROFILES: &[Profile] = &[
    PROFILE_CAPACITY,
    PROFILE_JOHNSON,
    PROFILE_CAPACITY_LR14,
    PROFILE_CAPACITY_G32_Q36,
    PROFILE_CAPACITY_G32_Q32,
    PROFILE_CAPACITY_LR10_Q40_G16,
    PROFILE_CAPACITY_LR10_Q36_G16,
    PROFILE_CAPACITY_LR10_Q32_G16,
    PROFILE_CAPACITY_LR10_Q36_G32,
    PROFILE_CAPACITY_LR10_Q34_G16,
    PROFILE_JOHNSON_LR10_Q74_G32,
    PROFILE_JOHNSON_LR10_B4_Q36_G32,
    PROFILE_JOHNSON_LR10_B4_Q36_G36_POW,
    PROFILE_PAYMENT_LR10_B4_Q36_G36_POW,
];

pub fn profile_by_id(id: u8) -> Option<&'static Profile> {
    PROFILES.iter().find(|p| p.id == id)
}
