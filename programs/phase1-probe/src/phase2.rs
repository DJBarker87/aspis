use borsh::{BorshDeserialize, BorshSerialize};
use solana_program::hash::hashv;

pub const M31_MODULUS: u32 = 0x7fff_ffff;
const M31_MODULUS_U64: u64 = M31_MODULUS as u64;
const M31_BARRETT_MU: u64 = (1_u64 << 33) + 4;
const M31_MONT_N_INV: u32 = 0x8000_0001;
const PHASE2_PROOF_MAGIC: [u8; 4] = *b"P2X1";
const PHASE2_PROOF_VERSION: u16 = 1;
const PHASE2_WHIR_QUERY_MAGIC: [u8; 4] = *b"P2W1";
const PHASE2_WHIR_QUERY_VERSION: u16 = 1;
const PHASE2_WHIR_TRANSCRIPT_MAGIC: [u8; 4] = *b"P2T1";
const PHASE2_WHIR_TRANSCRIPT_VERSION: u16 = 2;
const PHASE2_WHIR_MERKLE_PAYLOAD_MAGIC: [u8; 4] = *b"MPF1";
const PHASE2_WHIR_MERKLE_PAYLOAD_VERSION: u16 = 1;
const RAW_QUERY_RECORD_WORDS: usize = 10;
const LOCAL_QUERY_RECORD_WORDS: usize = 10;
pub const PHASE2_WHIR_MAX_ROUNDS: usize = 4;
pub const PHASE2_WHIR_MAX_OPENING_TERMS: usize = 4;
pub const PHASE2_WHIR_ROW_BUCKETS: usize = 8;
pub const PHASE2_WHIR_MAX_OOD_SAMPLES: usize = 4;
pub const PHASE2_WHIR_MAX_SUMCHECK_ROUNDS: usize = 8;
pub const PHASE2_WHIR_MAX_FINAL_COEFFS: usize = 64;
const PHASE2_WHIR_SELECTOR_TERMS: usize = 2;
const PHASE2_WHIR_FOLD_VALUES: usize = 8;
const PHASE2_WHIR_NUMERATOR_COEFFS: usize = 4;
const PHASE2_WHIR_QUERY_PRECOMPUTED_WORDS: usize = 7;
const PHASE2_WHIR_ROUND_PLAN_WORDS: usize = 5;
const PHASE2_WHIR_TRANSCRIPT_ROUND_PLAN_WORDS: usize = 8;
const PHASE2_WHIR_QUERY_RECORD_WORDS: usize = 2
    + (PHASE2_WHIR_MAX_OPENING_TERMS * 2)
    + (PHASE2_WHIR_SELECTOR_TERMS * 2)
    + PHASE2_WHIR_FOLD_VALUES
    + PHASE2_WHIR_NUMERATOR_COEFFS
    + PHASE2_WHIR_SELECTOR_TERMS;
const PHASE2_WHIR_SUMCHECK_RECORD_WORDS: usize = 4;
const PHASE2_WHIR_FINAL_QUERY_RECORD_WORDS: usize = 2;
const PHASE2_WHIR_DEFERRED_EVAL_WORDS: usize = 4;
const PHASE2_WHIR_MERKLE_NODE_BYTES: usize = 32;
const TRANSCRIPT_DIGEST_BYTES: usize = 32;

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub enum ArithmeticKernelId {
    ReferenceCanonical,
    DirectM31,
    DirectM31Lazy,
    Montgomery,
    Barrett,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub enum ReductionMode {
    Canonical,
    DirectM31,
    Montgomery,
    Barrett,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub enum LazyReductionMode {
    None,
    Batch4,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub enum ExtensionKernelId {
    Schoolbook,
    Karatsuba,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub enum LiftPolicy {
    EagerQm31,
    LateLiftQm31,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub enum WhirFoldMode {
    RawFibers,
    LocalInterpolant,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub enum MerkleProofMode {
    SeparatePaths,
    MinimalSubtree,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub enum WhirQueryReuseMode {
    PerQueryInversion,
    RoundBatchInversion,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub enum WhirQueryPrecomputeMode {
    None,
    ProofCarriedRoundLocal,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub enum WhirMerklePayloadFormat {
    FlatNodes,
    CanonicalPayload,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub enum ArithmeticWorkloadId {
    Mul,
    Square,
    MulAdd,
    InnerProduct4,
    Horner4,
    DenominatorChain4,
    SkeletonFoldStep,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub enum ExtensionWorkloadId {
    Cm31Mul,
    Cm31Square,
    Cm31MulConst,
    Cm31Inv,
    Qm31Mul,
    Qm31Square,
    Qm31MulConst,
    Qm31Inv,
    SkeletonAccumulator,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub struct Phase2ArithmeticConfig {
    pub kernel_id: ArithmeticKernelId,
    pub reduction_mode: ReductionMode,
    pub lazy_reduction_mode: LazyReductionMode,
}

impl Phase2ArithmeticConfig {
    pub const fn new(
        kernel_id: ArithmeticKernelId,
        reduction_mode: ReductionMode,
        lazy_reduction_mode: LazyReductionMode,
    ) -> Self {
        Self {
            kernel_id,
            reduction_mode,
            lazy_reduction_mode,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub struct Phase2ExtensionConfig {
    pub base: Phase2ArithmeticConfig,
    pub extension_kernel_id: ExtensionKernelId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub struct Phase2VerifierConfig {
    pub arithmetic_kernel_id: ArithmeticKernelId,
    pub reduction_mode: ReductionMode,
    pub lazy_reduction_mode: LazyReductionMode,
    pub extension_kernel_id: ExtensionKernelId,
    pub lift_policy: LiftPolicy,
    pub whir_fold_mode: WhirFoldMode,
    pub merkle_proof_mode: MerkleProofMode,
    pub query_reuse_mode: WhirQueryReuseMode,
    pub query_precompute_mode: WhirQueryPrecomputeMode,
}

impl Phase2VerifierConfig {
    pub const fn arithmetic_config(self) -> Phase2ArithmeticConfig {
        Phase2ArithmeticConfig {
            kernel_id: self.arithmetic_kernel_id,
            reduction_mode: self.reduction_mode,
            lazy_reduction_mode: self.lazy_reduction_mode,
        }
    }

    pub const fn extension_config(self) -> Phase2ExtensionConfig {
        Phase2ExtensionConfig {
            base: self.arithmetic_config(),
            extension_kernel_id: self.extension_kernel_id,
        }
    }
}

const fn whir_query_record_words(mode: WhirQueryPrecomputeMode) -> usize {
    PHASE2_WHIR_QUERY_RECORD_WORDS
        + match mode {
            WhirQueryPrecomputeMode::None => 0,
            WhirQueryPrecomputeMode::ProofCarriedRoundLocal => PHASE2_WHIR_QUERY_PRECOMPUTED_WORDS,
        }
}

const fn whir_transcript_query_record_words(mode: WhirQueryPrecomputeMode) -> usize {
    2 + whir_query_record_words(mode)
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Phase2Counters {
    pub proof_bytes: u64,
    pub parser_bytes: u64,
    pub sha_calls: u64,
    pub sha_bytes: u64,
    pub merkle_paths: u64,
    pub merkle_levels: u64,
    pub m31_add_ops: u64,
    pub m31_mul_ops: u64,
    pub m31_square_ops: u64,
    pub m31_inv_ops: u64,
    pub cm31_mul_ops: u64,
    pub cm31_square_ops: u64,
    pub cm31_inv_ops: u64,
    pub cm31_mul_const_ops: u64,
    pub cm31_conjugate_ops: u64,
    pub qm31_mul_ops: u64,
    pub qm31_square_ops: u64,
    pub qm31_inv_ops: u64,
    pub qm31_mul_const_ops: u64,
    pub qm31_conjugate_ops: u64,
    pub lift_to_cm31_ops: u64,
    pub lift_to_qm31_ops: u64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Phase2ArithmeticOutcome {
    pub digest: u32,
    pub counters: Phase2Counters,
    pub uses_heap: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Phase2ExtensionOutcome {
    pub digest: u32,
    pub counters: Phase2Counters,
    pub uses_heap: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Phase2VerifierOutcome {
    pub digest: u32,
    pub counters: Phase2Counters,
    pub uses_heap: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub struct Phase2ProofPlan {
    pub query_count: u16,
    pub fold_arity: u16,
    pub merkle_depth: u16,
    pub merkle_paths: u16,
    pub target_proof_bytes: u32,
    pub query_schedule_seed: u64,
    pub statement_seed: u64,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub struct Phase2WhirRoundPlan {
    pub query_count: u16,
    pub merkle_depth: u16,
    pub ood_samples: u16,
    pub opening_count: u16,
    pub selector_count: u16,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub struct Phase2WhirStatementShape {
    pub spends: u16,
    pub outputs: u16,
    pub note_tree_depth: u16,
    pub note_openings_per_spend: u16,
    pub nullifier_hashes_per_spend: u16,
    pub note_commitments_per_output: u16,
    pub amount_range_checks_64: u16,
    pub ownership_checks: u16,
    pub balance_constraints: u16,
    pub lookup_arguments: u16,
    pub boundary_constraint_groups: u16,
    pub application_merkle_paths: u16,
    pub application_hash_gadgets: u16,
    pub evaluation_domain_log2: u16,
    pub merkle_rows_per_level: u16,
    pub nullifier_hash_rows: u16,
    pub note_commitment_rows: u16,
    pub range_check_rows: u16,
    pub ownership_rows: u16,
    pub balance_rows: u16,
    pub lookup_rows: u16,
    pub misc_rows: u16,
    pub total_rows: u32,
    pub row_breakdown: [u32; PHASE2_WHIR_ROW_BUCKETS],
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub struct Phase2WhirQueryPlan {
    pub round_count: u16,
    pub rounds: [Phase2WhirRoundPlan; PHASE2_WHIR_MAX_ROUNDS],
    pub statement_shape: Phase2WhirStatementShape,
    pub target_proof_bytes: u32,
    pub query_schedule_seed: u64,
    pub statement_seed: u64,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub struct Phase2WhirTranscriptRoundPlan {
    pub query_count: u16,
    pub merkle_depth: u16,
    pub ood_samples: u16,
    pub opening_count: u16,
    pub selector_count: u16,
    pub pow_bits: u16,
    pub sumcheck_rounds: u16,
    pub folding_pow_bits: u16,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub struct Phase2WhirTranscriptPlan {
    pub round_count: u16,
    pub rounds: [Phase2WhirTranscriptRoundPlan; PHASE2_WHIR_MAX_ROUNDS],
    pub statement_shape: Phase2WhirStatementShape,
    pub target_proof_bytes: u32,
    pub query_schedule_seed: u64,
    pub statement_seed: u64,
    pub commitment_ood_samples: u16,
    pub initial_sumcheck_rounds: u16,
    pub initial_folding_pow_bits: u16,
    pub final_query_count: u16,
    pub final_merkle_depth: u16,
    pub final_pow_bits: u16,
    pub final_sumcheck_rounds: u16,
    pub final_folding_pow_bits: u16,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub enum WhirTranscriptTraceMode {
    Disabled,
    Enabled,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub enum WhirTranscriptDiagnosticStage {
    Round,
    RoundReuse,
    FinalRound,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, BorshSerialize, BorshDeserialize)]
pub struct Phase2WhirTranscriptCheckpoint {
    pub transcript_state: [u8; 32],
    pub claim: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Phase2WhirTranscriptCheckpoints {
    pub round_count: u16,
    pub round_starts: [Phase2WhirTranscriptCheckpoint; PHASE2_WHIR_MAX_ROUNDS],
    pub final_round: Phase2WhirTranscriptCheckpoint,
}

#[derive(Clone, Copy, Debug)]
struct M31(u32);

#[derive(Clone, Copy, Debug)]
struct Cm31 {
    c0: M31,
    c1: M31,
}

#[derive(Clone, Copy, Debug)]
struct Qm31 {
    c0: Cm31,
    c1: Cm31,
}

#[derive(Clone, Copy)]
struct QueryRecord {
    x: Cm31,
    z0: Cm31,
    z1: Cm31,
    fold_payload: [M31; 4],
}

#[derive(Clone, Copy)]
struct WhirQueryPrecomputed {
    numerator_eval: M31,
    selector_affine_term: M31,
    selector_weight_sum: M31,
    opening_denom: Cm31,
    selector_denom: Cm31,
}

#[derive(Clone, Copy)]
struct WhirQueryRecord {
    x: Cm31,
    openings: [Cm31; PHASE2_WHIR_MAX_OPENING_TERMS],
    selectors: [Cm31; PHASE2_WHIR_SELECTOR_TERMS],
    fold_payload: [M31; PHASE2_WHIR_FOLD_VALUES],
    numerator_coeffs: [M31; PHASE2_WHIR_NUMERATOR_COEFFS],
    selector_weights: [M31; PHASE2_WHIR_SELECTOR_TERMS],
    precomputed: WhirQueryPrecomputed,
}

#[derive(Clone, Copy)]
struct WhirTranscriptQueryRecord {
    position: u64,
    inner: WhirQueryRecord,
}

#[derive(Clone, Copy)]
struct WhirQueryTerm {
    numerator_cm: Cm31,
    combined_denom: Cm31,
    beta: M31,
    gamma: Qm31,
}

const fn whir_zero_query_precomputed() -> WhirQueryPrecomputed {
    WhirQueryPrecomputed {
        numerator_eval: M31::ZERO,
        selector_affine_term: M31::ZERO,
        selector_weight_sum: M31::ZERO,
        opening_denom: Cm31 {
            c0: M31::ZERO,
            c1: M31::ZERO,
        },
        selector_denom: Cm31 {
            c0: M31::ZERO,
            c1: M31::ZERO,
        },
    }
}

#[derive(Clone, Copy)]
struct WhirSumcheckRecord {
    c0: M31,
    c_inf: M31,
    nonce: u64,
}

#[derive(Clone, Copy)]
struct WhirFinalQueryRecord {
    position: u32,
    value: M31,
}

macro_rules! bump_counter {
    ($counters:expr, $field:ident, $value:expr) => {{
        #[cfg(feature = "phase2-instrumentation")]
        {
            $counters.$field = $counters.$field.saturating_add($value as u64);
        }
    }};
}

impl M31 {
    const ZERO: Self = Self(0);
    const ONE: Self = Self(1);
    const TWO: Self = Self(2);

    fn new(value: u32) -> Option<Self> {
        (value < M31_MODULUS).then_some(Self(value))
    }

    fn new_lossy(value: u64) -> Self {
        Self(m31_reduce_direct(value))
    }

    fn as_u32(self) -> u32 {
        self.0
    }

    fn add(self, rhs: Self, counters: &mut Phase2Counters) -> Self {
        bump_counter!(counters, m31_add_ops, 1);
        let sum = self.0 as u64 + rhs.0 as u64;
        let value = if sum >= M31_MODULUS_U64 {
            (sum - M31_MODULUS_U64) as u32
        } else {
            sum as u32
        };
        Self(value)
    }

    fn sub(self, rhs: Self, counters: &mut Phase2Counters) -> Self {
        bump_counter!(counters, m31_add_ops, 1);
        if self.0 >= rhs.0 {
            Self(self.0 - rhs.0)
        } else {
            Self(((self.0 as u64 + M31_MODULUS_U64) - rhs.0 as u64) as u32)
        }
    }

    fn mul(self, rhs: Self, config: Phase2ArithmeticConfig, counters: &mut Phase2Counters) -> Self {
        bump_counter!(counters, m31_mul_ops, 1);
        let product = self.0 as u64 * rhs.0 as u64;
        let value = match config.kernel_id {
            ArithmeticKernelId::ReferenceCanonical => m31_reduce_reference(product),
            ArithmeticKernelId::DirectM31 | ArithmeticKernelId::DirectM31Lazy => {
                m31_reduce_direct(product)
            }
            ArithmeticKernelId::Montgomery => m31_mul_montgomery(self.0, rhs.0),
            ArithmeticKernelId::Barrett => m31_reduce_barrett(product),
        };
        Self(value)
    }

    fn square(self, config: Phase2ArithmeticConfig, counters: &mut Phase2Counters) -> Self {
        bump_counter!(counters, m31_square_ops, 1);
        self.mul(self, config, counters)
    }

    fn inv(self, config: Phase2ArithmeticConfig, counters: &mut Phase2Counters) -> Self {
        assert!(self.0 != 0, "inverse of zero");
        bump_counter!(counters, m31_inv_ops, 1);
        self.pow(M31_MODULUS - 2, config, counters)
    }

    fn pow(
        self,
        mut exponent: u32,
        config: Phase2ArithmeticConfig,
        counters: &mut Phase2Counters,
    ) -> Self {
        let mut result = Self::ONE;
        let mut base = self;
        while exponent > 0 {
            if exponent & 1 == 1 {
                result = result.mul(base, config, counters);
            }
            exponent >>= 1;
            if exponent > 0 {
                base = base.square(config, counters);
            }
        }
        result
    }
}

impl Cm31 {
    fn new(c0: M31, c1: M31) -> Self {
        Self { c0, c1 }
    }

    fn from_base(value: M31) -> Self {
        Self {
            c0: value,
            c1: M31::ZERO,
        }
    }

    fn add(self, rhs: Self, counters: &mut Phase2Counters) -> Self {
        Self {
            c0: self.c0.add(rhs.c0, counters),
            c1: self.c1.add(rhs.c1, counters),
        }
    }

    fn sub(self, rhs: Self, counters: &mut Phase2Counters) -> Self {
        Self {
            c0: self.c0.sub(rhs.c0, counters),
            c1: self.c1.sub(rhs.c1, counters),
        }
    }

    fn conjugate(self, counters: &mut Phase2Counters) -> Self {
        bump_counter!(counters, cm31_conjugate_ops, 1);
        Self {
            c0: self.c0,
            c1: M31::ZERO.sub(self.c1, counters),
        }
    }

    fn mul_const(
        self,
        rhs: M31,
        config: Phase2ArithmeticConfig,
        counters: &mut Phase2Counters,
    ) -> Self {
        bump_counter!(counters, cm31_mul_const_ops, 1);
        Self {
            c0: self.c0.mul(rhs, config, counters),
            c1: self.c1.mul(rhs, config, counters),
        }
    }

    fn square(self, config: Phase2ExtensionConfig, counters: &mut Phase2Counters) -> Self {
        bump_counter!(counters, cm31_square_ops, 1);
        let a2 = self.c0.square(config.base, counters);
        let b2 = self.c1.square(config.base, counters);
        let ab = self.c0.mul(self.c1, config.base, counters);
        let two_ab = ab.add(ab, counters);
        Self {
            c0: a2.sub(b2, counters),
            c1: two_ab,
        }
    }

    fn mul(self, rhs: Self, config: Phase2ExtensionConfig, counters: &mut Phase2Counters) -> Self {
        bump_counter!(counters, cm31_mul_ops, 1);
        match config.extension_kernel_id {
            ExtensionKernelId::Schoolbook => {
                let ac = self.c0.mul(rhs.c0, config.base, counters);
                let bd = self.c1.mul(rhs.c1, config.base, counters);
                let ad = self.c0.mul(rhs.c1, config.base, counters);
                let bc = self.c1.mul(rhs.c0, config.base, counters);
                Self {
                    c0: ac.sub(bd, counters),
                    c1: ad.add(bc, counters),
                }
            }
            ExtensionKernelId::Karatsuba => {
                let z0 = self.c0.mul(rhs.c0, config.base, counters);
                let z2 = self.c1.mul(rhs.c1, config.base, counters);
                let z1 = self
                    .c0
                    .add(self.c1, counters)
                    .mul(rhs.c0.add(rhs.c1, counters), config.base, counters)
                    .sub(z0, counters)
                    .sub(z2, counters);
                Self {
                    c0: z0.sub(z2, counters),
                    c1: z1,
                }
            }
        }
    }

    fn inv(self, config: Phase2ExtensionConfig, counters: &mut Phase2Counters) -> Self {
        bump_counter!(counters, cm31_inv_ops, 1);
        let a2 = self.c0.square(config.base, counters);
        let b2 = self.c1.square(config.base, counters);
        let norm = a2.add(b2, counters);
        let norm_inv = norm.inv(config.base, counters);
        self.conjugate(counters)
            .mul_const(norm_inv, config.base, counters)
    }
}

impl Qm31 {
    fn new(c0: Cm31, c1: Cm31) -> Self {
        Self { c0, c1 }
    }

    fn from_base(value: M31) -> Self {
        Self {
            c0: Cm31::from_base(value),
            c1: Cm31::from_base(M31::ZERO),
        }
    }

    fn from_cm31(value: Cm31) -> Self {
        Self {
            c0: value,
            c1: Cm31::from_base(M31::ZERO),
        }
    }

    fn add(self, rhs: Self, counters: &mut Phase2Counters) -> Self {
        Self {
            c0: self.c0.add(rhs.c0, counters),
            c1: self.c1.add(rhs.c1, counters),
        }
    }

    fn conjugate(self, counters: &mut Phase2Counters) -> Self {
        bump_counter!(counters, qm31_conjugate_ops, 1);
        Self {
            c0: self.c0,
            c1: Cm31::from_base(M31::ZERO).sub(self.c1, counters),
        }
    }

    fn mul_const(
        self,
        rhs: Cm31,
        config: Phase2ExtensionConfig,
        counters: &mut Phase2Counters,
    ) -> Self {
        bump_counter!(counters, qm31_mul_const_ops, 1);
        Self {
            c0: self.c0.mul(rhs, config, counters),
            c1: self.c1.mul(rhs, config, counters),
        }
    }

    fn square(self, config: Phase2ExtensionConfig, counters: &mut Phase2Counters) -> Self {
        bump_counter!(counters, qm31_square_ops, 1);
        let a2 = self.c0.square(config, counters);
        let b2 = self.c1.square(config, counters);
        let ab = self.c0.mul(self.c1, config, counters);
        let two_ab = ab.add(ab, counters);
        Self {
            c0: a2.add(b2.mul(non_residue_cm31(), config, counters), counters),
            c1: two_ab,
        }
    }

    fn mul(self, rhs: Self, config: Phase2ExtensionConfig, counters: &mut Phase2Counters) -> Self {
        bump_counter!(counters, qm31_mul_ops, 1);
        match config.extension_kernel_id {
            ExtensionKernelId::Schoolbook => {
                let z0 = self.c0.mul(rhs.c0, config, counters);
                let z1 = self.c0.mul(rhs.c1, config, counters);
                let z2 = self.c1.mul(rhs.c0, config, counters);
                let z3 = self.c1.mul(rhs.c1, config, counters);
                Self {
                    c0: z0.add(z3.mul(non_residue_cm31(), config, counters), counters),
                    c1: z1.add(z2, counters),
                }
            }
            ExtensionKernelId::Karatsuba => {
                let z0 = self.c0.mul(rhs.c0, config, counters);
                let z2 = self.c1.mul(rhs.c1, config, counters);
                let z1 = self
                    .c0
                    .add(self.c1, counters)
                    .mul(rhs.c0.add(rhs.c1, counters), config, counters)
                    .sub(z0, counters)
                    .sub(z2, counters);
                Self {
                    c0: z0.add(z2.mul(non_residue_cm31(), config, counters), counters),
                    c1: z1,
                }
            }
        }
    }

    fn inv(self, config: Phase2ExtensionConfig, counters: &mut Phase2Counters) -> Self {
        bump_counter!(counters, qm31_inv_ops, 1);
        let a2 = self.c0.square(config, counters);
        let b2 = self.c1.square(config, counters);
        let denom = a2.sub(b2.mul(non_residue_cm31(), config, counters), counters);
        let denom_inv = denom.inv(config, counters);
        self.conjugate(counters)
            .mul_const(denom_inv, config, counters)
    }

    fn sub(self, rhs: Self, counters: &mut Phase2Counters) -> Self {
        Self {
            c0: self.c0.sub(rhs.c0, counters),
            c1: self.c1.sub(rhs.c1, counters),
        }
    }
}

fn non_residue_cm31() -> Cm31 {
    Cm31::new(M31::ZERO, M31::ONE)
}

pub fn build_phase2_proof_bytes(plan: Phase2ProofPlan, fold_mode: WhirFoldMode) -> Vec<u8> {
    let query_count = plan.query_count.max(1) as usize;
    let fold_arity = plan.fold_arity.max(4) as usize;
    let mut out = Vec::new();
    out.extend_from_slice(&PHASE2_PROOF_MAGIC);
    out.extend_from_slice(&PHASE2_PROOF_VERSION.to_le_bytes());
    out.extend_from_slice(&(fold_mode as u16).to_le_bytes());
    out.extend_from_slice(&plan.query_count.to_le_bytes());
    out.extend_from_slice(&plan.fold_arity.to_le_bytes());
    out.extend_from_slice(&plan.merkle_depth.to_le_bytes());
    out.extend_from_slice(&plan.merkle_paths.to_le_bytes());
    out.extend_from_slice(&plan.target_proof_bytes.to_le_bytes());
    out.extend_from_slice(&plan.query_schedule_seed.to_le_bytes());
    out.extend_from_slice(&plan.statement_seed.to_le_bytes());

    let statement_digest = hashv(&[
        &plan.statement_seed.to_le_bytes(),
        &plan.query_schedule_seed.to_le_bytes(),
        &plan.query_count.to_le_bytes(),
    ])
    .to_bytes();
    out.extend_from_slice(&statement_digest);

    for query_index in 0..query_count {
        let record = build_query_record(plan, query_index as u64);
        push_query_record(&mut out, record, fold_mode, fold_arity);
    }

    let minimum_len = out.len();
    let target_len = (plan.target_proof_bytes as usize).max(minimum_len);
    let mut state = mix64(plan.query_schedule_seed ^ plan.statement_seed ^ 0x9e37_79b9_7f4a_7c15);
    while out.len() < target_len {
        state = mix64(state);
        out.extend_from_slice(&state.to_le_bytes());
    }
    out.truncate(target_len);
    out
}

pub fn build_phase2_whir_query_proof_bytes(
    plan: Phase2WhirQueryPlan,
    fold_mode: WhirFoldMode,
) -> Vec<u8> {
    let round_count = usize::from(plan.round_count.clamp(1, PHASE2_WHIR_MAX_ROUNDS as u16));
    let mut out = Vec::new();
    out.extend_from_slice(&PHASE2_WHIR_QUERY_MAGIC);
    out.extend_from_slice(&PHASE2_WHIR_QUERY_VERSION.to_le_bytes());
    out.extend_from_slice(&(fold_mode as u16).to_le_bytes());
    out.extend_from_slice(&plan.round_count.to_le_bytes());
    out.extend_from_slice(&plan.target_proof_bytes.to_le_bytes());
    out.extend_from_slice(&plan.query_schedule_seed.to_le_bytes());
    out.extend_from_slice(&plan.statement_seed.to_le_bytes());

    let statement_digest = phase2_whir_statement_digest(plan);
    out.extend_from_slice(&statement_digest);

    for round in plan.rounds.iter().take(round_count) {
        out.extend_from_slice(&round.query_count.to_le_bytes());
        out.extend_from_slice(&round.merkle_depth.to_le_bytes());
        out.extend_from_slice(&round.ood_samples.to_le_bytes());
        out.extend_from_slice(&round.opening_count.to_le_bytes());
        out.extend_from_slice(&round.selector_count.to_le_bytes());
    }

    for (round_index, round) in plan.rounds.iter().take(round_count).enumerate() {
        let query_count = usize::from(round.query_count.max(1));
        for query_index in 0..query_count {
            let record = build_whir_query_record(
                plan,
                round_index as u64,
                query_index as u64,
                *round,
                false,
            );
            push_whir_query_record(&mut out, record, fold_mode, WhirQueryPrecomputeMode::None);
        }
    }

    let minimum_len = out.len();
    let target_len = (plan.target_proof_bytes as usize).max(minimum_len);
    let mut state = mix64(plan.query_schedule_seed ^ plan.statement_seed ^ 0x5a81_0b3d_7e19_f0c1);
    while out.len() < target_len {
        state = mix64(state);
        out.extend_from_slice(&state.to_le_bytes());
    }
    out.truncate(target_len);
    out
}

pub fn build_phase2_whir_transcript_proof_bytes(
    plan: Phase2WhirTranscriptPlan,
    fold_mode: WhirFoldMode,
    merkle_mode: MerkleProofMode,
) -> Vec<u8> {
    build_phase2_whir_transcript_proof_bytes_with_precompute_mode(
        plan,
        fold_mode,
        merkle_mode,
        WhirQueryPrecomputeMode::None,
    )
}

pub fn build_phase2_whir_transcript_proof_bytes_with_precompute_mode(
    plan: Phase2WhirTranscriptPlan,
    fold_mode: WhirFoldMode,
    merkle_mode: MerkleProofMode,
    precompute_mode: WhirQueryPrecomputeMode,
) -> Vec<u8> {
    let proof = build_phase2_whir_transcript_proof_bytes_inner(
        plan,
        fold_mode,
        merkle_mode,
        precompute_mode,
    );
    if proof.len() > plan.target_proof_bytes as usize {
        let mut adjusted = plan;
        adjusted.target_proof_bytes = proof.len() as u32;
        return build_phase2_whir_transcript_proof_bytes_inner(
            adjusted,
            fold_mode,
            merkle_mode,
            precompute_mode,
        );
    }
    proof
}

fn build_phase2_whir_transcript_proof_bytes_inner(
    plan: Phase2WhirTranscriptPlan,
    fold_mode: WhirFoldMode,
    merkle_mode: MerkleProofMode,
    precompute_mode: WhirQueryPrecomputeMode,
) -> Vec<u8> {
    let round_count = usize::from(plan.round_count.clamp(0, PHASE2_WHIR_MAX_ROUNDS as u16));
    let initial_sumcheck_rounds = usize::from(
        plan.initial_sumcheck_rounds
            .min(PHASE2_WHIR_MAX_SUMCHECK_ROUNDS as u16),
    );
    let final_sumcheck_rounds = usize::from(
        plan.final_sumcheck_rounds
            .min(PHASE2_WHIR_MAX_SUMCHECK_ROUNDS as u16),
    );
    let final_coeff_count = (1usize << final_sumcheck_rounds).min(PHASE2_WHIR_MAX_FINAL_COEFFS);
    let statement_digest = phase2_whir_transcript_statement_digest(plan);

    let mut out = Vec::new();
    out.extend_from_slice(&PHASE2_WHIR_TRANSCRIPT_MAGIC);
    out.extend_from_slice(&PHASE2_WHIR_TRANSCRIPT_VERSION.to_le_bytes());
    out.extend_from_slice(&(fold_mode as u16).to_le_bytes());
    out.extend_from_slice(&(merkle_mode as u16).to_le_bytes());
    out.extend_from_slice(&plan.round_count.to_le_bytes());
    out.extend_from_slice(&plan.target_proof_bytes.to_le_bytes());
    out.extend_from_slice(&plan.query_schedule_seed.to_le_bytes());
    out.extend_from_slice(&plan.statement_seed.to_le_bytes());
    out.extend_from_slice(&statement_digest);
    write_whir_statement_shape(&mut out, plan.statement_shape);
    out.extend_from_slice(&plan.commitment_ood_samples.to_le_bytes());
    out.extend_from_slice(&plan.initial_sumcheck_rounds.to_le_bytes());
    out.extend_from_slice(&plan.initial_folding_pow_bits.to_le_bytes());
    out.extend_from_slice(&plan.final_query_count.to_le_bytes());
    out.extend_from_slice(&plan.final_merkle_depth.to_le_bytes());
    out.extend_from_slice(&plan.final_pow_bits.to_le_bytes());
    out.extend_from_slice(&plan.final_sumcheck_rounds.to_le_bytes());
    out.extend_from_slice(&plan.final_folding_pow_bits.to_le_bytes());

    for round in plan.rounds.iter().take(round_count) {
        out.extend_from_slice(&round.query_count.to_le_bytes());
        out.extend_from_slice(&round.merkle_depth.to_le_bytes());
        out.extend_from_slice(&round.ood_samples.to_le_bytes());
        out.extend_from_slice(&round.opening_count.to_le_bytes());
        out.extend_from_slice(&round.selector_count.to_le_bytes());
        out.extend_from_slice(&round.pow_bits.to_le_bytes());
        out.extend_from_slice(&round.sumcheck_rounds.to_le_bytes());
        out.extend_from_slice(&round.folding_pow_bits.to_le_bytes());
    }

    let arithmetic = Phase2ArithmeticConfig::new(
        ArithmeticKernelId::ReferenceCanonical,
        ReductionMode::Canonical,
        LazyReductionMode::None,
    );
    let extension = Phase2ExtensionConfig {
        base: arithmetic,
        extension_kernel_id: ExtensionKernelId::Karatsuba,
    };
    let mut counters = Phase2Counters::default();
    let mut transcript =
        phase2_whir_transcript_setup_state(plan, fold_mode, statement_digest, &mut counters);
    let mut claim = digest_word_to_m31(&statement_digest[0..4]);

    let commitment_root = phase2_whir_transcript_round_root(plan, u64::MAX, claim);
    out.extend_from_slice(&commitment_root);
    transcript_absorb_bytes(
        &mut transcript,
        b"phase2-whir/commitment-root",
        &commitment_root,
        &mut counters,
    );
    for sample_index in 0..usize::from(
        plan.commitment_ood_samples
            .min(PHASE2_WHIR_MAX_OOD_SAMPLES as u16),
    ) {
        let point_digest = transcript_sample(
            &mut transcript,
            b"phase2-whir/commitment-ood-point",
            &mut counters,
        );
        let answer = build_whir_transcript_ood_answer(
            plan,
            u64::MAX,
            sample_index as u64,
            point_digest,
            claim,
        );
        out.extend_from_slice(&answer.c0.as_u32().to_le_bytes());
        out.extend_from_slice(&answer.c1.as_u32().to_le_bytes());
        transcript_absorb_cm31(
            &mut transcript,
            b"phase2-whir/commitment-ood-answer",
            answer,
            &mut counters,
        );
        claim = claim.add(answer.c0.add(answer.c1, &mut counters), &mut counters);
    }

    let initial_combination = digest_word_to_m31(
        &transcript_sample(
            &mut transcript,
            b"phase2-whir/initial-combination",
            &mut counters,
        )[0..4],
    );
    claim = claim.add(initial_combination, &mut counters);
    for round in 0..initial_sumcheck_rounds {
        let record = build_whir_sumcheck_record(statement_digest, claim, u64::MAX, round as u64);
        out.extend_from_slice(&record.c0.as_u32().to_le_bytes());
        out.extend_from_slice(&record.c_inf.as_u32().to_le_bytes());
        transcript_absorb_m31(
            &mut transcript,
            b"phase2-whir/sumcheck-c0",
            record.c0,
            &mut counters,
        );
        transcript_absorb_m31(
            &mut transcript,
            b"phase2-whir/sumcheck-cinf",
            record.c_inf,
            &mut counters,
        );
        let nonce = build_whir_pow_nonce(
            &mut transcript,
            b"phase2-whir/sumcheck-pow",
            usize::from(plan.initial_folding_pow_bits),
            &mut counters,
        );
        out.extend_from_slice(&nonce.to_le_bytes());
        let challenge = digest_word_to_m31(
            &transcript_sample(
                &mut transcript,
                b"phase2-whir/folding-randomness",
                &mut counters,
            )[0..4],
        );
        claim = whir_sumcheck_update(
            claim,
            record.c0,
            record.c_inf,
            challenge,
            arithmetic,
            &mut counters,
        );
    }

    for round_index in 0..round_count {
        let round = plan.rounds[round_index];
        let root = phase2_whir_transcript_round_root(plan, round_index as u64, claim);
        out.extend_from_slice(&root);
        transcript_absorb_bytes(
            &mut transcript,
            b"phase2-whir/round-root",
            &root,
            &mut counters,
        );

        let mut round_ood = M31::ZERO;
        for sample_index in
            0..usize::from(round.ood_samples.min(PHASE2_WHIR_MAX_OOD_SAMPLES as u16))
        {
            let point_digest = transcript_sample(
                &mut transcript,
                b"phase2-whir/round-ood-point",
                &mut counters,
            );
            let answer = build_whir_transcript_ood_answer(
                plan,
                round_index as u64,
                sample_index as u64,
                point_digest,
                claim,
            );
            out.extend_from_slice(&answer.c0.as_u32().to_le_bytes());
            out.extend_from_slice(&answer.c1.as_u32().to_le_bytes());
            transcript_absorb_cm31(
                &mut transcript,
                b"phase2-whir/round-ood-answer",
                answer,
                &mut counters,
            );
            round_ood = round_ood.add(answer.c0.add(answer.c1, &mut counters), &mut counters);
        }

        let query_pow_nonce = build_whir_pow_nonce(
            &mut transcript,
            b"phase2-whir/query-pow",
            usize::from(round.pow_bits),
            &mut counters,
        );
        out.extend_from_slice(&query_pow_nonce.to_le_bytes());
        let _ = transcript_sample(
            &mut transcript,
            b"phase2-whir/transcript-checkpoint",
            &mut counters,
        );

        let query_round = transcript_round_as_query_round(round);
        let mut accumulator = Qm31::from_base(M31::ZERO);
        for query_index in 0..usize::from(round.query_count.max(1)) {
            let position_digest = transcript_sample(
                &mut transcript,
                b"phase2-whir/query-position",
                &mut counters,
            );
            let position = u64::from_le_bytes(position_digest[0..8].try_into().unwrap());
            out.extend_from_slice(&position.to_le_bytes());
            let record = build_whir_query_record(
                transcript_plan_as_query_plan(plan),
                round_index as u64,
                query_index as u64,
                query_round,
                matches!(
                    precompute_mode,
                    WhirQueryPrecomputeMode::ProofCarriedRoundLocal
                ),
            );
            push_whir_query_record(&mut out, record, fold_mode, precompute_mode);
            let evaluation_record = match fold_mode {
                WhirFoldMode::RawFibers => record,
                WhirFoldMode::LocalInterpolant => WhirQueryRecord {
                    fold_payload: multilinear_to_local_interpolant(record.fold_payload),
                    ..record
                },
            };
            let challenges = derive_whir_transcript_query_challenges(
                transcript,
                round_index as u64,
                query_index as u64,
                position,
                &mut counters,
            );
            let contribution = evaluate_whir_query_contribution(
                evaluation_record,
                query_round,
                challenges,
                arithmetic,
                extension,
                fold_mode,
                precompute_mode,
                LiftPolicy::LateLiftQm31,
                &mut counters,
            );
            accumulator = accumulator.add(contribution, &mut counters);
        }
        let merkle_digest = append_synthetic_merkle_witness(
            &mut out,
            statement_digest,
            round_index as u64,
            usize::from(round.merkle_depth.max(1)),
            usize::from(round.query_count.max(1)),
            merkle_mode,
        );
        let combination = digest_word_to_m31(
            &transcript_sample(
                &mut transcript,
                b"phase2-whir/combination-randomness",
                &mut counters,
            )[0..4],
        );
        claim = claim
            .add(round_ood, &mut counters)
            .add(digest_word_to_m31(&merkle_digest[0..4]), &mut counters)
            .add(
                digest_word_to_m31(&fold_qm31(accumulator).to_le_bytes()),
                &mut counters,
            )
            .add(combination, &mut counters);

        for sumcheck_round in 0..usize::from(
            round
                .sumcheck_rounds
                .min(PHASE2_WHIR_MAX_SUMCHECK_ROUNDS as u16),
        ) {
            let record = build_whir_sumcheck_record(
                statement_digest,
                claim,
                round_index as u64,
                sumcheck_round as u64,
            );
            out.extend_from_slice(&record.c0.as_u32().to_le_bytes());
            out.extend_from_slice(&record.c_inf.as_u32().to_le_bytes());
            transcript_absorb_m31(
                &mut transcript,
                b"phase2-whir/sumcheck-c0",
                record.c0,
                &mut counters,
            );
            transcript_absorb_m31(
                &mut transcript,
                b"phase2-whir/sumcheck-cinf",
                record.c_inf,
                &mut counters,
            );
            let nonce = build_whir_pow_nonce(
                &mut transcript,
                b"phase2-whir/sumcheck-pow",
                usize::from(round.folding_pow_bits),
                &mut counters,
            );
            out.extend_from_slice(&nonce.to_le_bytes());
            let challenge = digest_word_to_m31(
                &transcript_sample(
                    &mut transcript,
                    b"phase2-whir/folding-randomness",
                    &mut counters,
                )[0..4],
            );
            claim = whir_sumcheck_update(
                claim,
                record.c0,
                record.c_inf,
                challenge,
                arithmetic,
                &mut counters,
            );
        }
    }

    let final_coeffs = build_whir_final_coeffs(plan, claim, final_coeff_count);
    for coeff in final_coeffs.iter().take(final_coeff_count) {
        out.extend_from_slice(&coeff.as_u32().to_le_bytes());
        transcript_absorb_m31(
            &mut transcript,
            b"phase2-whir/final-coeff",
            *coeff,
            &mut counters,
        );
    }
    let final_pow_nonce = build_whir_pow_nonce(
        &mut transcript,
        b"phase2-whir/final-pow",
        usize::from(plan.final_pow_bits),
        &mut counters,
    );
    out.extend_from_slice(&final_pow_nonce.to_le_bytes());
    let mut final_claim = claim;
    for query_index in 0..usize::from(plan.final_query_count.max(1)) {
        let position_digest = transcript_sample(
            &mut transcript,
            b"phase2-whir/final-query-position",
            &mut counters,
        );
        let position = u32::from_le_bytes(position_digest[0..4].try_into().unwrap());
        let point = final_query_point(position, claim);
        let value = horner_eval_slice_m31(
            &final_coeffs[..final_coeff_count],
            point,
            arithmetic,
            &mut counters,
        );
        out.extend_from_slice(&position.to_le_bytes());
        out.extend_from_slice(&value.as_u32().to_le_bytes());
        final_claim = final_claim.add(
            value.mul(
                point.add(M31::ONE, &mut counters),
                arithmetic,
                &mut counters,
            ),
            &mut counters,
        );
        let _ = query_index;
    }
    let final_merkle = append_synthetic_merkle_witness(
        &mut out,
        statement_digest,
        u64::MAX - 1,
        usize::from(plan.final_merkle_depth.max(1)),
        usize::from(plan.final_query_count.max(1)),
        merkle_mode,
    );
    final_claim = final_claim.add(digest_word_to_m31(&final_merkle[0..4]), &mut counters);
    for round in 0..final_sumcheck_rounds {
        let record =
            build_whir_sumcheck_record(statement_digest, final_claim, u64::MAX - 1, round as u64);
        out.extend_from_slice(&record.c0.as_u32().to_le_bytes());
        out.extend_from_slice(&record.c_inf.as_u32().to_le_bytes());
        transcript_absorb_m31(
            &mut transcript,
            b"phase2-whir/final-sumcheck-c0",
            record.c0,
            &mut counters,
        );
        transcript_absorb_m31(
            &mut transcript,
            b"phase2-whir/final-sumcheck-cinf",
            record.c_inf,
            &mut counters,
        );
        let nonce = build_whir_pow_nonce(
            &mut transcript,
            b"phase2-whir/final-sumcheck-pow",
            usize::from(plan.final_folding_pow_bits),
            &mut counters,
        );
        out.extend_from_slice(&nonce.to_le_bytes());
        let challenge = digest_word_to_m31(
            &transcript_sample(
                &mut transcript,
                b"phase2-whir/final-folding-randomness",
                &mut counters,
            )[0..4],
        );
        final_claim = whir_sumcheck_update(
            final_claim,
            record.c0,
            record.c_inf,
            challenge,
            arithmetic,
            &mut counters,
        );
    }
    let deferred = build_whir_deferred_evals(plan, final_claim);
    for value in deferred {
        out.extend_from_slice(&value.as_u32().to_le_bytes());
    }

    let minimum_len = out.len();
    let target_len = (plan.target_proof_bytes as usize).max(minimum_len);
    let mut state = mix64(plan.query_schedule_seed ^ plan.statement_seed ^ 0x6f42_17d1_3c3a_98ef);
    while out.len() < target_len {
        state = mix64(state);
        out.extend_from_slice(&state.to_le_bytes());
    }
    out.truncate(target_len);
    out
}

pub fn derive_phase2_whir_transcript_checkpoints(
    plan: Phase2WhirTranscriptPlan,
    fold_mode: WhirFoldMode,
    merkle_mode: MerkleProofMode,
) -> Phase2WhirTranscriptCheckpoints {
    let round_count = usize::from(plan.round_count.clamp(0, PHASE2_WHIR_MAX_ROUNDS as u16));
    let initial_sumcheck_rounds = usize::from(
        plan.initial_sumcheck_rounds
            .min(PHASE2_WHIR_MAX_SUMCHECK_ROUNDS as u16),
    );
    let statement_digest = phase2_whir_transcript_statement_digest(plan);
    let arithmetic = Phase2ArithmeticConfig::new(
        ArithmeticKernelId::ReferenceCanonical,
        ReductionMode::Canonical,
        LazyReductionMode::None,
    );
    let extension = Phase2ExtensionConfig {
        base: arithmetic,
        extension_kernel_id: ExtensionKernelId::Karatsuba,
    };
    let mut counters = Phase2Counters::default();
    let mut transcript =
        phase2_whir_transcript_setup_state(plan, fold_mode, statement_digest, &mut counters);
    let mut claim = digest_word_to_m31(&statement_digest[0..4]);
    let commitment_root = phase2_whir_transcript_round_root(plan, u64::MAX, claim);
    transcript_absorb_bytes(
        &mut transcript,
        b"phase2-whir/commitment-root",
        &commitment_root,
        &mut counters,
    );
    for sample_index in 0..usize::from(
        plan.commitment_ood_samples
            .min(PHASE2_WHIR_MAX_OOD_SAMPLES as u16),
    ) {
        let point_digest = transcript_sample(
            &mut transcript,
            b"phase2-whir/commitment-ood-point",
            &mut counters,
        );
        let answer = build_whir_transcript_ood_answer(
            plan,
            u64::MAX,
            sample_index as u64,
            point_digest,
            claim,
        );
        transcript_absorb_cm31(
            &mut transcript,
            b"phase2-whir/commitment-ood-answer",
            answer,
            &mut counters,
        );
        claim = claim.add(answer.c0.add(answer.c1, &mut counters), &mut counters);
    }

    let initial_combination = digest_word_to_m31(
        &transcript_sample(
            &mut transcript,
            b"phase2-whir/initial-combination",
            &mut counters,
        )[0..4],
    );
    claim = claim.add(initial_combination, &mut counters);
    for round in 0..initial_sumcheck_rounds {
        let record = build_whir_sumcheck_record(statement_digest, claim, u64::MAX, round as u64);
        transcript_absorb_m31(
            &mut transcript,
            b"phase2-whir/sumcheck-c0",
            record.c0,
            &mut counters,
        );
        transcript_absorb_m31(
            &mut transcript,
            b"phase2-whir/sumcheck-cinf",
            record.c_inf,
            &mut counters,
        );
        let _nonce = build_whir_pow_nonce(
            &mut transcript,
            b"phase2-whir/sumcheck-pow",
            usize::from(plan.initial_folding_pow_bits),
            &mut counters,
        );
        let challenge = digest_word_to_m31(
            &transcript_sample(
                &mut transcript,
                b"phase2-whir/folding-randomness",
                &mut counters,
            )[0..4],
        );
        claim = whir_sumcheck_update(
            claim,
            record.c0,
            record.c_inf,
            challenge,
            arithmetic,
            &mut counters,
        );
    }

    let mut round_starts = [Phase2WhirTranscriptCheckpoint {
        transcript_state: [0_u8; 32],
        claim: 0,
    }; PHASE2_WHIR_MAX_ROUNDS];
    for round_index in 0..round_count {
        round_starts[round_index] = Phase2WhirTranscriptCheckpoint {
            transcript_state: transcript,
            claim: claim.as_u32(),
        };

        let round = plan.rounds[round_index];
        let root = phase2_whir_transcript_round_root(plan, round_index as u64, claim);
        transcript_absorb_bytes(
            &mut transcript,
            b"phase2-whir/round-root",
            &root,
            &mut counters,
        );
        let mut round_ood = M31::ZERO;
        for sample_index in
            0..usize::from(round.ood_samples.min(PHASE2_WHIR_MAX_OOD_SAMPLES as u16))
        {
            let point_digest = transcript_sample(
                &mut transcript,
                b"phase2-whir/round-ood-point",
                &mut counters,
            );
            let answer = build_whir_transcript_ood_answer(
                plan,
                round_index as u64,
                sample_index as u64,
                point_digest,
                claim,
            );
            transcript_absorb_cm31(
                &mut transcript,
                b"phase2-whir/round-ood-answer",
                answer,
                &mut counters,
            );
            round_ood = round_ood.add(answer.c0.add(answer.c1, &mut counters), &mut counters);
        }

        let _query_pow_nonce = build_whir_pow_nonce(
            &mut transcript,
            b"phase2-whir/query-pow",
            usize::from(round.pow_bits),
            &mut counters,
        );
        let _ = transcript_sample(
            &mut transcript,
            b"phase2-whir/transcript-checkpoint",
            &mut counters,
        );

        let query_round = transcript_round_as_query_round(round);
        let mut accumulator = Qm31::from_base(M31::ZERO);
        for query_index in 0..usize::from(round.query_count.max(1)) {
            let position_digest = transcript_sample(
                &mut transcript,
                b"phase2-whir/query-position",
                &mut counters,
            );
            let position = u64::from_le_bytes(position_digest[0..8].try_into().unwrap());
            let record = build_whir_query_record(
                transcript_plan_as_query_plan(plan),
                round_index as u64,
                query_index as u64,
                query_round,
                false,
            );
            let evaluation_record = match fold_mode {
                WhirFoldMode::RawFibers => record,
                WhirFoldMode::LocalInterpolant => WhirQueryRecord {
                    fold_payload: multilinear_to_local_interpolant(record.fold_payload),
                    ..record
                },
            };
            let challenges = derive_whir_transcript_query_challenges(
                transcript,
                round_index as u64,
                query_index as u64,
                position,
                &mut counters,
            );
            let contribution = evaluate_whir_query_contribution(
                evaluation_record,
                query_round,
                challenges,
                arithmetic,
                extension,
                fold_mode,
                WhirQueryPrecomputeMode::None,
                LiftPolicy::LateLiftQm31,
                &mut counters,
            );
            accumulator = accumulator.add(contribution, &mut counters);
        }
        let merkle_digest = generated_synthetic_merkle_digest(
            statement_digest,
            round_index as u64,
            usize::from(round.merkle_depth.max(1)),
            usize::from(round.query_count.max(1)),
            merkle_mode,
        );
        let combination = digest_word_to_m31(
            &transcript_sample(
                &mut transcript,
                b"phase2-whir/combination-randomness",
                &mut counters,
            )[0..4],
        );
        claim = claim
            .add(round_ood, &mut counters)
            .add(digest_word_to_m31(&merkle_digest[0..4]), &mut counters)
            .add(
                digest_word_to_m31(&fold_qm31(accumulator).to_le_bytes()),
                &mut counters,
            )
            .add(combination, &mut counters);

        for sumcheck_round in 0..usize::from(
            round
                .sumcheck_rounds
                .min(PHASE2_WHIR_MAX_SUMCHECK_ROUNDS as u16),
        ) {
            let record = build_whir_sumcheck_record(
                statement_digest,
                claim,
                round_index as u64,
                sumcheck_round as u64,
            );
            transcript_absorb_m31(
                &mut transcript,
                b"phase2-whir/sumcheck-c0",
                record.c0,
                &mut counters,
            );
            transcript_absorb_m31(
                &mut transcript,
                b"phase2-whir/sumcheck-cinf",
                record.c_inf,
                &mut counters,
            );
            let _nonce = build_whir_pow_nonce(
                &mut transcript,
                b"phase2-whir/sumcheck-pow",
                usize::from(round.folding_pow_bits),
                &mut counters,
            );
            let challenge = digest_word_to_m31(
                &transcript_sample(
                    &mut transcript,
                    b"phase2-whir/folding-randomness",
                    &mut counters,
                )[0..4],
            );
            claim = whir_sumcheck_update(
                claim,
                record.c0,
                record.c_inf,
                challenge,
                arithmetic,
                &mut counters,
            );
        }
    }

    Phase2WhirTranscriptCheckpoints {
        round_count: plan.round_count,
        round_starts,
        final_round: Phase2WhirTranscriptCheckpoint {
            transcript_state: transcript,
            claim: claim.as_u32(),
        },
    }
}

pub fn run_phase2_arithmetic_bench(
    config: Phase2ArithmeticConfig,
    workload: ArithmeticWorkloadId,
    iterations: u32,
) -> Phase2ArithmeticOutcome {
    let mut counters = Phase2Counters::default();
    let iterations = iterations.max(1);
    let digest = match config.kernel_id {
        ArithmeticKernelId::ReferenceCanonical => {
            run_m31_workload::<ReferenceKernel>(config, workload, iterations, &mut counters)
        }
        ArithmeticKernelId::DirectM31 => {
            run_m31_workload::<DirectKernel>(config, workload, iterations, &mut counters)
        }
        ArithmeticKernelId::DirectM31Lazy => {
            run_m31_workload::<DirectLazyKernel>(config, workload, iterations, &mut counters)
        }
        ArithmeticKernelId::Montgomery => {
            run_m31_workload::<MontgomeryKernel>(config, workload, iterations, &mut counters)
        }
        ArithmeticKernelId::Barrett => {
            run_m31_workload::<BarrettKernel>(config, workload, iterations, &mut counters)
        }
    };
    Phase2ArithmeticOutcome {
        digest,
        counters,
        uses_heap: false,
    }
}

pub fn run_phase2_extension_bench(
    config: Phase2ExtensionConfig,
    workload: ExtensionWorkloadId,
    iterations: u32,
) -> Phase2ExtensionOutcome {
    let mut counters = Phase2Counters::default();
    let mut digest = 0_u32;
    let rounds = iterations.max(1);
    for round in 0..rounds {
        let seed = mix64((round as u64) ^ 0x1234_5678_9abc_def0);
        let a = seeded_qm31(seed);
        let b = seeded_qm31(seed.rotate_left(7));
        let c = seeded_cm31(seed.rotate_left(19));
        let result = match workload {
            ExtensionWorkloadId::Cm31Mul => {
                let lhs = a.c0;
                let rhs = b.c0;
                Qm31::from_cm31(lhs.mul(rhs, config, &mut counters))
            }
            ExtensionWorkloadId::Cm31Square => Qm31::from_cm31(a.c0.square(config, &mut counters)),
            ExtensionWorkloadId::Cm31MulConst => {
                Qm31::from_cm31(a.c0.mul_const(c.c0, config.base, &mut counters))
            }
            ExtensionWorkloadId::Cm31Inv => Qm31::from_cm31(a.c0.inv(config, &mut counters)),
            ExtensionWorkloadId::Qm31Mul => a.mul(b, config, &mut counters),
            ExtensionWorkloadId::Qm31Square => a.square(config, &mut counters),
            ExtensionWorkloadId::Qm31MulConst => a.mul_const(c, config, &mut counters),
            ExtensionWorkloadId::Qm31Inv => a.inv(config, &mut counters),
            ExtensionWorkloadId::SkeletonAccumulator => {
                skeleton_extension_accumulator(a, b, c, config, &mut counters)
            }
        };
        digest ^= fold_qm31(result);
    }
    Phase2ExtensionOutcome {
        digest,
        counters,
        uses_heap: false,
    }
}

pub fn run_phase2_skeleton_verify(
    config: Phase2VerifierConfig,
    proof_bytes: &[u8],
    repeat: u32,
) -> Result<Phase2VerifierOutcome, &'static str> {
    let view = Phase2ProofView::parse(proof_bytes)?;
    if view.fold_mode != config.whir_fold_mode {
        return Err("phase2 fold mode config/proof mismatch");
    }
    let mut counters = Phase2Counters::default();
    counters.proof_bytes = proof_bytes.len() as u64;
    counters.parser_bytes = proof_bytes.len() as u64;
    counters.merkle_paths = view.merkle_paths as u64;
    counters.merkle_levels = view.merkle_depth as u64 * view.merkle_paths as u64;

    let mut digest = 0_u32;
    let extension = config.extension_config();
    let tail_checksum = checksum_tail(view.tail_bytes());
    for repetition in 0..repeat.max(1) {
        let mut acc = Qm31::from_base(M31::ZERO);
        for query_index in 0..view.query_count as usize {
            let record = view.query_record(query_index)?;
            bump_counter!(counters, sha_calls, 1);
            bump_counter!(counters, sha_bytes, (TRANSCRIPT_DIGEST_BYTES + 8) as u64);
            let transcript = transcript_material(view.statement_digest, repetition, query_index);
            let challenges = derive_challenges(transcript, &mut counters);
            let local_eval = evaluate_fold(
                record.fold_payload,
                challenges.fold_r0,
                challenges.fold_r1,
                config.arithmetic_config(),
                config.whir_fold_mode,
                &mut counters,
            );
            let d0 = record.x.sub(record.z0, &mut counters);
            let d1 = record
                .x
                .conjugate(&mut counters)
                .sub(record.z1, &mut counters);
            let denom = d0.mul(d1, extension, &mut counters);
            let inv = denom.inv(extension, &mut counters);
            let per_query = match config.lift_policy {
                LiftPolicy::LateLiftQm31 => {
                    let scaled =
                        inv.mul_const(local_eval, config.arithmetic_config(), &mut counters);
                    bump_counter!(counters, lift_to_qm31_ops, 1);
                    Qm31::from_cm31(scaled).mul(challenges.gamma, extension, &mut counters)
                }
                LiftPolicy::EagerQm31 => {
                    bump_counter!(counters, lift_to_cm31_ops, 1);
                    bump_counter!(counters, lift_to_qm31_ops, 1);
                    let local_qm = Qm31::from_base(local_eval);
                    let inv_qm = Qm31::from_cm31(inv);
                    local_qm.mul(inv_qm, extension, &mut counters).mul(
                        challenges.gamma,
                        extension,
                        &mut counters,
                    )
                }
            };
            acc = acc.add(per_query, &mut counters);
        }
        let merkle_sha = synthetic_merkle_cost(
            view.merkle_depth as usize,
            view.merkle_paths as usize,
            config.merkle_proof_mode,
            &mut counters,
        );
        let checksum = fold_qm31(acc)
            ^ u32::from_le_bytes([merkle_sha[0], merkle_sha[1], merkle_sha[2], merkle_sha[3]])
            ^ tail_checksum;
        digest ^= checksum.rotate_left(repetition % 31);
    }

    Ok(Phase2VerifierOutcome {
        digest,
        counters,
        uses_heap: false,
    })
}

pub fn run_phase2_whir_query_verify(
    config: Phase2VerifierConfig,
    proof_bytes: &[u8],
    repeat: u32,
) -> Result<Phase2VerifierOutcome, &'static str> {
    let view = Phase2WhirQueryView::parse(proof_bytes)?;
    if view.fold_mode != config.whir_fold_mode {
        return Err("phase2 whir fold mode config/proof mismatch");
    }
    let mut counters = Phase2Counters::default();
    counters.proof_bytes = proof_bytes.len() as u64;
    counters.parser_bytes = proof_bytes.len() as u64;
    counters.merkle_paths = view.total_query_count() as u64;
    counters.merkle_levels = view.total_merkle_levels() as u64;

    let arithmetic = config.arithmetic_config();
    let extension = config.extension_config();
    let tail_checksum = checksum_tail(view.tail_bytes());
    let mut digest = 0_u32;
    for repetition in 0..repeat.max(1) {
        let mut accumulator = Qm31::from_base(M31::ZERO);
        for round_index in 0..view.round_count {
            let round = view.round_plan(round_index);
            let selector_count = usize::from(
                round
                    .selector_count
                    .clamp(1, PHASE2_WHIR_SELECTOR_TERMS as u16),
            );
            let opening_count = usize::from(
                round
                    .opening_count
                    .clamp(1, PHASE2_WHIR_MAX_OPENING_TERMS as u16),
            );
            for query_index in 0..usize::from(round.query_count.max(1)) {
                bump_counter!(counters, sha_calls, 1);
                bump_counter!(counters, sha_bytes, (TRANSCRIPT_DIGEST_BYTES + 12) as u64);
                let transcript = whir_query_transcript_material(
                    view.statement_digest,
                    repetition,
                    round_index,
                    query_index,
                    round.ood_samples,
                );
                let challenges = derive_whir_query_challenges(transcript, &mut counters);
                let record = view.query_record(round_index, query_index)?;
                let local_eval = evaluate_fold8(
                    record.fold_payload,
                    challenges.fold_r,
                    arithmetic,
                    config.whir_fold_mode,
                    &mut counters,
                );
                let numerator_eval = horner_eval_m31(
                    record.numerator_coeffs,
                    record.x.c0,
                    arithmetic,
                    &mut counters,
                );
                let selector_eval = selector_mix_m31(
                    record.selector_weights,
                    record.selectors,
                    selector_count,
                    challenges.beta,
                    arithmetic,
                    &mut counters,
                );
                let numerator_cm =
                    Cm31::new(local_eval.add(numerator_eval, &mut counters), selector_eval);
                let opening_denom = denominator_chain_cm31(
                    record.x,
                    &record.openings,
                    opening_count,
                    extension,
                    &mut counters,
                );
                let selector_denom = denominator_chain_cm31(
                    record.x.conjugate(&mut counters),
                    &record.selectors,
                    selector_count,
                    extension,
                    &mut counters,
                );
                let combined_denom = opening_denom.mul(selector_denom, extension, &mut counters);
                let denom_inv = combined_denom.inv(extension, &mut counters);
                let per_query = match config.lift_policy {
                    LiftPolicy::LateLiftQm31 => {
                        let residue = numerator_cm.mul(denom_inv, extension, &mut counters);
                        let weighted =
                            residue.mul_const(challenges.beta, arithmetic, &mut counters);
                        bump_counter!(counters, lift_to_qm31_ops, 1);
                        Qm31::from_cm31(weighted).mul(challenges.gamma, extension, &mut counters)
                    }
                    LiftPolicy::EagerQm31 => {
                        bump_counter!(counters, lift_to_cm31_ops, 1);
                        bump_counter!(counters, lift_to_qm31_ops, 1);
                        Qm31::from_cm31(numerator_cm)
                            .mul(Qm31::from_cm31(denom_inv), extension, &mut counters)
                            .mul(challenges.gamma, extension, &mut counters)
                    }
                };
                accumulator = accumulator.add(per_query, &mut counters);
            }
            let merkle_sha = synthetic_merkle_cost(
                usize::from(round.merkle_depth.max(1)),
                usize::from(round.query_count.max(1)),
                config.merkle_proof_mode,
                &mut counters,
            );
            let round_seed = digest_word_to_m31(&merkle_sha[0..4]);
            accumulator = accumulator.add(Qm31::from_base(round_seed), &mut counters);
        }
        let checksum = fold_qm31(accumulator) ^ tail_checksum;
        digest ^= checksum.rotate_left((repetition + 1) % 31);
    }

    Ok(Phase2VerifierOutcome {
        digest,
        counters,
        uses_heap: false,
    })
}

pub fn run_phase2_whir_transcript_verify(
    config: Phase2VerifierConfig,
    proof_bytes: &[u8],
    repeat: u32,
    trace_mode: WhirTranscriptTraceMode,
) -> Result<Phase2VerifierOutcome, &'static str> {
    trace_phase_begin(trace_mode, "parse");
    let view = Phase2WhirTranscriptView::parse(proof_bytes, config.query_precompute_mode)?;
    trace_phase_end(trace_mode, "parse");
    if view.fold_mode != config.whir_fold_mode {
        return Err("phase2 whir transcript fold mode config/proof mismatch");
    }
    if view.merkle_mode != config.merkle_proof_mode {
        return Err("phase2 whir transcript merkle mode config/proof mismatch");
    }
    let mut counters = Phase2Counters::default();
    counters.proof_bytes = proof_bytes.len() as u64;
    counters.parser_bytes = proof_bytes.len() as u64;
    counters.merkle_paths =
        (view.total_intermediate_query_count() + view.final_query_count()) as u64;
    counters.merkle_levels =
        (view.total_intermediate_merkle_levels() + view.final_merkle_levels()) as u64;

    let arithmetic = config.arithmetic_config();
    let extension = config.extension_config();
    let query_plan = transcript_plan_as_query_plan(view.plan());
    let tail_checksum = checksum_tail(view.tail_bytes());
    let mut digest = 0_u32;
    for repetition in 0..repeat.max(1) {
        trace_phase_begin(trace_mode, "transcript_setup");
        let mut transcript = phase2_whir_transcript_setup_state(
            view.plan(),
            view.fold_mode,
            view.statement_digest,
            &mut counters,
        );
        let mut claim = digest_word_to_m31(&view.statement_digest[0..4]);
        let expected_commitment_root =
            phase2_whir_transcript_round_root(view.plan(), u64::MAX, claim);
        if view.commitment_root() != expected_commitment_root {
            return Err("phase2 whir transcript commitment root mismatch");
        }
        transcript_absorb_bytes(
            &mut transcript,
            b"phase2-whir/commitment-root",
            &expected_commitment_root,
            &mut counters,
        );
        trace_phase_end(trace_mode, "transcript_setup");

        trace_phase_begin(trace_mode, "ood");
        for sample_index in 0..view.commitment_ood_count() {
            let point_digest = transcript_sample(
                &mut transcript,
                b"phase2-whir/commitment-ood-point",
                &mut counters,
            );
            let expected = build_whir_transcript_ood_answer(
                view.plan(),
                u64::MAX,
                sample_index as u64,
                point_digest,
                claim,
            );
            let actual = view.commitment_ood_answer(sample_index)?;
            if actual.c0.as_u32() != expected.c0.as_u32()
                || actual.c1.as_u32() != expected.c1.as_u32()
            {
                return Err("phase2 whir transcript commitment ood mismatch");
            }
            transcript_absorb_cm31(
                &mut transcript,
                b"phase2-whir/commitment-ood-answer",
                actual,
                &mut counters,
            );
            claim = claim.add(actual.c0.add(actual.c1, &mut counters), &mut counters);
        }
        trace_phase_end(trace_mode, "ood");

        trace_phase_begin(trace_mode, "folding");
        let initial_combination = digest_word_to_m31(
            &transcript_sample(
                &mut transcript,
                b"phase2-whir/initial-combination",
                &mut counters,
            )[0..4],
        );
        claim = claim.add(initial_combination, &mut counters);
        for round in 0..view.initial_sumcheck_round_count() {
            let record = view.initial_sumcheck_record(round)?;
            transcript_absorb_m31(
                &mut transcript,
                b"phase2-whir/sumcheck-c0",
                record.c0,
                &mut counters,
            );
            transcript_absorb_m31(
                &mut transcript,
                b"phase2-whir/sumcheck-cinf",
                record.c_inf,
                &mut counters,
            );
            verify_whir_pow_nonce(
                &mut transcript,
                b"phase2-whir/sumcheck-pow",
                usize::from(view.initial_folding_pow_bits),
                record.nonce,
                &mut counters,
            )?;
            let challenge = digest_word_to_m31(
                &transcript_sample(
                    &mut transcript,
                    b"phase2-whir/folding-randomness",
                    &mut counters,
                )[0..4],
            );
            claim = whir_sumcheck_update(
                claim,
                record.c0,
                record.c_inf,
                challenge,
                arithmetic,
                &mut counters,
            );
        }
        trace_phase_end(trace_mode, "folding");

        for round_index in 0..view.round_count {
            let round = view.round_plan(round_index);

            trace_phase_begin(trace_mode, "ood");
            let expected_root =
                phase2_whir_transcript_round_root(view.plan(), round_index as u64, claim);
            if view.round_root(round_index)? != expected_root {
                return Err("phase2 whir transcript round root mismatch");
            }
            transcript_absorb_bytes(
                &mut transcript,
                b"phase2-whir/round-root",
                &expected_root,
                &mut counters,
            );
            let mut round_ood = M31::ZERO;
            for sample_index in
                0..usize::from(round.ood_samples.min(PHASE2_WHIR_MAX_OOD_SAMPLES as u16))
            {
                let point_digest = transcript_sample(
                    &mut transcript,
                    b"phase2-whir/round-ood-point",
                    &mut counters,
                );
                let expected = build_whir_transcript_ood_answer(
                    view.plan(),
                    round_index as u64,
                    sample_index as u64,
                    point_digest,
                    claim,
                );
                let actual = view.round_ood_answer(round_index, sample_index)?;
                if actual.c0.as_u32() != expected.c0.as_u32()
                    || actual.c1.as_u32() != expected.c1.as_u32()
                {
                    return Err("phase2 whir transcript round ood mismatch");
                }
                transcript_absorb_cm31(
                    &mut transcript,
                    b"phase2-whir/round-ood-answer",
                    actual,
                    &mut counters,
                );
                round_ood = round_ood.add(actual.c0.add(actual.c1, &mut counters), &mut counters);
            }
            trace_phase_end(trace_mode, "ood");

            trace_phase_begin(trace_mode, "per_round_queries");
            verify_whir_pow_nonce(
                &mut transcript,
                b"phase2-whir/query-pow",
                usize::from(round.pow_bits),
                view.round_query_pow_nonce(round_index)?,
                &mut counters,
            )?;
            let _ = transcript_sample(
                &mut transcript,
                b"phase2-whir/transcript-checkpoint",
                &mut counters,
            );

            let accumulator = match config.query_reuse_mode {
                WhirQueryReuseMode::PerQueryInversion => {
                    let mut accumulator = Qm31::from_base(M31::ZERO);
                    let query_round = transcript_round_as_query_round(round);
                    for query_index in 0..usize::from(round.query_count.max(1)) {
                        let position_digest = transcript_sample(
                            &mut transcript,
                            b"phase2-whir/query-position",
                            &mut counters,
                        );
                        let expected_position =
                            u64::from_le_bytes(position_digest[0..8].try_into().unwrap());
                        let actual = view.round_query_record(round_index, query_index)?;
                        if actual.position != expected_position {
                            return Err("phase2 whir transcript query position mismatch");
                        }
                        let expected_record = build_whir_query_record(
                            query_plan,
                            round_index as u64,
                            query_index as u64,
                            query_round,
                            matches!(
                                config.query_precompute_mode,
                                WhirQueryPrecomputeMode::ProofCarriedRoundLocal
                            ),
                        );
                        if !whir_query_record_matches(expected_record, actual.inner, view.fold_mode)
                            || !whir_query_precomputed_matches(
                                expected_record,
                                actual.inner,
                                config.query_precompute_mode,
                            )
                        {
                            return Err("phase2 whir transcript query record mismatch");
                        }
                        let challenges = derive_whir_transcript_query_challenges(
                            transcript,
                            round_index as u64,
                            query_index as u64,
                            actual.position,
                            &mut counters,
                        );
                        let contribution = evaluate_whir_query_contribution(
                            actual.inner,
                            query_round,
                            challenges,
                            arithmetic,
                            extension,
                            view.fold_mode,
                            config.query_precompute_mode,
                            config.lift_policy,
                            &mut counters,
                        );
                        accumulator = accumulator.add(contribution, &mut counters);
                    }
                    accumulator
                }
                WhirQueryReuseMode::RoundBatchInversion => evaluate_whir_round_queries_reuse(
                    &view,
                    query_plan,
                    config,
                    round_index,
                    &mut transcript,
                    &mut counters,
                )?,
            };
            let merkle_digest = digest_synthetic_merkle_witness(
                view.round_merkle_witness(round_index),
                usize::from(round.merkle_depth.max(1)),
                usize::from(round.query_count.max(1)),
                config.merkle_proof_mode,
                &mut counters,
            )?;
            trace_phase_end(trace_mode, "per_round_queries");

            trace_phase_begin(trace_mode, "folding");
            let combination = digest_word_to_m31(
                &transcript_sample(
                    &mut transcript,
                    b"phase2-whir/combination-randomness",
                    &mut counters,
                )[0..4],
            );
            claim = claim
                .add(round_ood, &mut counters)
                .add(digest_word_to_m31(&merkle_digest[0..4]), &mut counters)
                .add(M31::new_lossy(fold_qm31(accumulator) as u64), &mut counters)
                .add(combination, &mut counters);
            for sumcheck_round in 0..usize::from(
                round
                    .sumcheck_rounds
                    .min(PHASE2_WHIR_MAX_SUMCHECK_ROUNDS as u16),
            ) {
                let record = view.round_sumcheck_record(round_index, sumcheck_round)?;
                transcript_absorb_m31(
                    &mut transcript,
                    b"phase2-whir/sumcheck-c0",
                    record.c0,
                    &mut counters,
                );
                transcript_absorb_m31(
                    &mut transcript,
                    b"phase2-whir/sumcheck-cinf",
                    record.c_inf,
                    &mut counters,
                );
                verify_whir_pow_nonce(
                    &mut transcript,
                    b"phase2-whir/sumcheck-pow",
                    usize::from(round.folding_pow_bits),
                    record.nonce,
                    &mut counters,
                )?;
                let challenge = digest_word_to_m31(
                    &transcript_sample(
                        &mut transcript,
                        b"phase2-whir/folding-randomness",
                        &mut counters,
                    )[0..4],
                );
                claim = whir_sumcheck_update(
                    claim,
                    record.c0,
                    record.c_inf,
                    challenge,
                    arithmetic,
                    &mut counters,
                );
            }
            trace_phase_end(trace_mode, "folding");
        }

        trace_phase_begin(trace_mode, "final_round");
        let final_coeff_count = view.final_coeff_count();
        let mut final_coeffs = [M31::ZERO; PHASE2_WHIR_MAX_FINAL_COEFFS];
        for index in 0..final_coeff_count {
            let actual = view.final_coeff(index)?;
            final_coeffs[index] = actual;
            transcript_absorb_m31(
                &mut transcript,
                b"phase2-whir/final-coeff",
                actual,
                &mut counters,
            );
        }
        verify_whir_pow_nonce(
            &mut transcript,
            b"phase2-whir/final-pow",
            usize::from(view.final_pow_bits),
            view.final_pow_nonce()?,
            &mut counters,
        )?;
        let mut final_claim = claim;
        for query_index in 0..view.final_query_count() {
            let position_digest = transcript_sample(
                &mut transcript,
                b"phase2-whir/final-query-position",
                &mut counters,
            );
            let expected_position = u32::from_le_bytes(position_digest[0..4].try_into().unwrap());
            let record = view.final_query_record(query_index)?;
            if record.position != expected_position {
                return Err("phase2 whir transcript final query position mismatch");
            }
            let point = final_query_point(expected_position, claim);
            let expected_value = horner_eval_slice_m31(
                &final_coeffs[..final_coeff_count],
                point,
                arithmetic,
                &mut counters,
            );
            if record.value.as_u32() != expected_value.as_u32() {
                return Err("phase2 whir transcript final query value mismatch");
            }
            final_claim = final_claim.add(
                record.value.mul(
                    point.add(M31::ONE, &mut counters),
                    arithmetic,
                    &mut counters,
                ),
                &mut counters,
            );
        }
        let final_merkle = digest_synthetic_merkle_witness(
            view.final_merkle_witness(),
            usize::from(view.final_merkle_depth.max(1)),
            view.final_query_count().max(1),
            config.merkle_proof_mode,
            &mut counters,
        )?;
        final_claim = final_claim.add(digest_word_to_m31(&final_merkle[0..4]), &mut counters);
        for round in 0..view.final_sumcheck_round_count() {
            let record = view.final_sumcheck_record(round)?;
            transcript_absorb_m31(
                &mut transcript,
                b"phase2-whir/final-sumcheck-c0",
                record.c0,
                &mut counters,
            );
            transcript_absorb_m31(
                &mut transcript,
                b"phase2-whir/final-sumcheck-cinf",
                record.c_inf,
                &mut counters,
            );
            verify_whir_pow_nonce(
                &mut transcript,
                b"phase2-whir/final-sumcheck-pow",
                usize::from(view.final_folding_pow_bits),
                record.nonce,
                &mut counters,
            )?;
            let challenge = digest_word_to_m31(
                &transcript_sample(
                    &mut transcript,
                    b"phase2-whir/final-folding-randomness",
                    &mut counters,
                )[0..4],
            );
            final_claim = whir_sumcheck_update(
                final_claim,
                record.c0,
                record.c_inf,
                challenge,
                arithmetic,
                &mut counters,
            );
        }
        let deferred = build_whir_deferred_evals(view.plan(), final_claim);
        for (index, expected) in deferred.iter().enumerate() {
            let actual = view.deferred_eval(index)?;
            if actual.as_u32() != expected.as_u32() {
                return Err("phase2 whir transcript deferred eval mismatch");
            }
        }
        trace_phase_end(trace_mode, "final_round");

        digest ^= final_claim.as_u32().rotate_left((repetition + 1) % 31) ^ tail_checksum;
    }

    Ok(Phase2VerifierOutcome {
        digest,
        counters,
        uses_heap: false,
    })
}

pub fn run_phase2_whir_transcript_segment_verify(
    config: Phase2VerifierConfig,
    proof_bytes: &[u8],
    stage: WhirTranscriptDiagnosticStage,
    round_index: u16,
    checkpoint: Phase2WhirTranscriptCheckpoint,
    repeat: u32,
    trace_mode: WhirTranscriptTraceMode,
) -> Result<Phase2VerifierOutcome, &'static str> {
    trace_phase_begin(trace_mode, "parse");
    let view = Phase2WhirTranscriptView::parse(proof_bytes, config.query_precompute_mode)?;
    trace_phase_end(trace_mode, "parse");
    if view.fold_mode != config.whir_fold_mode {
        return Err("phase2 whir transcript fold mode config/proof mismatch");
    }
    if view.merkle_mode != config.merkle_proof_mode {
        return Err("phase2 whir transcript merkle mode config/proof mismatch");
    }
    let mut counters = Phase2Counters::default();
    counters.proof_bytes = proof_bytes.len() as u64;
    counters.parser_bytes = proof_bytes.len() as u64;
    counters.merkle_paths =
        (view.total_intermediate_query_count() + view.final_query_count()) as u64;
    counters.merkle_levels =
        (view.total_intermediate_merkle_levels() + view.final_merkle_levels()) as u64;

    let arithmetic = config.arithmetic_config();
    let extension = config.extension_config();
    let query_plan = transcript_plan_as_query_plan(view.plan());
    let tail_checksum = checksum_tail(view.tail_bytes());
    let mut digest = 0_u32;

    for repetition in 0..repeat.max(1) {
        let mut transcript = checkpoint.transcript_state;
        let mut claim = M31::new_lossy(checkpoint.claim as u64);
        match stage {
            WhirTranscriptDiagnosticStage::Round | WhirTranscriptDiagnosticStage::RoundReuse => {
                let reuse_queries = matches!(stage, WhirTranscriptDiagnosticStage::RoundReuse);
                let round_index = usize::from(round_index);
                if round_index >= view.round_count {
                    return Err("phase2 whir transcript diagnostic round out of range");
                }
                let round = view.round_plan(round_index);
                trace_phase_begin(trace_mode, "ood");
                let expected_root =
                    phase2_whir_transcript_round_root(view.plan(), round_index as u64, claim);
                if view.round_root(round_index)? != expected_root {
                    return Err("phase2 whir transcript round root mismatch");
                }
                transcript_absorb_bytes(
                    &mut transcript,
                    b"phase2-whir/round-root",
                    &expected_root,
                    &mut counters,
                );
                let mut round_ood = M31::ZERO;
                for sample_index in
                    0..usize::from(round.ood_samples.min(PHASE2_WHIR_MAX_OOD_SAMPLES as u16))
                {
                    let point_digest = transcript_sample(
                        &mut transcript,
                        b"phase2-whir/round-ood-point",
                        &mut counters,
                    );
                    let expected = build_whir_transcript_ood_answer(
                        view.plan(),
                        round_index as u64,
                        sample_index as u64,
                        point_digest,
                        claim,
                    );
                    let actual = view.round_ood_answer(round_index, sample_index)?;
                    if actual.c0.as_u32() != expected.c0.as_u32()
                        || actual.c1.as_u32() != expected.c1.as_u32()
                    {
                        return Err("phase2 whir transcript round ood mismatch");
                    }
                    transcript_absorb_cm31(
                        &mut transcript,
                        b"phase2-whir/round-ood-answer",
                        actual,
                        &mut counters,
                    );
                    round_ood =
                        round_ood.add(actual.c0.add(actual.c1, &mut counters), &mut counters);
                }
                trace_phase_end(trace_mode, "ood");

                trace_phase_begin(trace_mode, "per_round_queries");
                verify_whir_pow_nonce(
                    &mut transcript,
                    b"phase2-whir/query-pow",
                    usize::from(round.pow_bits),
                    view.round_query_pow_nonce(round_index)?,
                    &mut counters,
                )?;
                let _ = transcript_sample(
                    &mut transcript,
                    b"phase2-whir/transcript-checkpoint",
                    &mut counters,
                );

                let accumulator = if reuse_queries {
                    evaluate_whir_round_queries_reuse(
                        &view,
                        query_plan,
                        config,
                        round_index,
                        &mut transcript,
                        &mut counters,
                    )?
                } else {
                    let mut accumulator = Qm31::from_base(M31::ZERO);
                    let query_round = transcript_round_as_query_round(round);
                    for query_index in 0..usize::from(round.query_count.max(1)) {
                        let position_digest = transcript_sample(
                            &mut transcript,
                            b"phase2-whir/query-position",
                            &mut counters,
                        );
                        let expected_position =
                            u64::from_le_bytes(position_digest[0..8].try_into().unwrap());
                        let actual = view.round_query_record(round_index, query_index)?;
                        if actual.position != expected_position {
                            return Err("phase2 whir transcript query position mismatch");
                        }
                        let expected_record = build_whir_query_record(
                            query_plan,
                            round_index as u64,
                            query_index as u64,
                            query_round,
                            matches!(
                                config.query_precompute_mode,
                                WhirQueryPrecomputeMode::ProofCarriedRoundLocal
                            ),
                        );
                        if !whir_query_record_matches(expected_record, actual.inner, view.fold_mode)
                            || !whir_query_precomputed_matches(
                                expected_record,
                                actual.inner,
                                config.query_precompute_mode,
                            )
                        {
                            return Err("phase2 whir transcript query record mismatch");
                        }
                        let challenges = derive_whir_transcript_query_challenges(
                            transcript,
                            round_index as u64,
                            query_index as u64,
                            actual.position,
                            &mut counters,
                        );
                        let contribution = evaluate_whir_query_contribution(
                            actual.inner,
                            query_round,
                            challenges,
                            arithmetic,
                            extension,
                            view.fold_mode,
                            config.query_precompute_mode,
                            config.lift_policy,
                            &mut counters,
                        );
                        accumulator = accumulator.add(contribution, &mut counters);
                    }
                    accumulator
                };
                let merkle_digest = digest_synthetic_merkle_witness(
                    view.round_merkle_witness(round_index),
                    usize::from(round.merkle_depth.max(1)),
                    usize::from(round.query_count.max(1)),
                    config.merkle_proof_mode,
                    &mut counters,
                )?;
                trace_phase_end(trace_mode, "per_round_queries");

                trace_phase_begin(trace_mode, "folding");
                let combination = digest_word_to_m31(
                    &transcript_sample(
                        &mut transcript,
                        b"phase2-whir/combination-randomness",
                        &mut counters,
                    )[0..4],
                );
                claim = claim
                    .add(round_ood, &mut counters)
                    .add(digest_word_to_m31(&merkle_digest[0..4]), &mut counters)
                    .add(M31::new_lossy(fold_qm31(accumulator) as u64), &mut counters)
                    .add(combination, &mut counters);
                for sumcheck_round in 0..usize::from(
                    round
                        .sumcheck_rounds
                        .min(PHASE2_WHIR_MAX_SUMCHECK_ROUNDS as u16),
                ) {
                    let record = view.round_sumcheck_record(round_index, sumcheck_round)?;
                    transcript_absorb_m31(
                        &mut transcript,
                        b"phase2-whir/sumcheck-c0",
                        record.c0,
                        &mut counters,
                    );
                    transcript_absorb_m31(
                        &mut transcript,
                        b"phase2-whir/sumcheck-cinf",
                        record.c_inf,
                        &mut counters,
                    );
                    verify_whir_pow_nonce(
                        &mut transcript,
                        b"phase2-whir/sumcheck-pow",
                        usize::from(round.folding_pow_bits),
                        record.nonce,
                        &mut counters,
                    )?;
                    let challenge = digest_word_to_m31(
                        &transcript_sample(
                            &mut transcript,
                            b"phase2-whir/folding-randomness",
                            &mut counters,
                        )[0..4],
                    );
                    claim = whir_sumcheck_update(
                        claim,
                        record.c0,
                        record.c_inf,
                        challenge,
                        arithmetic,
                        &mut counters,
                    );
                }
                trace_phase_end(trace_mode, "folding");
                digest ^= claim.as_u32().rotate_left((repetition + 1) % 31) ^ tail_checksum;
            }
            WhirTranscriptDiagnosticStage::FinalRound => {
                trace_phase_begin(trace_mode, "final_round");
                let final_coeff_count = view.final_coeff_count();
                let mut final_coeffs = [M31::ZERO; PHASE2_WHIR_MAX_FINAL_COEFFS];
                for index in 0..final_coeff_count {
                    let actual = view.final_coeff(index)?;
                    final_coeffs[index] = actual;
                    transcript_absorb_m31(
                        &mut transcript,
                        b"phase2-whir/final-coeff",
                        actual,
                        &mut counters,
                    );
                }
                verify_whir_pow_nonce(
                    &mut transcript,
                    b"phase2-whir/final-pow",
                    usize::from(view.final_pow_bits),
                    view.final_pow_nonce()?,
                    &mut counters,
                )?;
                let mut final_claim = claim;
                for query_index in 0..view.final_query_count() {
                    let position_digest = transcript_sample(
                        &mut transcript,
                        b"phase2-whir/final-query-position",
                        &mut counters,
                    );
                    let expected_position =
                        u32::from_le_bytes(position_digest[0..4].try_into().unwrap());
                    let record = view.final_query_record(query_index)?;
                    if record.position != expected_position {
                        return Err("phase2 whir transcript final query position mismatch");
                    }
                    let point = final_query_point(expected_position, claim);
                    let expected_value = horner_eval_slice_m31(
                        &final_coeffs[..final_coeff_count],
                        point,
                        arithmetic,
                        &mut counters,
                    );
                    if record.value.as_u32() != expected_value.as_u32() {
                        return Err("phase2 whir transcript final query value mismatch");
                    }
                    final_claim = final_claim.add(
                        record.value.mul(
                            point.add(M31::ONE, &mut counters),
                            arithmetic,
                            &mut counters,
                        ),
                        &mut counters,
                    );
                }
                let final_merkle = digest_synthetic_merkle_witness(
                    view.final_merkle_witness(),
                    usize::from(view.final_merkle_depth.max(1)),
                    view.final_query_count().max(1),
                    config.merkle_proof_mode,
                    &mut counters,
                )?;
                final_claim =
                    final_claim.add(digest_word_to_m31(&final_merkle[0..4]), &mut counters);
                for round in 0..view.final_sumcheck_round_count() {
                    let record = view.final_sumcheck_record(round)?;
                    transcript_absorb_m31(
                        &mut transcript,
                        b"phase2-whir/final-sumcheck-c0",
                        record.c0,
                        &mut counters,
                    );
                    transcript_absorb_m31(
                        &mut transcript,
                        b"phase2-whir/final-sumcheck-cinf",
                        record.c_inf,
                        &mut counters,
                    );
                    verify_whir_pow_nonce(
                        &mut transcript,
                        b"phase2-whir/final-sumcheck-pow",
                        usize::from(view.final_folding_pow_bits),
                        record.nonce,
                        &mut counters,
                    )?;
                    let challenge = digest_word_to_m31(
                        &transcript_sample(
                            &mut transcript,
                            b"phase2-whir/final-folding-randomness",
                            &mut counters,
                        )[0..4],
                    );
                    final_claim = whir_sumcheck_update(
                        final_claim,
                        record.c0,
                        record.c_inf,
                        challenge,
                        arithmetic,
                        &mut counters,
                    );
                }
                let deferred = build_whir_deferred_evals(view.plan(), final_claim);
                for (index, expected) in deferred.iter().enumerate() {
                    let actual = view.deferred_eval(index)?;
                    if actual.as_u32() != expected.as_u32() {
                        return Err("phase2 whir transcript deferred eval mismatch");
                    }
                }
                trace_phase_end(trace_mode, "final_round");
                digest ^= final_claim.as_u32().rotate_left((repetition + 1) % 31) ^ tail_checksum;
            }
        }
    }

    Ok(Phase2VerifierOutcome {
        digest,
        counters,
        uses_heap: false,
    })
}

trait M31Kernel {
    fn mul_pair(lhs: u32, rhs: u32) -> u32;
    fn reduce_sum(sum: u64) -> u32;
}

struct ReferenceKernel;
struct DirectKernel;
struct DirectLazyKernel;
struct MontgomeryKernel;
struct BarrettKernel;

impl M31Kernel for ReferenceKernel {
    fn mul_pair(lhs: u32, rhs: u32) -> u32 {
        m31_reduce_reference(lhs as u64 * rhs as u64)
    }
    fn reduce_sum(sum: u64) -> u32 {
        m31_reduce_reference(sum)
    }
}

impl M31Kernel for DirectKernel {
    fn mul_pair(lhs: u32, rhs: u32) -> u32 {
        m31_reduce_direct(lhs as u64 * rhs as u64)
    }
    fn reduce_sum(sum: u64) -> u32 {
        m31_reduce_direct(sum)
    }
}

impl M31Kernel for DirectLazyKernel {
    fn mul_pair(lhs: u32, rhs: u32) -> u32 {
        m31_reduce_direct(lhs as u64 * rhs as u64)
    }
    fn reduce_sum(sum: u64) -> u32 {
        m31_reduce_direct(sum)
    }
}

impl M31Kernel for MontgomeryKernel {
    fn mul_pair(lhs: u32, rhs: u32) -> u32 {
        m31_mul_montgomery(lhs, rhs)
    }
    fn reduce_sum(sum: u64) -> u32 {
        m31_reduce_direct(sum)
    }
}

impl M31Kernel for BarrettKernel {
    fn mul_pair(lhs: u32, rhs: u32) -> u32 {
        m31_reduce_barrett(lhs as u64 * rhs as u64)
    }
    fn reduce_sum(sum: u64) -> u32 {
        m31_reduce_barrett(sum)
    }
}

fn run_m31_workload<K: M31Kernel>(
    config: Phase2ArithmeticConfig,
    workload: ArithmeticWorkloadId,
    iterations: u32,
    counters: &mut Phase2Counters,
) -> u32 {
    let mut state = 0x6a09_e667_u32;
    let mut acc = 0_u32;
    for round in 0..iterations {
        let a = sample_m31(round as u64 ^ 0x1111_2222_3333_4444);
        let b = sample_m31(round as u64 ^ 0x5555_6666_7777_8888);
        let c = sample_m31(round as u64 ^ 0x9999_aaaa_bbbb_cccc);
        let x = sample_m31(round as u64 ^ 0xdead_beef_cafe_f00d);
        let value = match workload {
            ArithmeticWorkloadId::Mul => {
                bump_counter!(counters, m31_mul_ops, 1);
                K::mul_pair(a.as_u32(), b.as_u32())
            }
            ArithmeticWorkloadId::Square => {
                bump_counter!(counters, m31_square_ops, 1);
                bump_counter!(counters, m31_mul_ops, 1);
                K::mul_pair(a.as_u32(), a.as_u32())
            }
            ArithmeticWorkloadId::MulAdd => {
                bump_counter!(counters, m31_mul_ops, 1);
                bump_counter!(counters, m31_add_ops, 1);
                let sum = a.as_u32() as u64 * b.as_u32() as u64 + c.as_u32() as u64;
                match config.lazy_reduction_mode {
                    LazyReductionMode::Batch4
                        if matches!(config.kernel_id, ArithmeticKernelId::DirectM31Lazy) =>
                    {
                        K::reduce_sum(sum)
                    }
                    _ => m31_reduce_direct(
                        K::mul_pair(a.as_u32(), b.as_u32()) as u64 + c.as_u32() as u64,
                    ),
                }
            }
            ArithmeticWorkloadId::InnerProduct4 => {
                let inputs = [(a, b), (b, c), (c, x), (x, a)];
                let mut sum = 0_u64;
                for &(lhs, rhs) in &inputs {
                    bump_counter!(counters, m31_mul_ops, 1);
                    sum = sum.saturating_add(lhs.as_u32() as u64 * rhs.as_u32() as u64);
                }
                bump_counter!(counters, m31_add_ops, 3);
                match config.lazy_reduction_mode {
                    LazyReductionMode::Batch4
                        if matches!(config.kernel_id, ArithmeticKernelId::DirectM31Lazy) =>
                    {
                        K::reduce_sum(sum)
                    }
                    _ => K::reduce_sum(sum),
                }
            }
            ArithmeticWorkloadId::Horner4 => {
                let coeffs = [a, b, c, x];
                let mut horner = M31::ZERO;
                for coeff in coeffs {
                    bump_counter!(counters, m31_mul_ops, 1);
                    let prod = K::mul_pair(horner.as_u32(), x.as_u32());
                    bump_counter!(counters, m31_add_ops, 1);
                    horner = M31::new_lossy(prod as u64 + coeff.as_u32() as u64);
                }
                horner.as_u32()
            }
            ArithmeticWorkloadId::DenominatorChain4 => {
                let terms = [a, b, c, x];
                let mut product = M31::ONE;
                for term in terms {
                    let shifted = term.add(M31::TWO, counters);
                    bump_counter!(counters, m31_mul_ops, 1);
                    product =
                        M31::new_lossy(K::mul_pair(product.as_u32(), shifted.as_u32()) as u64);
                }
                product.as_u32()
            }
            ArithmeticWorkloadId::SkeletonFoldStep => {
                let v00 = a;
                let v10 = b;
                let v01 = c;
                let v11 = x;
                let r0 = sample_m31(round as u64 ^ 0x0101_0101_0101_0101);
                let r1 = sample_m31(round as u64 ^ 0x0202_0202_0202_0202);
                let cx = v10.sub(v00, counters);
                let cy = v01.sub(v00, counters);
                let cxy = v11.sub(v10, counters).sub(v01, counters).add(v00, counters);
                let cross = M31::new_lossy(K::mul_pair(r0.as_u32(), r1.as_u32()) as u64);
                let mut total = v00;
                let rx = M31::new_lossy(K::mul_pair(r0.as_u32(), cx.as_u32()) as u64);
                let ry = M31::new_lossy(K::mul_pair(r1.as_u32(), cy.as_u32()) as u64);
                let rxy = M31::new_lossy(K::mul_pair(cross.as_u32(), cxy.as_u32()) as u64);
                total = total.add(rx, counters).add(ry, counters).add(rxy, counters);
                total.as_u32()
            }
        };
        state ^= value.rotate_left((round % 17) + 1);
        acc ^= value;
    }
    state ^ acc
}

fn skeleton_extension_accumulator(
    a: Qm31,
    b: Qm31,
    c: Cm31,
    config: Phase2ExtensionConfig,
    counters: &mut Phase2Counters,
) -> Qm31 {
    let t0 = a.mul(b, config, counters);
    let t1 = a.square(config, counters);
    let t2 = t0.add(t1, counters);
    let t3 = t2.mul_const(c, config, counters);
    t3.sub(b.inv(config, counters), counters)
}

struct Phase2ProofView<'a> {
    bytes: &'a [u8],
    fold_mode: WhirFoldMode,
    query_count: u16,
    fold_arity: u16,
    merkle_depth: u16,
    merkle_paths: u16,
    statement_digest: [u8; 32],
    query_section_offset: usize,
    query_record_words: usize,
}

impl<'a> Phase2ProofView<'a> {
    fn parse(bytes: &'a [u8]) -> Result<Self, &'static str> {
        if bytes.len() < 68 {
            return Err("phase2 proof too short");
        }
        if bytes[0..4] != PHASE2_PROOF_MAGIC {
            return Err("phase2 proof magic mismatch");
        }
        let version = read_u16(bytes, 4)?;
        if version != PHASE2_PROOF_VERSION {
            return Err("phase2 proof version mismatch");
        }
        let fold_mode = match read_u16(bytes, 6)? {
            0 => WhirFoldMode::RawFibers,
            1 => WhirFoldMode::LocalInterpolant,
            _ => return Err("phase2 fold mode mismatch"),
        };
        let query_count = read_u16(bytes, 8)?;
        let fold_arity = read_u16(bytes, 10)?;
        let merkle_depth = read_u16(bytes, 12)?;
        let merkle_paths = read_u16(bytes, 14)?;
        let target_proof_bytes = read_u32(bytes, 16)? as usize;
        if target_proof_bytes > bytes.len() {
            return Err("phase2 target proof bytes mismatch");
        }
        let mut statement_digest = [0_u8; 32];
        statement_digest.copy_from_slice(&bytes[36..68]);
        Ok(Self {
            bytes,
            fold_mode,
            query_count,
            fold_arity,
            merkle_depth,
            merkle_paths,
            statement_digest,
            query_section_offset: 68,
            query_record_words: match fold_mode {
                WhirFoldMode::RawFibers => RAW_QUERY_RECORD_WORDS,
                WhirFoldMode::LocalInterpolant => LOCAL_QUERY_RECORD_WORDS,
            },
        })
    }

    fn query_record(&self, query_index: usize) -> Result<QueryRecord, &'static str> {
        if query_index >= self.query_count as usize {
            return Err("query index out of range");
        }
        let word_offset = self.query_section_offset
            + (query_index * self.query_record_words * core::mem::size_of::<u32>());
        let payload_offset = word_offset + 6 * core::mem::size_of::<u32>();
        let x = Cm31::new(
            checked_m31(read_u32(self.bytes, word_offset)?)?,
            checked_m31(read_u32(self.bytes, word_offset + 4)?)?,
        );
        let z0 = Cm31::new(
            checked_m31(read_u32(self.bytes, word_offset + 8)?)?,
            checked_m31(read_u32(self.bytes, word_offset + 12)?)?,
        );
        let z1 = Cm31::new(
            checked_m31(read_u32(self.bytes, word_offset + 16)?)?,
            checked_m31(read_u32(self.bytes, word_offset + 20)?)?,
        );
        let mut fold_payload = [M31::ZERO; 4];
        for (index, slot) in fold_payload.iter_mut().enumerate() {
            *slot = checked_m31(read_u32(
                self.bytes,
                payload_offset + index * core::mem::size_of::<u32>(),
            )?)?;
        }
        let _ = self.fold_arity;
        Ok(QueryRecord {
            x,
            z0,
            z1,
            fold_payload,
        })
    }

    fn tail_bytes(&self) -> &'a [u8] {
        let query_bytes =
            self.query_count as usize * self.query_record_words * core::mem::size_of::<u32>();
        let tail_offset = self.query_section_offset + query_bytes;
        if tail_offset >= self.bytes.len() {
            &[]
        } else {
            &self.bytes[tail_offset..]
        }
    }
}

struct Phase2WhirQueryView<'a> {
    bytes: &'a [u8],
    fold_mode: WhirFoldMode,
    round_count: usize,
    rounds: [Phase2WhirRoundPlan; PHASE2_WHIR_MAX_ROUNDS],
    statement_digest: [u8; 32],
    query_section_offset: usize,
    round_query_offsets: [usize; PHASE2_WHIR_MAX_ROUNDS],
}

impl<'a> Phase2WhirQueryView<'a> {
    fn parse(bytes: &'a [u8]) -> Result<Self, &'static str> {
        const HEADER_BYTES: usize = 62;
        if bytes.len() < HEADER_BYTES {
            return Err("phase2 whir proof too short");
        }
        if bytes[0..4] != PHASE2_WHIR_QUERY_MAGIC {
            return Err("phase2 whir proof magic mismatch");
        }
        let version = read_u16(bytes, 4)?;
        if version != PHASE2_WHIR_QUERY_VERSION {
            return Err("phase2 whir proof version mismatch");
        }
        let fold_mode = match read_u16(bytes, 6)? {
            0 => WhirFoldMode::RawFibers,
            1 => WhirFoldMode::LocalInterpolant,
            _ => return Err("phase2 whir fold mode mismatch"),
        };
        let round_count = usize::from(read_u16(bytes, 8)?.clamp(1, PHASE2_WHIR_MAX_ROUNDS as u16));
        let target_proof_bytes = read_u32(bytes, 10)? as usize;
        if target_proof_bytes > bytes.len() {
            return Err("phase2 whir target proof bytes mismatch");
        }
        let mut statement_digest = [0_u8; 32];
        statement_digest.copy_from_slice(&bytes[30..62]);

        let round_section_offset = HEADER_BYTES;
        let query_section_offset =
            round_section_offset + round_count * PHASE2_WHIR_ROUND_PLAN_WORDS * 2;
        if query_section_offset > bytes.len() {
            return Err("phase2 whir round plan overflow");
        }

        let mut rounds = [Phase2WhirRoundPlan::default(); PHASE2_WHIR_MAX_ROUNDS];
        let mut round_query_offsets = [0_usize; PHASE2_WHIR_MAX_ROUNDS];
        let mut cursor = query_section_offset;
        for round_index in 0..round_count {
            let base = round_section_offset + round_index * PHASE2_WHIR_ROUND_PLAN_WORDS * 2;
            let round = Phase2WhirRoundPlan {
                query_count: read_u16(bytes, base)?,
                merkle_depth: read_u16(bytes, base + 2)?,
                ood_samples: read_u16(bytes, base + 4)?,
                opening_count: read_u16(bytes, base + 6)?,
                selector_count: read_u16(bytes, base + 8)?,
            };
            rounds[round_index] = round;
            round_query_offsets[round_index] = cursor;
            let query_bytes = usize::from(round.query_count.max(1))
                * PHASE2_WHIR_QUERY_RECORD_WORDS
                * core::mem::size_of::<u32>();
            cursor = cursor
                .checked_add(query_bytes)
                .ok_or("phase2 whir query section overflow")?;
            if cursor > target_proof_bytes {
                return Err("phase2 whir query section exceeds target proof bytes");
            }
        }

        Ok(Self {
            bytes,
            fold_mode,
            round_count,
            rounds,
            statement_digest,
            query_section_offset,
            round_query_offsets,
        })
    }

    fn round_plan(&self, round_index: usize) -> Phase2WhirRoundPlan {
        self.rounds[round_index]
    }

    fn query_record(
        &self,
        round_index: usize,
        query_index: usize,
    ) -> Result<WhirQueryRecord, &'static str> {
        if round_index >= self.round_count {
            return Err("phase2 whir round index out of range");
        }
        let round = self.round_plan(round_index);
        if query_index >= usize::from(round.query_count.max(1)) {
            return Err("phase2 whir query index out of range");
        }
        let word_offset = self.round_query_offsets[round_index]
            + (query_index * PHASE2_WHIR_QUERY_RECORD_WORDS * core::mem::size_of::<u32>());
        let mut cursor = word_offset;
        let x = read_cm31(self.bytes, &mut cursor)?;

        let mut openings = [Cm31::from_base(M31::ZERO); PHASE2_WHIR_MAX_OPENING_TERMS];
        for slot in &mut openings {
            *slot = read_cm31(self.bytes, &mut cursor)?;
        }
        let mut selectors = [Cm31::from_base(M31::ZERO); PHASE2_WHIR_SELECTOR_TERMS];
        for slot in &mut selectors {
            *slot = read_cm31(self.bytes, &mut cursor)?;
        }
        let mut fold_payload = [M31::ZERO; PHASE2_WHIR_FOLD_VALUES];
        for slot in &mut fold_payload {
            *slot = checked_m31(read_u32(self.bytes, cursor)?)?;
            cursor += 4;
        }
        let mut numerator_coeffs = [M31::ZERO; PHASE2_WHIR_NUMERATOR_COEFFS];
        for slot in &mut numerator_coeffs {
            *slot = checked_m31(read_u32(self.bytes, cursor)?)?;
            cursor += 4;
        }
        let mut selector_weights = [M31::ZERO; PHASE2_WHIR_SELECTOR_TERMS];
        for slot in &mut selector_weights {
            *slot = checked_m31(read_u32(self.bytes, cursor)?)?;
            cursor += 4;
        }

        Ok(WhirQueryRecord {
            x,
            openings,
            selectors,
            fold_payload,
            numerator_coeffs,
            selector_weights,
            precomputed: whir_zero_query_precomputed(),
        })
    }

    fn total_query_count(&self) -> usize {
        self.rounds
            .iter()
            .take(self.round_count)
            .map(|round| usize::from(round.query_count.max(1)))
            .sum()
    }

    fn total_merkle_levels(&self) -> usize {
        self.rounds
            .iter()
            .take(self.round_count)
            .map(|round| usize::from(round.query_count.max(1)) * usize::from(round.merkle_depth))
            .sum()
    }

    fn tail_bytes(&self) -> &'a [u8] {
        let query_bytes =
            self.total_query_count() * PHASE2_WHIR_QUERY_RECORD_WORDS * core::mem::size_of::<u32>();
        let tail_offset = self.query_section_offset + query_bytes;
        if tail_offset >= self.bytes.len() {
            &[]
        } else {
            &self.bytes[tail_offset..]
        }
    }
}

#[derive(Clone, Copy, Default)]
struct Phase2WhirTranscriptRoundOffsets {
    root_offset: usize,
    ood_offset: usize,
    query_pow_nonce_offset: usize,
    query_offset: usize,
    merkle_witness_offset: usize,
    merkle_witness_bytes: usize,
    sumcheck_offset: usize,
}

struct Phase2WhirTranscriptView<'a> {
    bytes: &'a [u8],
    fold_mode: WhirFoldMode,
    merkle_mode: MerkleProofMode,
    query_precompute_mode: WhirQueryPrecomputeMode,
    round_count: usize,
    rounds: [Phase2WhirTranscriptRoundPlan; PHASE2_WHIR_MAX_ROUNDS],
    statement_shape: Phase2WhirStatementShape,
    statement_digest: [u8; 32],
    commitment_ood_samples: u16,
    initial_sumcheck_rounds: u16,
    initial_folding_pow_bits: u16,
    final_query_count: u16,
    final_merkle_depth: u16,
    final_pow_bits: u16,
    final_sumcheck_rounds: u16,
    final_folding_pow_bits: u16,
    target_proof_bytes: usize,
    query_schedule_seed: u64,
    statement_seed: u64,
    commitment_root_offset: usize,
    commitment_ood_offset: usize,
    initial_sumcheck_offset: usize,
    round_offsets: [Phase2WhirTranscriptRoundOffsets; PHASE2_WHIR_MAX_ROUNDS],
    final_coeff_offset: usize,
    final_pow_nonce_offset: usize,
    final_query_offset: usize,
    final_merkle_witness_offset: usize,
    final_merkle_witness_bytes: usize,
    final_sumcheck_offset: usize,
    deferred_offset: usize,
}

impl<'a> Phase2WhirTranscriptView<'a> {
    fn parse(
        bytes: &'a [u8],
        query_precompute_mode: WhirQueryPrecomputeMode,
    ) -> Result<Self, &'static str> {
        const FIXED_HEADER_BYTES: usize = 80;
        const STATEMENT_SHAPE_BYTES: usize = 80;
        if bytes.len() < FIXED_HEADER_BYTES + STATEMENT_SHAPE_BYTES {
            return Err("phase2 whir transcript proof too short");
        }
        if bytes[0..4] != PHASE2_WHIR_TRANSCRIPT_MAGIC {
            return Err("phase2 whir transcript proof magic mismatch");
        }
        let version = read_u16(bytes, 4)?;
        if version != PHASE2_WHIR_TRANSCRIPT_VERSION {
            return Err("phase2 whir transcript proof version mismatch");
        }
        let fold_mode = match read_u16(bytes, 6)? {
            0 => WhirFoldMode::RawFibers,
            1 => WhirFoldMode::LocalInterpolant,
            _ => return Err("phase2 whir transcript fold mode mismatch"),
        };
        let merkle_mode = match read_u16(bytes, 8)? {
            0 => MerkleProofMode::SeparatePaths,
            1 => MerkleProofMode::MinimalSubtree,
            _ => return Err("phase2 whir transcript merkle mode mismatch"),
        };
        let round_count = usize::from(read_u16(bytes, 10)?.clamp(0, PHASE2_WHIR_MAX_ROUNDS as u16));
        let target_proof_bytes = read_u32(bytes, 12)? as usize;
        if target_proof_bytes > bytes.len() {
            return Err("phase2 whir transcript target proof bytes mismatch");
        }
        let mut statement_digest = [0_u8; 32];
        statement_digest.copy_from_slice(&bytes[32..64]);
        let (statement_shape, statement_shape_offset) = read_whir_statement_shape(bytes, 64)?;
        let commitment_ood_samples = read_u16(bytes, statement_shape_offset)?;
        let initial_sumcheck_rounds = read_u16(bytes, statement_shape_offset + 2)?;
        let initial_folding_pow_bits = read_u16(bytes, statement_shape_offset + 4)?;
        let final_query_count = read_u16(bytes, statement_shape_offset + 6)?;
        let final_merkle_depth = read_u16(bytes, statement_shape_offset + 8)?;
        let final_pow_bits = read_u16(bytes, statement_shape_offset + 10)?;
        let final_sumcheck_rounds = read_u16(bytes, statement_shape_offset + 12)?;
        let final_folding_pow_bits = read_u16(bytes, statement_shape_offset + 14)?;
        let round_section_offset = statement_shape_offset + 16;

        let mut rounds = [Phase2WhirTranscriptRoundPlan::default(); PHASE2_WHIR_MAX_ROUNDS];
        for round_index in 0..round_count {
            let base =
                round_section_offset + round_index * PHASE2_WHIR_TRANSCRIPT_ROUND_PLAN_WORDS * 2;
            rounds[round_index] = Phase2WhirTranscriptRoundPlan {
                query_count: read_u16(bytes, base)?,
                merkle_depth: read_u16(bytes, base + 2)?,
                ood_samples: read_u16(bytes, base + 4)?,
                opening_count: read_u16(bytes, base + 6)?,
                selector_count: read_u16(bytes, base + 8)?,
                pow_bits: read_u16(bytes, base + 10)?,
                sumcheck_rounds: read_u16(bytes, base + 12)?,
                folding_pow_bits: read_u16(bytes, base + 14)?,
            };
        }

        let mut cursor =
            round_section_offset + round_count * PHASE2_WHIR_TRANSCRIPT_ROUND_PLAN_WORDS * 2;
        let commitment_root_offset = cursor;
        cursor = cursor
            .checked_add(32)
            .ok_or("phase2 whir transcript section overflow")?;
        let commitment_ood_offset = cursor;
        cursor = cursor
            .checked_add(
                usize::from(commitment_ood_samples.min(PHASE2_WHIR_MAX_OOD_SAMPLES as u16)) * 8,
            )
            .ok_or("phase2 whir transcript commitment ood overflow")?;
        let initial_sumcheck_offset = cursor;
        cursor = cursor
            .checked_add(
                usize::from(initial_sumcheck_rounds.min(PHASE2_WHIR_MAX_SUMCHECK_ROUNDS as u16))
                    * PHASE2_WHIR_SUMCHECK_RECORD_WORDS
                    * 4,
            )
            .ok_or("phase2 whir transcript initial sumcheck overflow")?;

        let mut round_offsets =
            [Phase2WhirTranscriptRoundOffsets::default(); PHASE2_WHIR_MAX_ROUNDS];
        for round_index in 0..round_count {
            let round = rounds[round_index];
            round_offsets[round_index].root_offset = cursor;
            cursor = cursor
                .checked_add(32)
                .ok_or("phase2 whir transcript round root overflow")?;
            round_offsets[round_index].ood_offset = cursor;
            cursor = cursor
                .checked_add(
                    usize::from(round.ood_samples.min(PHASE2_WHIR_MAX_OOD_SAMPLES as u16)) * 8,
                )
                .ok_or("phase2 whir transcript round ood overflow")?;
            round_offsets[round_index].query_pow_nonce_offset = cursor;
            cursor = cursor
                .checked_add(8)
                .ok_or("phase2 whir transcript round pow overflow")?;
            round_offsets[round_index].query_offset = cursor;
            cursor = cursor
                .checked_add(
                    usize::from(round.query_count.max(1))
                        * whir_transcript_query_record_words(query_precompute_mode)
                        * 4,
                )
                .ok_or("phase2 whir transcript round query overflow")?;
            round_offsets[round_index].merkle_witness_offset = cursor;
            round_offsets[round_index].merkle_witness_bytes = synthetic_merkle_witness_bytes(
                usize::from(round.merkle_depth.max(1)),
                usize::from(round.query_count.max(1)),
                merkle_mode,
            );
            cursor = cursor
                .checked_add(round_offsets[round_index].merkle_witness_bytes)
                .ok_or("phase2 whir transcript round merkle witness overflow")?;
            round_offsets[round_index].sumcheck_offset = cursor;
            cursor = cursor
                .checked_add(
                    usize::from(
                        round
                            .sumcheck_rounds
                            .min(PHASE2_WHIR_MAX_SUMCHECK_ROUNDS as u16),
                    ) * PHASE2_WHIR_SUMCHECK_RECORD_WORDS
                        * 4,
                )
                .ok_or("phase2 whir transcript round sumcheck overflow")?;
        }

        let final_coeff_offset = cursor;
        let final_coeff_count = (1usize
            << usize::from(final_sumcheck_rounds.min(PHASE2_WHIR_MAX_SUMCHECK_ROUNDS as u16)))
        .min(PHASE2_WHIR_MAX_FINAL_COEFFS);
        cursor = cursor
            .checked_add(final_coeff_count * 4)
            .ok_or("phase2 whir transcript final coeff overflow")?;
        let final_pow_nonce_offset = cursor;
        cursor = cursor
            .checked_add(8)
            .ok_or("phase2 whir transcript final pow overflow")?;
        let final_query_offset = cursor;
        cursor = cursor
            .checked_add(
                usize::from(final_query_count.max(1)) * PHASE2_WHIR_FINAL_QUERY_RECORD_WORDS * 4,
            )
            .ok_or("phase2 whir transcript final query overflow")?;
        let final_merkle_witness_offset = cursor;
        let final_merkle_witness_bytes = synthetic_merkle_witness_bytes(
            usize::from(final_merkle_depth.max(1)),
            usize::from(final_query_count.max(1)),
            merkle_mode,
        );
        cursor = cursor
            .checked_add(final_merkle_witness_bytes)
            .ok_or("phase2 whir transcript final merkle witness overflow")?;
        let final_sumcheck_offset = cursor;
        cursor = cursor
            .checked_add(
                usize::from(final_sumcheck_rounds.min(PHASE2_WHIR_MAX_SUMCHECK_ROUNDS as u16))
                    * PHASE2_WHIR_SUMCHECK_RECORD_WORDS
                    * 4,
            )
            .ok_or("phase2 whir transcript final sumcheck overflow")?;
        let deferred_offset = cursor;
        cursor = cursor
            .checked_add(PHASE2_WHIR_DEFERRED_EVAL_WORDS * 4)
            .ok_or("phase2 whir transcript deferred overflow")?;
        if cursor > target_proof_bytes {
            return Err("phase2 whir transcript section exceeds target proof bytes");
        }

        Ok(Self {
            bytes,
            fold_mode,
            merkle_mode,
            query_precompute_mode,
            round_count,
            rounds,
            statement_shape,
            statement_digest,
            commitment_ood_samples,
            initial_sumcheck_rounds,
            initial_folding_pow_bits,
            final_query_count,
            final_merkle_depth,
            final_pow_bits,
            final_sumcheck_rounds,
            final_folding_pow_bits,
            target_proof_bytes,
            query_schedule_seed: u64::from_le_bytes(bytes[16..24].try_into().unwrap()),
            statement_seed: u64::from_le_bytes(bytes[24..32].try_into().unwrap()),
            commitment_root_offset,
            commitment_ood_offset,
            initial_sumcheck_offset,
            round_offsets,
            final_coeff_offset,
            final_pow_nonce_offset,
            final_query_offset,
            final_merkle_witness_offset,
            final_merkle_witness_bytes,
            final_sumcheck_offset,
            deferred_offset,
        })
    }

    fn plan(&self) -> Phase2WhirTranscriptPlan {
        Phase2WhirTranscriptPlan {
            round_count: self.round_count as u16,
            rounds: self.rounds,
            statement_shape: self.statement_shape,
            target_proof_bytes: self.target_proof_bytes as u32,
            query_schedule_seed: self.query_schedule_seed,
            statement_seed: self.statement_seed,
            commitment_ood_samples: self.commitment_ood_samples,
            initial_sumcheck_rounds: self.initial_sumcheck_rounds,
            initial_folding_pow_bits: self.initial_folding_pow_bits,
            final_query_count: self.final_query_count,
            final_merkle_depth: self.final_merkle_depth,
            final_pow_bits: self.final_pow_bits,
            final_sumcheck_rounds: self.final_sumcheck_rounds,
            final_folding_pow_bits: self.final_folding_pow_bits,
        }
    }

    fn commitment_root(&self) -> [u8; 32] {
        let mut root = [0_u8; 32];
        root.copy_from_slice(
            &self.bytes[self.commitment_root_offset..self.commitment_root_offset + 32],
        );
        root
    }

    fn commitment_ood_count(&self) -> usize {
        usize::from(
            self.commitment_ood_samples
                .min(PHASE2_WHIR_MAX_OOD_SAMPLES as u16),
        )
    }

    fn commitment_ood_answer(&self, sample_index: usize) -> Result<Cm31, &'static str> {
        let offset = self.commitment_ood_offset + sample_index * 8;
        let mut cursor = offset;
        read_cm31(self.bytes, &mut cursor)
    }

    fn initial_sumcheck_round_count(&self) -> usize {
        usize::from(
            self.initial_sumcheck_rounds
                .min(PHASE2_WHIR_MAX_SUMCHECK_ROUNDS as u16),
        )
    }

    fn initial_sumcheck_record(
        &self,
        round_index: usize,
    ) -> Result<WhirSumcheckRecord, &'static str> {
        let offset =
            self.initial_sumcheck_offset + round_index * PHASE2_WHIR_SUMCHECK_RECORD_WORDS * 4;
        read_whir_sumcheck_record(self.bytes, offset)
    }

    fn round_plan(&self, round_index: usize) -> Phase2WhirTranscriptRoundPlan {
        self.rounds[round_index]
    }

    fn round_root(&self, round_index: usize) -> Result<[u8; 32], &'static str> {
        let offset = self.round_offsets[round_index].root_offset;
        if offset + 32 > self.bytes.len() {
            return Err("phase2 whir transcript round root overflow");
        }
        let mut root = [0_u8; 32];
        root.copy_from_slice(&self.bytes[offset..offset + 32]);
        Ok(root)
    }

    fn round_ood_answer(
        &self,
        round_index: usize,
        sample_index: usize,
    ) -> Result<Cm31, &'static str> {
        let offset = self.round_offsets[round_index].ood_offset + sample_index * 8;
        let mut cursor = offset;
        read_cm31(self.bytes, &mut cursor)
    }

    fn round_query_pow_nonce(&self, round_index: usize) -> Result<u64, &'static str> {
        read_u64(
            self.bytes,
            self.round_offsets[round_index].query_pow_nonce_offset,
        )
    }

    fn round_query_record(
        &self,
        round_index: usize,
        query_index: usize,
    ) -> Result<WhirTranscriptQueryRecord, &'static str> {
        let base = self.round_offsets[round_index].query_offset
            + query_index * whir_transcript_query_record_words(self.query_precompute_mode) * 4;
        let position = read_u64(self.bytes, base)?;
        let inner = read_whir_query_record(self.bytes, base + 8, self.query_precompute_mode)?;
        Ok(WhirTranscriptQueryRecord { position, inner })
    }

    fn round_merkle_witness(&self, round_index: usize) -> &'a [u8] {
        let offset = self.round_offsets[round_index].merkle_witness_offset;
        let end = offset + self.round_offsets[round_index].merkle_witness_bytes;
        &self.bytes[offset..end]
    }

    fn round_sumcheck_record(
        &self,
        round_index: usize,
        sumcheck_index: usize,
    ) -> Result<WhirSumcheckRecord, &'static str> {
        let offset = self.round_offsets[round_index].sumcheck_offset
            + sumcheck_index * PHASE2_WHIR_SUMCHECK_RECORD_WORDS * 4;
        read_whir_sumcheck_record(self.bytes, offset)
    }

    fn final_coeff_count(&self) -> usize {
        (1usize
            << usize::from(
                self.final_sumcheck_rounds
                    .min(PHASE2_WHIR_MAX_SUMCHECK_ROUNDS as u16),
            ))
        .min(PHASE2_WHIR_MAX_FINAL_COEFFS)
    }

    fn final_coeff(&self, index: usize) -> Result<M31, &'static str> {
        checked_m31(read_u32(self.bytes, self.final_coeff_offset + index * 4)?)
    }

    fn final_pow_nonce(&self) -> Result<u64, &'static str> {
        read_u64(self.bytes, self.final_pow_nonce_offset)
    }

    fn final_query_count(&self) -> usize {
        usize::from(self.final_query_count.max(1))
    }

    fn final_query_record(&self, query_index: usize) -> Result<WhirFinalQueryRecord, &'static str> {
        let offset =
            self.final_query_offset + query_index * PHASE2_WHIR_FINAL_QUERY_RECORD_WORDS * 4;
        Ok(WhirFinalQueryRecord {
            position: read_u32(self.bytes, offset)?,
            value: checked_m31(read_u32(self.bytes, offset + 4)?)?,
        })
    }

    fn final_merkle_witness(&self) -> &'a [u8] {
        &self.bytes[self.final_merkle_witness_offset
            ..self.final_merkle_witness_offset + self.final_merkle_witness_bytes]
    }

    fn final_sumcheck_round_count(&self) -> usize {
        usize::from(
            self.final_sumcheck_rounds
                .min(PHASE2_WHIR_MAX_SUMCHECK_ROUNDS as u16),
        )
    }

    fn final_sumcheck_record(
        &self,
        round_index: usize,
    ) -> Result<WhirSumcheckRecord, &'static str> {
        let offset =
            self.final_sumcheck_offset + round_index * PHASE2_WHIR_SUMCHECK_RECORD_WORDS * 4;
        read_whir_sumcheck_record(self.bytes, offset)
    }

    fn deferred_eval(&self, index: usize) -> Result<M31, &'static str> {
        checked_m31(read_u32(self.bytes, self.deferred_offset + index * 4)?)
    }

    fn total_intermediate_query_count(&self) -> usize {
        self.rounds
            .iter()
            .take(self.round_count)
            .map(|round| usize::from(round.query_count.max(1)))
            .sum()
    }

    fn total_intermediate_merkle_levels(&self) -> usize {
        self.rounds
            .iter()
            .take(self.round_count)
            .map(|round| {
                usize::from(round.query_count.max(1)) * usize::from(round.merkle_depth.max(1))
            })
            .sum()
    }

    fn final_merkle_levels(&self) -> usize {
        usize::from(self.final_merkle_depth.max(1)) * self.final_query_count()
    }

    fn tail_bytes(&self) -> &'a [u8] {
        if self.deferred_offset + PHASE2_WHIR_DEFERRED_EVAL_WORDS * 4 >= self.bytes.len() {
            &[]
        } else {
            &self.bytes[self.deferred_offset + PHASE2_WHIR_DEFERRED_EVAL_WORDS * 4..]
        }
    }
}

#[derive(Clone, Copy)]
struct TranscriptChallenges {
    fold_r0: M31,
    fold_r1: M31,
    gamma: Qm31,
}

#[derive(Clone, Copy)]
struct WhirQueryChallenges {
    fold_r: [M31; 3],
    gamma: Qm31,
    beta: M31,
}

fn derive_challenges(transcript: [u8; 32], counters: &mut Phase2Counters) -> TranscriptChallenges {
    bump_counter!(counters, sha_calls, 2);
    bump_counter!(counters, sha_bytes, (TRANSCRIPT_DIGEST_BYTES * 2) as u64);
    let first = hashv(&[&transcript, b"fold"]).to_bytes();
    let second = hashv(&[&transcript, b"gamma"]).to_bytes();
    TranscriptChallenges {
        fold_r0: digest_word_to_m31(&first[0..4]),
        fold_r1: digest_word_to_m31(&first[4..8]),
        gamma: seeded_qm31(u64::from_le_bytes(second[0..8].try_into().unwrap())),
    }
}

fn derive_whir_query_challenges(
    transcript: [u8; 32],
    counters: &mut Phase2Counters,
) -> WhirQueryChallenges {
    bump_counter!(counters, sha_calls, 2);
    bump_counter!(counters, sha_bytes, (TRANSCRIPT_DIGEST_BYTES * 2) as u64);
    let first = hashv(&[&transcript, b"whir-fold"]).to_bytes();
    let second = hashv(&[&transcript, b"whir-mix"]).to_bytes();
    WhirQueryChallenges {
        fold_r: [
            digest_word_to_m31(&first[0..4]),
            digest_word_to_m31(&first[4..8]),
            digest_word_to_m31(&first[8..12]),
        ],
        beta: digest_word_to_m31(&first[12..16]),
        gamma: seeded_qm31(u64::from_le_bytes(second[0..8].try_into().unwrap())),
    }
}

fn transcript_material(
    statement_digest: [u8; 32],
    repetition: u32,
    query_index: usize,
) -> [u8; 32] {
    hashv(&[
        &statement_digest,
        &repetition.to_le_bytes(),
        &(query_index as u32).to_le_bytes(),
    ])
    .to_bytes()
}

fn whir_query_transcript_material(
    statement_digest: [u8; 32],
    repetition: u32,
    round_index: usize,
    query_index: usize,
    ood_samples: u16,
) -> [u8; 32] {
    hashv(&[
        &statement_digest,
        &repetition.to_le_bytes(),
        &(round_index as u32).to_le_bytes(),
        &(query_index as u32).to_le_bytes(),
        &ood_samples.to_le_bytes(),
    ])
    .to_bytes()
}

fn phase2_whir_transcript_statement_digest(plan: Phase2WhirTranscriptPlan) -> [u8; 32] {
    let base = phase2_whir_statement_digest(Phase2WhirQueryPlan {
        round_count: (usize::from(plan.round_count) + 1) as u16,
        rounds: transcript_plan_as_query_plan(plan).rounds,
        statement_shape: plan.statement_shape,
        target_proof_bytes: plan.target_proof_bytes,
        query_schedule_seed: plan.query_schedule_seed,
        statement_seed: plan.statement_seed,
    });
    hashv(&[
        &base,
        &plan.commitment_ood_samples.to_le_bytes(),
        &plan.initial_sumcheck_rounds.to_le_bytes(),
        &plan.initial_folding_pow_bits.to_le_bytes(),
        &plan.final_query_count.to_le_bytes(),
        &plan.final_merkle_depth.to_le_bytes(),
        &plan.final_pow_bits.to_le_bytes(),
        &plan.final_sumcheck_rounds.to_le_bytes(),
        &plan.final_folding_pow_bits.to_le_bytes(),
    ])
    .to_bytes()
}

fn phase2_whir_transcript_setup_state(
    plan: Phase2WhirTranscriptPlan,
    fold_mode: WhirFoldMode,
    statement_digest: [u8; 32],
    counters: &mut Phase2Counters,
) -> [u8; 32] {
    let mut state = transcript_hash(&[b"phase2-whir-transcript-v1", &statement_digest], counters);
    transcript_absorb_bytes(
        &mut state,
        b"phase2-whir/fold-mode",
        &(fold_mode as u16).to_le_bytes(),
        counters,
    );
    transcript_absorb_bytes(
        &mut state,
        b"phase2-whir/round-count",
        &plan.round_count.to_le_bytes(),
        counters,
    );
    transcript_absorb_bytes(
        &mut state,
        b"phase2-whir/query-seed",
        &plan.query_schedule_seed.to_le_bytes(),
        counters,
    );
    transcript_absorb_bytes(
        &mut state,
        b"phase2-whir/statement-seed",
        &plan.statement_seed.to_le_bytes(),
        counters,
    );
    for value in [
        plan.commitment_ood_samples,
        plan.initial_sumcheck_rounds,
        plan.initial_folding_pow_bits,
        plan.final_query_count,
        plan.final_merkle_depth,
        plan.final_pow_bits,
        plan.final_sumcheck_rounds,
        plan.final_folding_pow_bits,
    ] {
        transcript_absorb_bytes(
            &mut state,
            b"phase2-whir/param",
            &value.to_le_bytes(),
            counters,
        );
    }
    for round in plan.rounds.iter().take(usize::from(plan.round_count)) {
        for value in [
            round.query_count,
            round.merkle_depth,
            round.ood_samples,
            round.opening_count,
            round.selector_count,
            round.pow_bits,
            round.sumcheck_rounds,
            round.folding_pow_bits,
        ] {
            transcript_absorb_bytes(
                &mut state,
                b"phase2-whir/round-param",
                &value.to_le_bytes(),
                counters,
            );
        }
    }
    write_statement_shape_into_transcript(&mut state, plan.statement_shape, counters);
    state
}

fn write_statement_shape_into_transcript(
    state: &mut [u8; 32],
    shape: Phase2WhirStatementShape,
    counters: &mut Phase2Counters,
) {
    for value in [
        shape.spends,
        shape.outputs,
        shape.note_tree_depth,
        shape.note_openings_per_spend,
        shape.nullifier_hashes_per_spend,
        shape.note_commitments_per_output,
        shape.amount_range_checks_64,
        shape.ownership_checks,
        shape.balance_constraints,
        shape.lookup_arguments,
        shape.boundary_constraint_groups,
        shape.application_merkle_paths,
        shape.application_hash_gadgets,
        shape.evaluation_domain_log2,
        shape.merkle_rows_per_level,
        shape.nullifier_hash_rows,
        shape.note_commitment_rows,
        shape.range_check_rows,
        shape.ownership_rows,
        shape.balance_rows,
        shape.lookup_rows,
        shape.misc_rows,
    ] {
        transcript_absorb_bytes(
            state,
            b"phase2-whir/shape-u16",
            &value.to_le_bytes(),
            counters,
        );
    }
    transcript_absorb_bytes(
        state,
        b"phase2-whir/shape-total-rows",
        &shape.total_rows.to_le_bytes(),
        counters,
    );
    for row in shape.row_breakdown {
        transcript_absorb_bytes(
            state,
            b"phase2-whir/shape-row",
            &row.to_le_bytes(),
            counters,
        );
    }
}

fn transcript_hash(parts: &[&[u8]], counters: &mut Phase2Counters) -> [u8; 32] {
    bump_counter!(counters, sha_calls, 1);
    bump_counter!(
        counters,
        sha_bytes,
        parts.iter().map(|part| part.len() as u64).sum::<u64>()
    );
    hashv(parts).to_bytes()
}

fn transcript_absorb_bytes(
    state: &mut [u8; 32],
    label: &[u8],
    bytes: &[u8],
    counters: &mut Phase2Counters,
) {
    let current = *state;
    *state = transcript_hash(&[&current, label, bytes], counters);
}

fn transcript_absorb_m31(
    state: &mut [u8; 32],
    label: &[u8],
    value: M31,
    counters: &mut Phase2Counters,
) {
    transcript_absorb_bytes(state, label, &value.as_u32().to_le_bytes(), counters);
}

fn transcript_absorb_cm31(
    state: &mut [u8; 32],
    label: &[u8],
    value: Cm31,
    counters: &mut Phase2Counters,
) {
    let current = *state;
    let lhs = transcript_hash(
        &[&current, label, &value.c0.as_u32().to_le_bytes()],
        counters,
    );
    *state = transcript_hash(&[&lhs, &value.c1.as_u32().to_le_bytes()], counters);
}

fn transcript_sample(
    state: &mut [u8; 32],
    label: &[u8],
    counters: &mut Phase2Counters,
) -> [u8; 32] {
    let current = *state;
    *state = transcript_hash(&[&current, b"sample", label], counters);
    *state
}

fn phase2_whir_transcript_round_root(
    plan: Phase2WhirTranscriptPlan,
    round_index: u64,
    claim: M31,
) -> [u8; 32] {
    hashv(&[
        &phase2_whir_transcript_statement_digest(plan),
        &round_index.to_le_bytes(),
        &claim.as_u32().to_le_bytes(),
    ])
    .to_bytes()
}

fn build_whir_transcript_ood_answer(
    plan: Phase2WhirTranscriptPlan,
    round_index: u64,
    sample_index: u64,
    point_digest: [u8; 32],
    claim: M31,
) -> Cm31 {
    let mut point_lo = [0_u8; 8];
    point_lo.copy_from_slice(&point_digest[0..8]);
    let mut point_hi = [0_u8; 8];
    point_hi.copy_from_slice(&point_digest[8..16]);
    let seed = mix64(
        plan.query_schedule_seed
            ^ plan.statement_seed.rotate_left(7)
            ^ round_index.rotate_left(19)
            ^ sample_index.rotate_left(31)
            ^ claim.as_u32() as u64
            ^ u64::from_le_bytes(point_lo)
            ^ u64::from_le_bytes(point_hi).rotate_left(11),
    );
    phase2_whir_semantic_cm31(
        transcript_plan_as_query_plan(plan),
        0x7100 ^ round_index.rotate_left(9),
        round_index,
        sample_index,
        claim.as_u32() as u64,
        [seed, point_digest[0] as u64, point_digest[9] as u64],
    )
}

fn build_whir_sumcheck_record(
    statement_digest: [u8; 32],
    claim: M31,
    section_tag: u64,
    round_index: u64,
) -> WhirSumcheckRecord {
    let mut lo = [0_u8; 8];
    lo.copy_from_slice(&statement_digest[0..8]);
    let seed = mix64(
        u64::from_le_bytes(lo)
            ^ section_tag.rotate_left(17)
            ^ round_index.rotate_left(33)
            ^ claim.as_u32() as u64,
    );
    WhirSumcheckRecord {
        c0: sample_m31(seed),
        c_inf: sample_nonzero_m31(seed.rotate_left(13)),
        nonce: 0,
    }
}

fn build_whir_pow_nonce(
    transcript: &mut [u8; 32],
    label: &[u8],
    bits: usize,
    counters: &mut Phase2Counters,
) -> u64 {
    if bits == 0 {
        return 0;
    }
    let challenge = transcript_sample(transcript, label, counters);
    let anchor = transcript_hash(&[&challenge, b"pow-anchor"], counters);
    let nonce = u64::from_le_bytes(anchor[0..8].try_into().unwrap());
    transcript_absorb_bytes(transcript, b"pow-nonce", &nonce.to_le_bytes(), counters);
    nonce
}

fn verify_whir_pow_nonce(
    transcript: &mut [u8; 32],
    label: &[u8],
    bits: usize,
    nonce: u64,
    counters: &mut Phase2Counters,
) -> Result<(), &'static str> {
    if bits == 0 {
        return Ok(());
    }
    let challenge = transcript_sample(transcript, label, counters);
    let anchor = transcript_hash(&[&challenge, b"pow-anchor"], counters);
    let anchor_word = u64::from_le_bytes(anchor[0..8].try_into().unwrap());
    let mask = if bits >= u64::BITS as usize {
        u64::MAX
    } else {
        (1_u64 << bits) - 1
    };
    if ((anchor_word ^ nonce) & mask) != 0 {
        return Err("phase2 whir transcript pow witness mismatch");
    }
    transcript_absorb_bytes(transcript, b"pow-nonce", &nonce.to_le_bytes(), counters);
    Ok(())
}

fn transcript_round_as_query_round(round: Phase2WhirTranscriptRoundPlan) -> Phase2WhirRoundPlan {
    Phase2WhirRoundPlan {
        query_count: round.query_count,
        merkle_depth: round.merkle_depth,
        ood_samples: round.ood_samples,
        opening_count: round.opening_count,
        selector_count: round.selector_count,
    }
}

fn transcript_plan_as_query_plan(plan: Phase2WhirTranscriptPlan) -> Phase2WhirQueryPlan {
    let mut rounds = [Phase2WhirRoundPlan::default(); PHASE2_WHIR_MAX_ROUNDS];
    for (dst, src) in rounds.iter_mut().zip(
        plan.rounds
            .iter()
            .map(|round| transcript_round_as_query_round(*round)),
    ) {
        *dst = src;
    }
    Phase2WhirQueryPlan {
        round_count: plan.round_count,
        rounds,
        statement_shape: plan.statement_shape,
        target_proof_bytes: plan.target_proof_bytes,
        query_schedule_seed: plan.query_schedule_seed,
        statement_seed: plan.statement_seed,
    }
}

fn derive_whir_transcript_query_challenges(
    transcript_state: [u8; 32],
    round_index: u64,
    query_index: u64,
    position: u64,
    counters: &mut Phase2Counters,
) -> WhirQueryChallenges {
    let first = transcript_hash(
        &[
            &transcript_state,
            b"phase2-whir/query-challenges",
            &round_index.to_le_bytes(),
            &query_index.to_le_bytes(),
            &position.to_le_bytes(),
        ],
        counters,
    );
    let second = transcript_hash(&[&first, b"phase2-whir/query-mix"], counters);
    WhirQueryChallenges {
        fold_r: [
            digest_word_to_m31(&first[0..4]),
            digest_word_to_m31(&first[4..8]),
            digest_word_to_m31(&first[8..12]),
        ],
        beta: digest_word_to_m31(&first[12..16]),
        gamma: seeded_qm31(u64::from_le_bytes(second[0..8].try_into().unwrap())),
    }
}

fn evaluate_whir_query_contribution(
    record: WhirQueryRecord,
    round: Phase2WhirRoundPlan,
    challenges: WhirQueryChallenges,
    arithmetic: Phase2ArithmeticConfig,
    extension: Phase2ExtensionConfig,
    fold_mode: WhirFoldMode,
    precompute_mode: WhirQueryPrecomputeMode,
    lift_policy: LiftPolicy,
    counters: &mut Phase2Counters,
) -> Qm31 {
    let term = build_whir_query_term(
        record,
        round,
        challenges,
        arithmetic,
        extension,
        fold_mode,
        precompute_mode,
        counters,
    );
    let denom_inv = term.combined_denom.inv(extension, counters);
    finish_whir_query_term(
        term,
        denom_inv,
        arithmetic,
        extension,
        lift_policy,
        counters,
    )
}

fn build_whir_query_term(
    record: WhirQueryRecord,
    round: Phase2WhirRoundPlan,
    challenges: WhirQueryChallenges,
    arithmetic: Phase2ArithmeticConfig,
    extension: Phase2ExtensionConfig,
    fold_mode: WhirFoldMode,
    precompute_mode: WhirQueryPrecomputeMode,
    counters: &mut Phase2Counters,
) -> WhirQueryTerm {
    let selector_count = usize::from(
        round
            .selector_count
            .clamp(1, PHASE2_WHIR_SELECTOR_TERMS as u16),
    );
    let opening_count = usize::from(
        round
            .opening_count
            .clamp(1, PHASE2_WHIR_MAX_OPENING_TERMS as u16),
    );
    let local_eval = evaluate_fold8(
        record.fold_payload,
        challenges.fold_r,
        arithmetic,
        fold_mode,
        counters,
    );
    let (numerator_eval, selector_eval, opening_denom, selector_denom) = match precompute_mode {
        WhirQueryPrecomputeMode::None => (
            horner_eval_m31(record.numerator_coeffs, record.x.c0, arithmetic, counters),
            selector_mix_m31(
                record.selector_weights,
                record.selectors,
                selector_count,
                challenges.beta,
                arithmetic,
                counters,
            ),
            denominator_chain_cm31(
                record.x,
                &record.openings,
                opening_count,
                extension,
                counters,
            ),
            denominator_chain_cm31(
                record.x.conjugate(counters),
                &record.selectors,
                selector_count,
                extension,
                counters,
            ),
        ),
        WhirQueryPrecomputeMode::ProofCarriedRoundLocal => (
            record.precomputed.numerator_eval,
            record.precomputed.selector_affine_term.add(
                challenges
                    .beta
                    .mul(record.precomputed.selector_weight_sum, arithmetic, counters),
                counters,
            ),
            record.precomputed.opening_denom,
            record.precomputed.selector_denom,
        ),
    };
    let numerator_cm = Cm31::new(local_eval.add(numerator_eval, counters), selector_eval);
    let combined_denom = opening_denom.mul(selector_denom, extension, counters);
    WhirQueryTerm {
        numerator_cm,
        combined_denom,
        beta: challenges.beta,
        gamma: challenges.gamma,
    }
}

fn finish_whir_query_term(
    term: WhirQueryTerm,
    denom_inv: Cm31,
    arithmetic: Phase2ArithmeticConfig,
    extension: Phase2ExtensionConfig,
    lift_policy: LiftPolicy,
    counters: &mut Phase2Counters,
) -> Qm31 {
    match lift_policy {
        LiftPolicy::LateLiftQm31 => {
            let residue = term.numerator_cm.mul(denom_inv, extension, counters);
            let weighted = residue.mul_const(term.beta, arithmetic, counters);
            bump_counter!(counters, lift_to_qm31_ops, 1);
            Qm31::from_cm31(weighted).mul(term.gamma, extension, counters)
        }
        LiftPolicy::EagerQm31 => {
            bump_counter!(counters, lift_to_cm31_ops, 1);
            bump_counter!(counters, lift_to_qm31_ops, 1);
            Qm31::from_cm31(term.numerator_cm)
                .mul(Qm31::from_cm31(denom_inv), extension, counters)
                .mul(term.gamma, extension, counters)
        }
    }
}

fn batch_invert_cm31(
    values: &[Cm31],
    config: Phase2ExtensionConfig,
    counters: &mut Phase2Counters,
) -> Vec<Cm31> {
    if values.is_empty() {
        return Vec::new();
    }
    let mut prefixes = Vec::with_capacity(values.len());
    let mut product = Cm31::from_base(M31::ONE);
    for value in values {
        prefixes.push(product);
        product = product.mul(*value, config, counters);
    }
    let mut suffix_inv = product.inv(config, counters);
    let mut inverses = vec![Cm31::from_base(M31::ZERO); values.len()];
    for index in (0..values.len()).rev() {
        inverses[index] = prefixes[index].mul(suffix_inv, config, counters);
        suffix_inv = suffix_inv.mul(values[index], config, counters);
    }
    inverses
}

fn evaluate_whir_round_queries_reuse(
    view: &Phase2WhirTranscriptView,
    query_plan: Phase2WhirQueryPlan,
    config: Phase2VerifierConfig,
    round_index: usize,
    transcript: &mut [u8; 32],
    counters: &mut Phase2Counters,
) -> Result<Qm31, &'static str> {
    let round = view.round_plan(round_index);
    let query_round = transcript_round_as_query_round(round);
    let arithmetic = config.arithmetic_config();
    let extension = config.extension_config();
    let mut terms = Vec::with_capacity(usize::from(round.query_count.max(1)));
    for query_index in 0..usize::from(round.query_count.max(1)) {
        let position_digest =
            transcript_sample(transcript, b"phase2-whir/query-position", counters);
        let expected_position = u64::from_le_bytes(position_digest[0..8].try_into().unwrap());
        let actual = view.round_query_record(round_index, query_index)?;
        if actual.position != expected_position {
            return Err("phase2 whir transcript query position mismatch");
        }
        let expected_record = build_whir_query_record(
            query_plan,
            round_index as u64,
            query_index as u64,
            query_round,
            matches!(
                config.query_precompute_mode,
                WhirQueryPrecomputeMode::ProofCarriedRoundLocal
            ),
        );
        if !whir_query_record_matches(expected_record, actual.inner, view.fold_mode)
            || !whir_query_precomputed_matches(
                expected_record,
                actual.inner,
                config.query_precompute_mode,
            )
        {
            return Err("phase2 whir transcript query record mismatch");
        }
        let challenges = derive_whir_transcript_query_challenges(
            *transcript,
            round_index as u64,
            query_index as u64,
            actual.position,
            counters,
        );
        terms.push(build_whir_query_term(
            actual.inner,
            query_round,
            challenges,
            arithmetic,
            extension,
            view.fold_mode,
            config.query_precompute_mode,
            counters,
        ));
    }
    let denoms = terms
        .iter()
        .map(|term| term.combined_denom)
        .collect::<Vec<_>>();
    let inverses = batch_invert_cm31(&denoms, extension, counters);
    let mut accumulator = Qm31::from_base(M31::ZERO);
    for (term, denom_inv) in terms.iter().copied().zip(inverses.into_iter()) {
        let contribution = finish_whir_query_term(
            term,
            denom_inv,
            arithmetic,
            extension,
            config.lift_policy,
            counters,
        );
        accumulator = accumulator.add(contribution, counters);
    }
    Ok(accumulator)
}

fn whir_sumcheck_update(
    claimed_sum: M31,
    c0: M31,
    c_inf: M31,
    challenge: M31,
    arithmetic: Phase2ArithmeticConfig,
    counters: &mut Phase2Counters,
) -> M31 {
    let c1 = claimed_sum.sub(c0, counters);
    c0.add(challenge.mul(c1, arithmetic, counters), counters)
        .add(
            challenge
                .square(arithmetic, counters)
                .mul(c_inf, arithmetic, counters),
            counters,
        )
}

fn build_whir_final_coeffs(
    plan: Phase2WhirTranscriptPlan,
    claim: M31,
    coeff_count: usize,
) -> [M31; PHASE2_WHIR_MAX_FINAL_COEFFS] {
    let mut coeffs = [M31::ZERO; PHASE2_WHIR_MAX_FINAL_COEFFS];
    let query_plan = transcript_plan_as_query_plan(plan);
    for (index, slot) in coeffs.iter_mut().take(coeff_count).enumerate() {
        *slot = phase2_whir_semantic_m31(
            query_plan,
            0x8800 ^ index as u64,
            u64::from(plan.round_count),
            index as u64,
            claim.as_u32() as u64,
            [
                claim.as_u32() as u64,
                index as u64,
                u64::from(plan.final_query_count),
            ],
        );
    }
    coeffs
}

fn horner_eval_slice_m31(
    coeffs: &[M31],
    x: M31,
    arithmetic: Phase2ArithmeticConfig,
    counters: &mut Phase2Counters,
) -> M31 {
    let mut acc = M31::ZERO;
    for coeff in coeffs {
        acc = acc.mul(x, arithmetic, counters).add(*coeff, counters);
    }
    acc
}

fn final_query_point(position: u32, claim: M31) -> M31 {
    M31::new_lossy(position as u64 ^ claim.as_u32() as u64)
}

fn build_whir_deferred_evals(
    plan: Phase2WhirTranscriptPlan,
    final_claim: M31,
) -> [M31; PHASE2_WHIR_DEFERRED_EVAL_WORDS] {
    let query_plan = transcript_plan_as_query_plan(plan);
    let mut out = [M31::ZERO; PHASE2_WHIR_DEFERRED_EVAL_WORDS];
    for (index, slot) in out.iter_mut().enumerate() {
        *slot = phase2_whir_semantic_m31(
            query_plan,
            0x9900 ^ index as u64,
            u64::from(plan.round_count) + 1,
            index as u64,
            final_claim.as_u32() as u64,
            [
                final_claim.as_u32() as u64,
                u64::from(plan.final_query_count),
                index as u64,
            ],
        );
    }
    out
}

fn whir_query_record_matches(
    expected: WhirQueryRecord,
    actual: WhirQueryRecord,
    fold_mode: WhirFoldMode,
) -> bool {
    let expected_payload = match fold_mode {
        WhirFoldMode::RawFibers => expected.fold_payload,
        WhirFoldMode::LocalInterpolant => multilinear_to_local_interpolant(expected.fold_payload),
    };
    actual.x.c0.as_u32() == expected.x.c0.as_u32()
        && actual.x.c1.as_u32() == expected.x.c1.as_u32()
        && actual
            .openings
            .iter()
            .zip(expected.openings.iter())
            .all(|(lhs, rhs)| {
                lhs.c0.as_u32() == rhs.c0.as_u32() && lhs.c1.as_u32() == rhs.c1.as_u32()
            })
        && actual
            .selectors
            .iter()
            .zip(expected.selectors.iter())
            .all(|(lhs, rhs)| {
                lhs.c0.as_u32() == rhs.c0.as_u32() && lhs.c1.as_u32() == rhs.c1.as_u32()
            })
        && actual
            .fold_payload
            .iter()
            .zip(expected_payload.iter())
            .all(|(lhs, rhs)| lhs.as_u32() == rhs.as_u32())
        && actual
            .numerator_coeffs
            .iter()
            .zip(expected.numerator_coeffs.iter())
            .all(|(lhs, rhs)| lhs.as_u32() == rhs.as_u32())
        && actual
            .selector_weights
            .iter()
            .zip(expected.selector_weights.iter())
            .all(|(lhs, rhs)| lhs.as_u32() == rhs.as_u32())
}

fn whir_query_precomputed_matches(
    expected: WhirQueryRecord,
    actual: WhirQueryRecord,
    precompute_mode: WhirQueryPrecomputeMode,
) -> bool {
    match precompute_mode {
        WhirQueryPrecomputeMode::None => true,
        WhirQueryPrecomputeMode::ProofCarriedRoundLocal => {
            actual.precomputed.numerator_eval.as_u32()
                == expected.precomputed.numerator_eval.as_u32()
                && actual.precomputed.selector_affine_term.as_u32()
                    == expected.precomputed.selector_affine_term.as_u32()
                && actual.precomputed.selector_weight_sum.as_u32()
                    == expected.precomputed.selector_weight_sum.as_u32()
                && actual.precomputed.opening_denom.c0.as_u32()
                    == expected.precomputed.opening_denom.c0.as_u32()
                && actual.precomputed.opening_denom.c1.as_u32()
                    == expected.precomputed.opening_denom.c1.as_u32()
                && actual.precomputed.selector_denom.c0.as_u32()
                    == expected.precomputed.selector_denom.c0.as_u32()
                && actual.precomputed.selector_denom.c1.as_u32()
                    == expected.precomputed.selector_denom.c1.as_u32()
        }
    }
}

#[cfg(not(feature = "no-entrypoint"))]
fn trace_phase_begin(mode: WhirTranscriptTraceMode, label: &str) {
    if matches!(mode, WhirTranscriptTraceMode::Enabled) && label == "parse" {
        solana_program::msg!("phase2-whir-transcript start");
        solana_program::log::sol_log_compute_units();
    }
}

#[cfg(feature = "no-entrypoint")]
fn trace_phase_begin(_mode: WhirTranscriptTraceMode, _label: &str) {}

#[cfg(not(feature = "no-entrypoint"))]
fn trace_phase_end(mode: WhirTranscriptTraceMode, label: &str) {
    if matches!(mode, WhirTranscriptTraceMode::Enabled) {
        solana_program::msg!("phase2-whir-transcript stage {}", label);
        solana_program::log::sol_log_compute_units();
    }
}

#[cfg(feature = "no-entrypoint")]
fn trace_phase_end(_mode: WhirTranscriptTraceMode, _label: &str) {}

fn evaluate_fold(
    payload: [M31; 4],
    r0: M31,
    r1: M31,
    arithmetic: Phase2ArithmeticConfig,
    fold_mode: WhirFoldMode,
    counters: &mut Phase2Counters,
) -> M31 {
    match fold_mode {
        WhirFoldMode::RawFibers => {
            let v00 = payload[0];
            let v10 = payload[1];
            let v01 = payload[2];
            let v11 = payload[3];
            let cx = v10.sub(v00, counters);
            let cy = v01.sub(v00, counters);
            let cxy = v11.sub(v10, counters).sub(v01, counters).add(v00, counters);
            let cross = r0.mul(r1, arithmetic, counters);
            v00.add(r0.mul(cx, arithmetic, counters), counters)
                .add(r1.mul(cy, arithmetic, counters), counters)
                .add(cross.mul(cxy, arithmetic, counters), counters)
        }
        WhirFoldMode::LocalInterpolant => {
            let c0 = payload[0];
            let cx = payload[1];
            let cy = payload[2];
            let cxy = payload[3];
            let cross = r0.mul(r1, arithmetic, counters);
            c0.add(r0.mul(cx, arithmetic, counters), counters)
                .add(r1.mul(cy, arithmetic, counters), counters)
                .add(cross.mul(cxy, arithmetic, counters), counters)
        }
    }
}

fn evaluate_fold8(
    payload: [M31; PHASE2_WHIR_FOLD_VALUES],
    r: [M31; 3],
    arithmetic: Phase2ArithmeticConfig,
    fold_mode: WhirFoldMode,
    counters: &mut Phase2Counters,
) -> M31 {
    match fold_mode {
        WhirFoldMode::RawFibers => {
            let x00 = lerp_m31(payload[0], payload[1], r[0], arithmetic, counters);
            let x01 = lerp_m31(payload[2], payload[3], r[0], arithmetic, counters);
            let x10 = lerp_m31(payload[4], payload[5], r[0], arithmetic, counters);
            let x11 = lerp_m31(payload[6], payload[7], r[0], arithmetic, counters);
            let y0 = lerp_m31(x00, x01, r[1], arithmetic, counters);
            let y1 = lerp_m31(x10, x11, r[1], arithmetic, counters);
            lerp_m31(y0, y1, r[2], arithmetic, counters)
        }
        WhirFoldMode::LocalInterpolant => {
            let r01 = r[0].mul(r[1], arithmetic, counters);
            let r02 = r[0].mul(r[2], arithmetic, counters);
            let r12 = r[1].mul(r[2], arithmetic, counters);
            let r012 = r01.mul(r[2], arithmetic, counters);
            payload[0]
                .add(r[0].mul(payload[1], arithmetic, counters), counters)
                .add(r[1].mul(payload[2], arithmetic, counters), counters)
                .add(r01.mul(payload[3], arithmetic, counters), counters)
                .add(r[2].mul(payload[4], arithmetic, counters), counters)
                .add(r02.mul(payload[5], arithmetic, counters), counters)
                .add(r12.mul(payload[6], arithmetic, counters), counters)
                .add(r012.mul(payload[7], arithmetic, counters), counters)
        }
    }
}

fn lerp_m31(
    a: M31,
    b: M31,
    r: M31,
    arithmetic: Phase2ArithmeticConfig,
    counters: &mut Phase2Counters,
) -> M31 {
    let delta = b.sub(a, counters);
    a.add(r.mul(delta, arithmetic, counters), counters)
}

fn horner_eval_m31(
    coeffs: [M31; PHASE2_WHIR_NUMERATOR_COEFFS],
    x: M31,
    arithmetic: Phase2ArithmeticConfig,
    counters: &mut Phase2Counters,
) -> M31 {
    let mut acc = M31::ZERO;
    for coeff in coeffs {
        acc = acc.mul(x, arithmetic, counters).add(coeff, counters);
    }
    acc
}

fn selector_mix_m31(
    weights: [M31; PHASE2_WHIR_SELECTOR_TERMS],
    selectors: [Cm31; PHASE2_WHIR_SELECTOR_TERMS],
    selector_count: usize,
    beta: M31,
    arithmetic: Phase2ArithmeticConfig,
    counters: &mut Phase2Counters,
) -> M31 {
    let mut acc = M31::ZERO;
    for index in 0..selector_count.min(PHASE2_WHIR_SELECTOR_TERMS) {
        let shifted = selectors[index].c0.add(beta, counters);
        acc = acc.add(weights[index].mul(shifted, arithmetic, counters), counters);
    }
    acc
}

fn denominator_chain_cm31(
    x: Cm31,
    points: &[Cm31],
    count: usize,
    config: Phase2ExtensionConfig,
    counters: &mut Phase2Counters,
) -> Cm31 {
    let mut product = Cm31::from_base(M31::ONE);
    for point in points.iter().take(count.max(1)) {
        product = product.mul(x.sub(*point, counters), config, counters);
    }
    product
}

fn derive_whir_query_precomputed(
    record: &WhirQueryRecord,
    round: Phase2WhirRoundPlan,
    arithmetic: Phase2ArithmeticConfig,
    extension: Phase2ExtensionConfig,
    counters: &mut Phase2Counters,
) -> WhirQueryPrecomputed {
    let selector_count = usize::from(
        round
            .selector_count
            .clamp(1, PHASE2_WHIR_SELECTOR_TERMS as u16),
    );
    let opening_count = usize::from(
        round
            .opening_count
            .clamp(1, PHASE2_WHIR_MAX_OPENING_TERMS as u16),
    );
    let numerator_eval =
        horner_eval_m31(record.numerator_coeffs, record.x.c0, arithmetic, counters);
    let mut selector_affine_term = M31::ZERO;
    let mut selector_weight_sum = M31::ZERO;
    for index in 0..selector_count {
        selector_affine_term = selector_affine_term.add(
            record.selector_weights[index].mul(record.selectors[index].c0, arithmetic, counters),
            counters,
        );
        selector_weight_sum = selector_weight_sum.add(record.selector_weights[index], counters);
    }
    let opening_denom = denominator_chain_cm31(
        record.x,
        &record.openings,
        opening_count,
        extension,
        counters,
    );
    let selector_denom = denominator_chain_cm31(
        record.x.conjugate(counters),
        &record.selectors,
        selector_count,
        extension,
        counters,
    );
    WhirQueryPrecomputed {
        numerator_eval,
        selector_affine_term,
        selector_weight_sum,
        opening_denom,
        selector_denom,
    }
}

fn synthetic_merkle_cost(
    depth: usize,
    paths: usize,
    mode: MerkleProofMode,
    counters: &mut Phase2Counters,
) -> [u8; 32] {
    let effective_paths = paths.max(1);
    let effective_depth = depth.max(1);
    let mut state = [0_u8; 32];
    match mode {
        MerkleProofMode::SeparatePaths => {
            for path_index in 0..effective_paths {
                for level in 0..effective_depth {
                    bump_counter!(counters, sha_calls, 1);
                    bump_counter!(counters, sha_bytes, 64);
                    state = hashv(&[
                        &state,
                        &(path_index as u32).to_le_bytes(),
                        &(level as u32).to_le_bytes(),
                    ])
                    .to_bytes();
                }
            }
        }
        MerkleProofMode::MinimalSubtree => {
            let unique_nodes = effective_depth + effective_paths.saturating_sub(1);
            for node in 0..unique_nodes.max(1) {
                bump_counter!(counters, sha_calls, 1);
                bump_counter!(counters, sha_bytes, 64);
                state = hashv(&[&state, &(node as u32).to_le_bytes()]).to_bytes();
            }
        }
    }
    state
}

fn synthetic_merkle_witness_node_count(depth: usize, paths: usize, mode: MerkleProofMode) -> usize {
    let effective_paths = paths.max(1);
    let effective_depth = depth.max(1);
    match mode {
        MerkleProofMode::SeparatePaths => effective_depth * effective_paths,
        MerkleProofMode::MinimalSubtree => effective_depth + effective_paths.saturating_sub(1),
    }
}

fn synthetic_merkle_witness_bytes(depth: usize, paths: usize, mode: MerkleProofMode) -> usize {
    synthetic_merkle_witness_node_count(depth, paths, mode) * PHASE2_WHIR_MERKLE_NODE_BYTES
}

fn synthetic_merkle_witness_node(
    statement_digest: [u8; 32],
    namespace: u64,
    depth: usize,
    paths: usize,
    mode: MerkleProofMode,
    node_index: usize,
) -> [u8; 32] {
    hashv(&[
        b"phase2-whir/merkle-witness",
        &statement_digest,
        &namespace.to_le_bytes(),
        &(depth as u32).to_le_bytes(),
        &(paths as u32).to_le_bytes(),
        &(mode as u16).to_le_bytes(),
        &(node_index as u32).to_le_bytes(),
    ])
    .to_bytes()
}

fn append_synthetic_merkle_witness(
    out: &mut Vec<u8>,
    statement_digest: [u8; 32],
    namespace: u64,
    depth: usize,
    paths: usize,
    mode: MerkleProofMode,
) -> [u8; 32] {
    let node_count = synthetic_merkle_witness_node_count(depth, paths, mode);
    let mut state = [0_u8; 32];
    for node_index in 0..node_count {
        let node = synthetic_merkle_witness_node(
            statement_digest,
            namespace,
            depth,
            paths,
            mode,
            node_index,
        );
        out.extend_from_slice(&node);
        state = hashv(&[&state, &node, &(node_index as u32).to_le_bytes()]).to_bytes();
    }
    state
}

fn generated_synthetic_merkle_digest(
    statement_digest: [u8; 32],
    namespace: u64,
    depth: usize,
    paths: usize,
    mode: MerkleProofMode,
) -> [u8; 32] {
    let node_count = synthetic_merkle_witness_node_count(depth, paths, mode);
    let mut state = [0_u8; 32];
    for node_index in 0..node_count {
        let node = synthetic_merkle_witness_node(
            statement_digest,
            namespace,
            depth,
            paths,
            mode,
            node_index,
        );
        state = hashv(&[&state, &node, &(node_index as u32).to_le_bytes()]).to_bytes();
    }
    state
}

fn digest_synthetic_merkle_witness(
    witness_bytes: &[u8],
    depth: usize,
    paths: usize,
    mode: MerkleProofMode,
    counters: &mut Phase2Counters,
) -> Result<[u8; 32], &'static str> {
    let node_count = synthetic_merkle_witness_node_count(depth, paths, mode);
    if witness_bytes.len() != node_count * PHASE2_WHIR_MERKLE_NODE_BYTES {
        return Err("phase2 whir transcript merkle witness length mismatch");
    }
    let mut state = [0_u8; 32];
    for node_index in 0..node_count {
        let offset = node_index * PHASE2_WHIR_MERKLE_NODE_BYTES;
        let node = &witness_bytes[offset..offset + PHASE2_WHIR_MERKLE_NODE_BYTES];
        bump_counter!(counters, sha_calls, 1);
        bump_counter!(
            counters,
            sha_bytes,
            (state.len() + node.len() + core::mem::size_of::<u32>()) as u64
        );
        state = hashv(&[&state, node, &(node_index as u32).to_le_bytes()]).to_bytes();
    }
    Ok(state)
}

fn whir_merkle_payload_section_count(plan: Phase2WhirTranscriptPlan) -> usize {
    usize::from(plan.round_count.clamp(0, PHASE2_WHIR_MAX_ROUNDS as u16)) + 1
}

fn whir_merkle_payload_section(
    plan: Phase2WhirTranscriptPlan,
    section_index: usize,
) -> Option<(u64, usize, usize)> {
    let round_count = usize::from(plan.round_count.clamp(0, PHASE2_WHIR_MAX_ROUNDS as u16));
    if section_index < round_count {
        let round = plan.rounds[section_index];
        Some((
            section_index as u64,
            usize::from(round.merkle_depth.max(1)),
            usize::from(round.query_count.max(1)),
        ))
    } else if section_index == round_count {
        Some((
            u64::MAX,
            usize::from(plan.final_merkle_depth.max(1)),
            usize::from(plan.final_query_count.max(1)),
        ))
    } else {
        None
    }
}

fn synthetic_merkle_payload_query_position(
    statement_digest: [u8; 32],
    namespace: u64,
    query_index: usize,
) -> u32 {
    let word_index = (query_index % 8) * 4;
    let digest_word = u32::from_le_bytes(
        statement_digest[word_index..word_index + 4]
            .try_into()
            .unwrap(),
    );
    let namespace_mix = (namespace as u32) ^ ((namespace >> 32) as u32);
    digest_word
        .wrapping_add(namespace_mix.rotate_left((query_index % 31) as u32))
        .wrapping_add(((query_index as u32).wrapping_add(1)).wrapping_mul(0x9e37_79b9))
        & M31_MODULUS
}

fn synthetic_merkle_payload_node_metadata(
    depth: usize,
    paths: usize,
    mode: MerkleProofMode,
    node_index: usize,
) -> (u16, u16, u32) {
    let effective_depth = depth.max(1);
    let effective_paths = paths.max(1);
    let (level, branch) = match mode {
        MerkleProofMode::SeparatePaths => {
            let level = (node_index % effective_depth) as u16;
            let branch = (node_index / effective_depth) as u16;
            (level, branch)
        }
        MerkleProofMode::MinimalSubtree => {
            if node_index < effective_depth {
                (node_index as u16, 0)
            } else {
                (
                    effective_depth.saturating_sub(1) as u16,
                    (node_index - effective_depth + 1).min(effective_paths.saturating_sub(1))
                        as u16,
                )
            }
        }
    };
    let slot = ((u32::from(branch)) << 16) | u32::from(level);
    (level, branch, slot)
}

pub fn build_phase2_whir_merkle_payload_bytes(
    plan: Phase2WhirTranscriptPlan,
    mode: MerkleProofMode,
    payload_format: WhirMerklePayloadFormat,
) -> Vec<u8> {
    let statement_digest = phase2_whir_transcript_statement_digest(plan);
    match payload_format {
        WhirMerklePayloadFormat::FlatNodes => {
            let mut out = Vec::new();
            for section_index in 0..whir_merkle_payload_section_count(plan) {
                let (namespace, depth, paths) =
                    whir_merkle_payload_section(plan, section_index).unwrap();
                append_synthetic_merkle_witness(
                    &mut out,
                    statement_digest,
                    namespace,
                    depth,
                    paths,
                    mode,
                );
            }
            out
        }
        WhirMerklePayloadFormat::CanonicalPayload => {
            let section_count = whir_merkle_payload_section_count(plan);
            let total_nodes = (0..section_count)
                .map(|section_index| {
                    let (_, depth, paths) =
                        whir_merkle_payload_section(plan, section_index).unwrap();
                    synthetic_merkle_witness_node_count(depth, paths, mode)
                })
                .sum::<usize>();
            let mut out = Vec::new();
            out.extend_from_slice(&PHASE2_WHIR_MERKLE_PAYLOAD_MAGIC);
            out.extend_from_slice(&PHASE2_WHIR_MERKLE_PAYLOAD_VERSION.to_le_bytes());
            out.extend_from_slice(&(mode as u16).to_le_bytes());
            out.extend_from_slice(&(payload_format as u16).to_le_bytes());
            out.extend_from_slice(&(section_count as u16).to_le_bytes());
            out.extend_from_slice(&(total_nodes as u32).to_le_bytes());
            out.extend_from_slice(&statement_digest);
            for section_index in 0..section_count {
                let (namespace, depth, paths) =
                    whir_merkle_payload_section(plan, section_index).unwrap();
                let node_count = synthetic_merkle_witness_node_count(depth, paths, mode);
                out.extend_from_slice(&namespace.to_le_bytes());
                out.extend_from_slice(&(depth as u16).to_le_bytes());
                out.extend_from_slice(&(paths as u16).to_le_bytes());
                out.extend_from_slice(&(node_count as u32).to_le_bytes());
                for query_index in 0..paths {
                    out.extend_from_slice(
                        &synthetic_merkle_payload_query_position(
                            statement_digest,
                            namespace,
                            query_index,
                        )
                        .to_le_bytes(),
                    );
                }
                for node_index in 0..node_count {
                    let (level, branch, slot) =
                        synthetic_merkle_payload_node_metadata(depth, paths, mode, node_index);
                    let node = synthetic_merkle_witness_node(
                        statement_digest,
                        namespace,
                        depth,
                        paths,
                        mode,
                        node_index,
                    );
                    out.extend_from_slice(&level.to_le_bytes());
                    out.extend_from_slice(&branch.to_le_bytes());
                    out.extend_from_slice(&slot.to_le_bytes());
                    out.extend_from_slice(&node);
                }
            }
            out
        }
    }
}

pub fn run_phase2_whir_merkle_payload_parse(
    config: Phase2VerifierConfig,
    plan: Phase2WhirTranscriptPlan,
    payload_bytes: &[u8],
    payload_format: WhirMerklePayloadFormat,
    repeat: u32,
) -> Result<Phase2VerifierOutcome, &'static str> {
    let statement_digest = phase2_whir_transcript_statement_digest(plan);
    let section_count = whir_merkle_payload_section_count(plan);
    let mut counters = Phase2Counters::default();
    counters.proof_bytes = payload_bytes.len() as u64;
    counters.parser_bytes = payload_bytes.len() as u64;
    counters.merkle_paths = (0..section_count)
        .map(|section_index| {
            let (_, _, paths) = whir_merkle_payload_section(plan, section_index).unwrap();
            paths as u64
        })
        .sum();
    counters.merkle_levels = (0..section_count)
        .map(|section_index| {
            let (_, depth, _) = whir_merkle_payload_section(plan, section_index).unwrap();
            depth as u64
        })
        .sum();
    let tail_checksum = checksum_tail(payload_bytes);
    let mut digest = 0_u32;

    for repetition in 0..repeat.max(1) {
        let mut cursor = 0usize;
        let mut state = [0_u8; 32];
        match payload_format {
            WhirMerklePayloadFormat::FlatNodes => {
                for section_index in 0..section_count {
                    let (namespace, depth, paths) =
                        whir_merkle_payload_section(plan, section_index).unwrap();
                    let byte_len =
                        synthetic_merkle_witness_bytes(depth, paths, config.merkle_proof_mode);
                    if cursor + byte_len > payload_bytes.len() {
                        return Err("phase2 whir merkle payload truncated flat nodes");
                    }
                    let section_bytes = &payload_bytes[cursor..cursor + byte_len];
                    let section_digest = digest_synthetic_merkle_witness(
                        section_bytes,
                        depth,
                        paths,
                        config.merkle_proof_mode,
                        &mut counters,
                    )?;
                    bump_counter!(counters, sha_calls, 1);
                    bump_counter!(
                        counters,
                        sha_bytes,
                        (state.len()
                            + core::mem::size_of::<u64>()
                            + section_digest.len()
                            + core::mem::size_of::<u32>()) as u64
                    );
                    state = hashv(&[
                        &state,
                        &namespace.to_le_bytes(),
                        &section_digest,
                        &(section_index as u32).to_le_bytes(),
                    ])
                    .to_bytes();
                    cursor += byte_len;
                }
                if cursor != payload_bytes.len() {
                    return Err("phase2 whir merkle payload flat node length mismatch");
                }
            }
            WhirMerklePayloadFormat::CanonicalPayload => {
                if payload_bytes.len() < 48 {
                    return Err("phase2 whir merkle payload too short");
                }
                if payload_bytes[0..4] != PHASE2_WHIR_MERKLE_PAYLOAD_MAGIC {
                    return Err("phase2 whir merkle payload magic mismatch");
                }
                cursor += 4;
                let version =
                    u16::from_le_bytes(payload_bytes[cursor..cursor + 2].try_into().unwrap());
                cursor += 2;
                if version != PHASE2_WHIR_MERKLE_PAYLOAD_VERSION {
                    return Err("phase2 whir merkle payload version mismatch");
                }
                let payload_mode =
                    u16::from_le_bytes(payload_bytes[cursor..cursor + 2].try_into().unwrap());
                cursor += 2;
                if payload_mode != config.merkle_proof_mode as u16 {
                    return Err("phase2 whir merkle payload merkle mode mismatch");
                }
                let encoded_format =
                    u16::from_le_bytes(payload_bytes[cursor..cursor + 2].try_into().unwrap());
                cursor += 2;
                if encoded_format != payload_format as u16 {
                    return Err("phase2 whir merkle payload format mismatch");
                }
                let encoded_sections =
                    u16::from_le_bytes(payload_bytes[cursor..cursor + 2].try_into().unwrap())
                        as usize;
                cursor += 2;
                if encoded_sections != section_count {
                    return Err("phase2 whir merkle payload section count mismatch");
                }
                let total_nodes =
                    u32::from_le_bytes(payload_bytes[cursor..cursor + 4].try_into().unwrap())
                        as usize;
                cursor += 4;
                let expected_total_nodes = (0..section_count)
                    .map(|section_index| {
                        let (_, depth, paths) =
                            whir_merkle_payload_section(plan, section_index).unwrap();
                        synthetic_merkle_witness_node_count(depth, paths, config.merkle_proof_mode)
                    })
                    .sum::<usize>();
                if total_nodes != expected_total_nodes {
                    return Err("phase2 whir merkle payload total node count mismatch");
                }
                if payload_bytes[cursor..cursor + 32] != statement_digest {
                    return Err("phase2 whir merkle payload statement digest mismatch");
                }
                cursor += 32;
                for section_index in 0..section_count {
                    let (namespace, depth, paths) =
                        whir_merkle_payload_section(plan, section_index).unwrap();
                    let node_count =
                        synthetic_merkle_witness_node_count(depth, paths, config.merkle_proof_mode);
                    if cursor + 16 > payload_bytes.len() {
                        return Err("phase2 whir merkle payload truncated section header");
                    }
                    let actual_namespace =
                        u64::from_le_bytes(payload_bytes[cursor..cursor + 8].try_into().unwrap());
                    cursor += 8;
                    let actual_depth =
                        u16::from_le_bytes(payload_bytes[cursor..cursor + 2].try_into().unwrap())
                            as usize;
                    cursor += 2;
                    let actual_paths =
                        u16::from_le_bytes(payload_bytes[cursor..cursor + 2].try_into().unwrap())
                            as usize;
                    cursor += 2;
                    let actual_nodes =
                        u32::from_le_bytes(payload_bytes[cursor..cursor + 4].try_into().unwrap())
                            as usize;
                    cursor += 4;
                    if actual_namespace != namespace
                        || actual_depth != depth
                        || actual_paths != paths
                        || actual_nodes != node_count
                    {
                        return Err("phase2 whir merkle payload section header mismatch");
                    }
                    for query_index in 0..paths {
                        if cursor + 4 > payload_bytes.len() {
                            return Err("phase2 whir merkle payload truncated query positions");
                        }
                        let actual_position = u32::from_le_bytes(
                            payload_bytes[cursor..cursor + 4].try_into().unwrap(),
                        );
                        cursor += 4;
                        let expected_position = synthetic_merkle_payload_query_position(
                            statement_digest,
                            namespace,
                            query_index,
                        );
                        if actual_position != expected_position {
                            return Err("phase2 whir merkle payload query position mismatch");
                        }
                        bump_counter!(counters, sha_calls, 1);
                        bump_counter!(
                            counters,
                            sha_bytes,
                            (state.len()
                                + core::mem::size_of::<u64>()
                                + 2 * core::mem::size_of::<u32>())
                                as u64
                        );
                        state = hashv(&[
                            &state,
                            &namespace.to_le_bytes(),
                            &(query_index as u32).to_le_bytes(),
                            &actual_position.to_le_bytes(),
                        ])
                        .to_bytes();
                    }
                    for node_index in 0..node_count {
                        if cursor + 40 > payload_bytes.len() {
                            return Err("phase2 whir merkle payload truncated node entry");
                        }
                        let actual_level = u16::from_le_bytes(
                            payload_bytes[cursor..cursor + 2].try_into().unwrap(),
                        );
                        cursor += 2;
                        let actual_branch = u16::from_le_bytes(
                            payload_bytes[cursor..cursor + 2].try_into().unwrap(),
                        );
                        cursor += 2;
                        let actual_slot = u32::from_le_bytes(
                            payload_bytes[cursor..cursor + 4].try_into().unwrap(),
                        );
                        cursor += 4;
                        let node = &payload_bytes[cursor..cursor + PHASE2_WHIR_MERKLE_NODE_BYTES];
                        cursor += PHASE2_WHIR_MERKLE_NODE_BYTES;
                        let (expected_level, expected_branch, expected_slot) =
                            synthetic_merkle_payload_node_metadata(
                                depth,
                                paths,
                                config.merkle_proof_mode,
                                node_index,
                            );
                        if actual_level != expected_level
                            || actual_branch != expected_branch
                            || actual_slot != expected_slot
                        {
                            return Err("phase2 whir merkle payload node metadata mismatch");
                        }
                        bump_counter!(counters, sha_calls, 1);
                        bump_counter!(
                            counters,
                            sha_bytes,
                            (state.len()
                                + core::mem::size_of::<u64>()
                                + 2 * core::mem::size_of::<u16>()
                                + core::mem::size_of::<u32>()
                                + node.len()) as u64
                        );
                        state = hashv(&[
                            &state,
                            &namespace.to_le_bytes(),
                            &actual_level.to_le_bytes(),
                            &actual_branch.to_le_bytes(),
                            &actual_slot.to_le_bytes(),
                            node,
                        ])
                        .to_bytes();
                    }
                }
                if cursor != payload_bytes.len() {
                    return Err("phase2 whir merkle payload canonical length mismatch");
                }
            }
        }
        digest ^= digest_word_to_m31(&state[0..4])
            .as_u32()
            .rotate_left((repetition + 1) % 31)
            ^ tail_checksum;
    }

    Ok(Phase2VerifierOutcome {
        digest,
        counters,
        uses_heap: false,
    })
}

fn checksum_tail(bytes: &[u8]) -> u32 {
    let mut state = 0x811c_9dc5_u32;
    for (index, byte) in bytes.iter().enumerate() {
        state ^= (*byte as u32).rotate_left((index % 13) as u32);
        state = state.wrapping_mul(0x0100_0193);
    }
    state
}

fn build_query_record(plan: Phase2ProofPlan, query_index: u64) -> QueryRecord {
    let seed = mix64(plan.query_schedule_seed ^ query_index.rotate_left(9));
    let x = seeded_cm31(seed);
    let mut counters = Phase2Counters::default();
    let z0 = x.add(
        Cm31::new(
            sample_nonzero_m31(seed.rotate_left(11)),
            sample_nonzero_m31(seed.rotate_left(21)),
        ),
        &mut counters,
    );
    let z1 = x.conjugate(&mut counters).add(
        Cm31::new(
            sample_nonzero_m31(seed.rotate_left(23)),
            sample_nonzero_m31(seed.rotate_left(31)),
        ),
        &mut counters,
    );
    let fibers = [
        sample_m31(seed),
        sample_m31(seed.rotate_left(7)),
        sample_m31(seed.rotate_left(17)),
        sample_m31(seed.rotate_left(29)),
    ];
    QueryRecord {
        x,
        z0,
        z1,
        fold_payload: match plan.fold_arity {
            4 => fibers,
            _ => fibers,
        },
    }
}

fn build_whir_query_record(
    plan: Phase2WhirQueryPlan,
    round_index: u64,
    query_index: u64,
    round: Phase2WhirRoundPlan,
    derive_precomputed: bool,
) -> WhirQueryRecord {
    let query_ordinal = phase2_whir_query_ordinal(plan, round_index as usize, query_index);
    let row_index = phase2_whir_semantic_row_index(plan, round_index, query_ordinal, round);
    let (bucket_index, bucket_start, bucket_len, local_row) =
        phase2_whir_row_bucket(plan.statement_shape, row_index);
    let semantic_axes =
        phase2_whir_semantic_axes(plan.statement_shape, bucket_index, local_row, bucket_len);
    let x = phase2_whir_semantic_cm31(
        plan,
        0x1000,
        round_index,
        query_ordinal,
        row_index as u64,
        semantic_axes,
    );
    let mut counters = Phase2Counters::default();
    let mut openings = [Cm31::from_base(M31::ZERO); PHASE2_WHIR_MAX_OPENING_TERMS];
    for (index, slot) in openings.iter_mut().enumerate() {
        let opening_row = phase2_whir_opening_row(
            row_index,
            bucket_start,
            bucket_len,
            round_index,
            query_ordinal,
            index,
            round.ood_samples,
        );
        let opening_axes = phase2_whir_semantic_axes(
            plan.statement_shape,
            bucket_index,
            opening_row - bucket_start,
            bucket_len,
        );
        *slot = x.add(
            phase2_whir_semantic_nonzero_cm31(
                plan,
                0x2000 + index as u64,
                round_index,
                query_ordinal,
                opening_row as u64,
                opening_axes,
            ),
            &mut counters,
        );
    }
    let mut selectors = [Cm31::from_base(M31::ZERO); PHASE2_WHIR_SELECTOR_TERMS];
    for (index, slot) in selectors.iter_mut().enumerate() {
        let selector_axes = phase2_whir_selector_axes(
            plan.statement_shape,
            bucket_index,
            query_ordinal,
            round_index,
            index,
        );
        *slot = x.conjugate(&mut counters).add(
            phase2_whir_semantic_nonzero_cm31(
                plan,
                0x3000 + index as u64,
                round_index,
                query_ordinal,
                row_index as u64,
                selector_axes,
            ),
            &mut counters,
        );
    }
    let fold_payload = phase2_whir_fold_payload(
        plan,
        round_index,
        query_ordinal,
        row_index as u64,
        semantic_axes,
    );
    let numerator_coeffs = phase2_whir_numerator_coeffs(
        plan,
        round_index,
        query_ordinal,
        row_index as u64,
        semantic_axes,
    );
    let selector_weights = phase2_whir_selector_weights(
        plan,
        round_index,
        query_ordinal,
        row_index as u64,
        semantic_axes,
    );
    let mut record = WhirQueryRecord {
        x,
        openings,
        selectors,
        fold_payload,
        numerator_coeffs,
        selector_weights,
        precomputed: whir_zero_query_precomputed(),
    };
    if derive_precomputed {
        let arithmetic = Phase2ArithmeticConfig::new(
            ArithmeticKernelId::ReferenceCanonical,
            ReductionMode::Canonical,
            LazyReductionMode::None,
        );
        let extension = Phase2ExtensionConfig {
            base: arithmetic,
            extension_kernel_id: ExtensionKernelId::Karatsuba,
        };
        record.precomputed =
            derive_whir_query_precomputed(&record, round, arithmetic, extension, &mut counters);
    }
    record
}

fn phase2_whir_statement_digest(plan: Phase2WhirQueryPlan) -> [u8; 32] {
    let shape = plan.statement_shape;
    hashv(&[
        &plan.statement_seed.to_le_bytes(),
        &plan.query_schedule_seed.to_le_bytes(),
        &plan.round_count.to_le_bytes(),
        &plan.target_proof_bytes.to_le_bytes(),
        &shape.spends.to_le_bytes(),
        &shape.outputs.to_le_bytes(),
        &shape.note_tree_depth.to_le_bytes(),
        &shape.note_openings_per_spend.to_le_bytes(),
        &shape.nullifier_hashes_per_spend.to_le_bytes(),
        &shape.note_commitments_per_output.to_le_bytes(),
        &shape.amount_range_checks_64.to_le_bytes(),
        &shape.ownership_checks.to_le_bytes(),
        &shape.balance_constraints.to_le_bytes(),
        &shape.lookup_arguments.to_le_bytes(),
        &shape.boundary_constraint_groups.to_le_bytes(),
        &shape.application_merkle_paths.to_le_bytes(),
        &shape.application_hash_gadgets.to_le_bytes(),
        &shape.evaluation_domain_log2.to_le_bytes(),
        &shape.merkle_rows_per_level.to_le_bytes(),
        &shape.nullifier_hash_rows.to_le_bytes(),
        &shape.note_commitment_rows.to_le_bytes(),
        &shape.range_check_rows.to_le_bytes(),
        &shape.ownership_rows.to_le_bytes(),
        &shape.balance_rows.to_le_bytes(),
        &shape.lookup_rows.to_le_bytes(),
        &shape.misc_rows.to_le_bytes(),
        &shape.total_rows.to_le_bytes(),
        &shape.row_breakdown[0].to_le_bytes(),
        &shape.row_breakdown[1].to_le_bytes(),
        &shape.row_breakdown[2].to_le_bytes(),
        &shape.row_breakdown[3].to_le_bytes(),
        &shape.row_breakdown[4].to_le_bytes(),
        &shape.row_breakdown[5].to_le_bytes(),
        &shape.row_breakdown[6].to_le_bytes(),
        &shape.row_breakdown[7].to_le_bytes(),
    ])
    .to_bytes()
}

fn write_whir_statement_shape(out: &mut Vec<u8>, shape: Phase2WhirStatementShape) {
    for value in [
        shape.spends,
        shape.outputs,
        shape.note_tree_depth,
        shape.note_openings_per_spend,
        shape.nullifier_hashes_per_spend,
        shape.note_commitments_per_output,
        shape.amount_range_checks_64,
        shape.ownership_checks,
        shape.balance_constraints,
        shape.lookup_arguments,
        shape.boundary_constraint_groups,
        shape.application_merkle_paths,
        shape.application_hash_gadgets,
        shape.evaluation_domain_log2,
        shape.merkle_rows_per_level,
        shape.nullifier_hash_rows,
        shape.note_commitment_rows,
        shape.range_check_rows,
        shape.ownership_rows,
        shape.balance_rows,
        shape.lookup_rows,
        shape.misc_rows,
    ] {
        out.extend_from_slice(&value.to_le_bytes());
    }
    out.extend_from_slice(&shape.total_rows.to_le_bytes());
    for row in shape.row_breakdown {
        out.extend_from_slice(&row.to_le_bytes());
    }
}

fn read_whir_statement_shape(
    bytes: &[u8],
    mut offset: usize,
) -> Result<(Phase2WhirStatementShape, usize), &'static str> {
    let shape = Phase2WhirStatementShape {
        spends: read_u16(bytes, offset)?,
        outputs: read_u16(bytes, offset + 2)?,
        note_tree_depth: read_u16(bytes, offset + 4)?,
        note_openings_per_spend: read_u16(bytes, offset + 6)?,
        nullifier_hashes_per_spend: read_u16(bytes, offset + 8)?,
        note_commitments_per_output: read_u16(bytes, offset + 10)?,
        amount_range_checks_64: read_u16(bytes, offset + 12)?,
        ownership_checks: read_u16(bytes, offset + 14)?,
        balance_constraints: read_u16(bytes, offset + 16)?,
        lookup_arguments: read_u16(bytes, offset + 18)?,
        boundary_constraint_groups: read_u16(bytes, offset + 20)?,
        application_merkle_paths: read_u16(bytes, offset + 22)?,
        application_hash_gadgets: read_u16(bytes, offset + 24)?,
        evaluation_domain_log2: read_u16(bytes, offset + 26)?,
        merkle_rows_per_level: read_u16(bytes, offset + 28)?,
        nullifier_hash_rows: read_u16(bytes, offset + 30)?,
        note_commitment_rows: read_u16(bytes, offset + 32)?,
        range_check_rows: read_u16(bytes, offset + 34)?,
        ownership_rows: read_u16(bytes, offset + 36)?,
        balance_rows: read_u16(bytes, offset + 38)?,
        lookup_rows: read_u16(bytes, offset + 40)?,
        misc_rows: read_u16(bytes, offset + 42)?,
        total_rows: read_u32(bytes, offset + 44)?,
        row_breakdown: [
            read_u32(bytes, offset + 48)?,
            read_u32(bytes, offset + 52)?,
            read_u32(bytes, offset + 56)?,
            read_u32(bytes, offset + 60)?,
            read_u32(bytes, offset + 64)?,
            read_u32(bytes, offset + 68)?,
            read_u32(bytes, offset + 72)?,
            read_u32(bytes, offset + 76)?,
        ],
    };
    offset += 80;
    Ok((shape, offset))
}

fn phase2_whir_query_ordinal(
    plan: Phase2WhirQueryPlan,
    round_index: usize,
    query_index: u64,
) -> u64 {
    plan.rounds
        .iter()
        .take(round_index)
        .map(|round| u64::from(round.query_count.max(1)))
        .sum::<u64>()
        + query_index
}

fn phase2_whir_semantic_row_index(
    plan: Phase2WhirQueryPlan,
    round_index: u64,
    query_ordinal: u64,
    round: Phase2WhirRoundPlan,
) -> u32 {
    let total_rows = u64::from(plan.statement_shape.total_rows.max(1));
    let seed = phase2_whir_semantic_seed(
        plan,
        0x900,
        round_index,
        query_ordinal,
        u64::from(round.query_count),
        [
            u64::from(round.merkle_depth),
            u64::from(round.ood_samples),
            u64::from(round.opening_count),
        ],
    );
    (seed % total_rows) as u32
}

fn phase2_whir_row_bucket(
    shape: Phase2WhirStatementShape,
    row_index: u32,
) -> (usize, u32, u32, u32) {
    let mut start = 0_u32;
    for (bucket_index, bucket_len) in shape.row_breakdown.iter().copied().enumerate() {
        if row_index < start.saturating_add(bucket_len) {
            return (
                bucket_index,
                start,
                bucket_len.max(1),
                row_index.saturating_sub(start),
            );
        }
        start = start.saturating_add(bucket_len);
    }
    let last_index = PHASE2_WHIR_ROW_BUCKETS - 1;
    let last_len = shape.row_breakdown[last_index].max(1);
    (
        last_index,
        start.saturating_sub(last_len),
        last_len,
        row_index.saturating_sub(start.saturating_sub(last_len)),
    )
}

fn phase2_whir_semantic_axes(
    shape: Phase2WhirStatementShape,
    bucket_index: usize,
    local_row: u32,
    bucket_len: u32,
) -> [u64; 3] {
    match bucket_index {
        0 => {
            let per_level = u32::from(shape.merkle_rows_per_level.max(1));
            let depth = u32::from(shape.note_tree_depth.max(1));
            let path_index = local_row / per_level.saturating_mul(depth).max(1);
            let level = (local_row / per_level.max(1)) % depth.max(1);
            let row_in_level = local_row % per_level.max(1);
            [path_index as u64, level as u64, row_in_level as u64]
        }
        1 => {
            let per_hash = u32::from(shape.nullifier_hash_rows.max(1));
            let hash_index = local_row / per_hash.max(1);
            [
                hash_index as u64,
                (local_row % per_hash.max(1)) as u64,
                shape.spends as u64,
            ]
        }
        2 => {
            let per_commitment = u32::from(shape.note_commitment_rows.max(1));
            let output_index = local_row / per_commitment.max(1);
            [
                output_index as u64,
                (local_row % per_commitment.max(1)) as u64,
                shape.outputs as u64,
            ]
        }
        3 => {
            let per_range = u32::from(shape.range_check_rows.max(1));
            let range_index = local_row / per_range.max(1);
            [
                range_index as u64,
                (local_row % per_range.max(1)) as u64,
                shape.amount_range_checks_64 as u64,
            ]
        }
        4 => {
            let per_ownership = u32::from(shape.ownership_rows.max(1));
            let ownership_index = local_row / per_ownership.max(1);
            [
                ownership_index as u64,
                (local_row % per_ownership.max(1)) as u64,
                shape.ownership_checks as u64,
            ]
        }
        5 => {
            let per_balance = u32::from(shape.balance_rows.max(1));
            let balance_index = local_row / per_balance.max(1);
            [
                balance_index as u64,
                (local_row % per_balance.max(1)) as u64,
                shape.balance_constraints as u64,
            ]
        }
        6 => {
            let per_lookup = u32::from(shape.lookup_rows.max(1));
            let lookup_index = local_row / per_lookup.max(1);
            [
                lookup_index as u64,
                (local_row % per_lookup.max(1)) as u64,
                shape.lookup_arguments as u64,
            ]
        }
        _ => [
            local_row as u64,
            bucket_len as u64,
            shape.boundary_constraint_groups as u64,
        ],
    }
}

fn phase2_whir_opening_row(
    row_index: u32,
    bucket_start: u32,
    bucket_len: u32,
    round_index: u64,
    query_ordinal: u64,
    slot: usize,
    ood_samples: u16,
) -> u32 {
    let offset = (mix64(
        row_index as u64
            ^ round_index.rotate_left(11)
            ^ query_ordinal.rotate_left(23)
            ^ (slot as u64).rotate_left(31)
            ^ u64::from(ood_samples).rotate_left(7),
    ) % u64::from(bucket_len.max(1))) as u32;
    bucket_start + offset
}

fn phase2_whir_selector_axes(
    shape: Phase2WhirStatementShape,
    bucket_index: usize,
    query_ordinal: u64,
    round_index: u64,
    slot: usize,
) -> [u64; 3] {
    [
        bucket_index as u64,
        (slot as u64 + query_ordinal) % u64::from(shape.boundary_constraint_groups.max(1)),
        round_index ^ (shape.lookup_arguments as u64),
    ]
}

fn phase2_whir_fold_payload(
    plan: Phase2WhirQueryPlan,
    round_index: u64,
    query_ordinal: u64,
    row_index: u64,
    semantic_axes: [u64; 3],
) -> [M31; PHASE2_WHIR_FOLD_VALUES] {
    let mut out = [M31::ZERO; PHASE2_WHIR_FOLD_VALUES];
    for (vertex, slot) in out.iter_mut().enumerate() {
        let axes = [
            semantic_axes[0] + u64::from((vertex & 1) as u8),
            semantic_axes[1] + u64::from(((vertex >> 1) & 1) as u8),
            semantic_axes[2] + u64::from(((vertex >> 2) & 1) as u8),
        ];
        *slot = phase2_whir_semantic_m31(
            plan,
            0x4000 + vertex as u64,
            round_index,
            query_ordinal,
            row_index,
            axes,
        );
    }
    out
}

fn phase2_whir_numerator_coeffs(
    plan: Phase2WhirQueryPlan,
    round_index: u64,
    query_ordinal: u64,
    row_index: u64,
    semantic_axes: [u64; 3],
) -> [M31; PHASE2_WHIR_NUMERATOR_COEFFS] {
    let mut out = [M31::ZERO; PHASE2_WHIR_NUMERATOR_COEFFS];
    for (index, slot) in out.iter_mut().enumerate() {
        *slot = phase2_whir_semantic_m31(
            plan,
            0x5000 + index as u64,
            round_index,
            query_ordinal,
            row_index,
            [
                semantic_axes[0],
                semantic_axes[1] + index as u64,
                semantic_axes[2] ^ u64::from(plan.statement_shape.application_hash_gadgets),
            ],
        );
    }
    out
}

fn phase2_whir_selector_weights(
    plan: Phase2WhirQueryPlan,
    round_index: u64,
    query_ordinal: u64,
    row_index: u64,
    semantic_axes: [u64; 3],
) -> [M31; PHASE2_WHIR_SELECTOR_TERMS] {
    let mut out = [M31::ZERO; PHASE2_WHIR_SELECTOR_TERMS];
    for (index, slot) in out.iter_mut().enumerate() {
        *slot = phase2_whir_semantic_nonzero_m31(
            plan,
            0x6000 + index as u64,
            round_index,
            query_ordinal,
            row_index,
            [
                semantic_axes[0] + index as u64,
                u64::from(plan.statement_shape.boundary_constraint_groups),
                u64::from(plan.statement_shape.lookup_arguments),
            ],
        );
    }
    out
}

fn phase2_whir_semantic_cm31(
    plan: Phase2WhirQueryPlan,
    tag: u64,
    round_index: u64,
    query_ordinal: u64,
    row_index: u64,
    semantic_axes: [u64; 3],
) -> Cm31 {
    Cm31::new(
        phase2_whir_semantic_m31(
            plan,
            tag,
            round_index,
            query_ordinal,
            row_index,
            semantic_axes,
        ),
        phase2_whir_semantic_m31(
            plan,
            tag ^ 0x9e37_79b9,
            round_index,
            query_ordinal,
            row_index,
            [semantic_axes[2], semantic_axes[0], semantic_axes[1]],
        ),
    )
}

fn phase2_whir_semantic_nonzero_cm31(
    plan: Phase2WhirQueryPlan,
    tag: u64,
    round_index: u64,
    query_ordinal: u64,
    row_index: u64,
    semantic_axes: [u64; 3],
) -> Cm31 {
    Cm31::new(
        phase2_whir_semantic_nonzero_m31(
            plan,
            tag,
            round_index,
            query_ordinal,
            row_index,
            semantic_axes,
        ),
        phase2_whir_semantic_nonzero_m31(
            plan,
            tag ^ 0x7f4a_7c15,
            round_index,
            query_ordinal,
            row_index,
            [semantic_axes[1], semantic_axes[2], semantic_axes[0]],
        ),
    )
}

fn phase2_whir_semantic_m31(
    plan: Phase2WhirQueryPlan,
    tag: u64,
    round_index: u64,
    query_ordinal: u64,
    row_index: u64,
    semantic_axes: [u64; 3],
) -> M31 {
    sample_m31(phase2_whir_semantic_seed(
        plan,
        tag,
        round_index,
        query_ordinal,
        row_index,
        semantic_axes,
    ))
}

fn phase2_whir_semantic_nonzero_m31(
    plan: Phase2WhirQueryPlan,
    tag: u64,
    round_index: u64,
    query_ordinal: u64,
    row_index: u64,
    semantic_axes: [u64; 3],
) -> M31 {
    sample_nonzero_m31(phase2_whir_semantic_seed(
        plan,
        tag,
        round_index,
        query_ordinal,
        row_index,
        semantic_axes,
    ))
}

fn phase2_whir_semantic_seed(
    plan: Phase2WhirQueryPlan,
    tag: u64,
    round_index: u64,
    query_ordinal: u64,
    row_index: u64,
    semantic_axes: [u64; 3],
) -> u64 {
    let digest = phase2_whir_statement_digest(plan);
    let mut lo = [0_u8; 8];
    lo.copy_from_slice(&digest[0..8]);
    let mut hi = [0_u8; 8];
    hi.copy_from_slice(&digest[8..16]);
    let digest_lo = u64::from_le_bytes(lo);
    let digest_hi = u64::from_le_bytes(hi);
    let mut value = tag
        ^ plan.query_schedule_seed.rotate_left(17)
        ^ plan.statement_seed.rotate_right(9)
        ^ round_index.rotate_left(29)
        ^ query_ordinal.rotate_left(41)
        ^ row_index.rotate_left(11)
        ^ digest_lo
        ^ digest_hi.rotate_left(7);
    for axis in semantic_axes {
        value = mix64(value ^ axis.rotate_left(13));
    }
    mix64(value ^ u64::from(plan.statement_shape.total_rows))
}

fn push_query_record(
    out: &mut Vec<u8>,
    record: QueryRecord,
    fold_mode: WhirFoldMode,
    fold_arity: usize,
) {
    let mut payload = record.fold_payload;
    if matches!(fold_mode, WhirFoldMode::LocalInterpolant) {
        let mut counters = Phase2Counters::default();
        payload = [
            payload[0],
            payload[1].sub(payload[0], &mut counters),
            payload[2].sub(payload[0], &mut counters),
            payload[3]
                .sub(payload[1], &mut counters)
                .sub(payload[2], &mut counters)
                .add(payload[0], &mut counters),
        ];
    }
    let _ = fold_arity;
    for word in [
        record.x.c0.as_u32(),
        record.x.c1.as_u32(),
        record.z0.c0.as_u32(),
        record.z0.c1.as_u32(),
        record.z1.c0.as_u32(),
        record.z1.c1.as_u32(),
        payload[0].as_u32(),
        payload[1].as_u32(),
        payload[2].as_u32(),
        payload[3].as_u32(),
    ] {
        out.extend_from_slice(&word.to_le_bytes());
    }
}

fn push_whir_query_record(
    out: &mut Vec<u8>,
    record: WhirQueryRecord,
    fold_mode: WhirFoldMode,
    precompute_mode: WhirQueryPrecomputeMode,
) {
    let fold_payload = match fold_mode {
        WhirFoldMode::RawFibers => record.fold_payload,
        WhirFoldMode::LocalInterpolant => multilinear_to_local_interpolant(record.fold_payload),
    };
    out.extend_from_slice(&record.x.c0.as_u32().to_le_bytes());
    out.extend_from_slice(&record.x.c1.as_u32().to_le_bytes());
    for point in &record.openings {
        out.extend_from_slice(&point.c0.as_u32().to_le_bytes());
        out.extend_from_slice(&point.c1.as_u32().to_le_bytes());
    }
    for point in &record.selectors {
        out.extend_from_slice(&point.c0.as_u32().to_le_bytes());
        out.extend_from_slice(&point.c1.as_u32().to_le_bytes());
    }
    for value in fold_payload {
        out.extend_from_slice(&value.as_u32().to_le_bytes());
    }
    for value in record.numerator_coeffs {
        out.extend_from_slice(&value.as_u32().to_le_bytes());
    }
    for value in record.selector_weights {
        out.extend_from_slice(&value.as_u32().to_le_bytes());
    }
    if matches!(
        precompute_mode,
        WhirQueryPrecomputeMode::ProofCarriedRoundLocal
    ) {
        out.extend_from_slice(&record.precomputed.numerator_eval.as_u32().to_le_bytes());
        out.extend_from_slice(
            &record
                .precomputed
                .selector_affine_term
                .as_u32()
                .to_le_bytes(),
        );
        out.extend_from_slice(
            &record
                .precomputed
                .selector_weight_sum
                .as_u32()
                .to_le_bytes(),
        );
        out.extend_from_slice(&record.precomputed.opening_denom.c0.as_u32().to_le_bytes());
        out.extend_from_slice(&record.precomputed.opening_denom.c1.as_u32().to_le_bytes());
        out.extend_from_slice(&record.precomputed.selector_denom.c0.as_u32().to_le_bytes());
        out.extend_from_slice(&record.precomputed.selector_denom.c1.as_u32().to_le_bytes());
    }
}

fn multilinear_to_local_interpolant(
    values: [M31; PHASE2_WHIR_FOLD_VALUES],
) -> [M31; PHASE2_WHIR_FOLD_VALUES] {
    let mut coeffs = values;
    let mut counters = Phase2Counters::default();
    for bit in 0..3 {
        for mask in 0..PHASE2_WHIR_FOLD_VALUES {
            if (mask & (1 << bit)) != 0 {
                coeffs[mask] = coeffs[mask].sub(coeffs[mask ^ (1 << bit)], &mut counters);
            }
        }
    }
    coeffs
}

fn seeded_cm31(seed: u64) -> Cm31 {
    let mut value = Cm31::new(
        sample_nonzero_m31(seed),
        sample_nonzero_m31(seed.rotate_left(13)),
    );
    let config = Phase2ExtensionConfig {
        base: Phase2ArithmeticConfig::new(
            ArithmeticKernelId::DirectM31,
            ReductionMode::DirectM31,
            LazyReductionMode::None,
        ),
        extension_kernel_id: ExtensionKernelId::Schoolbook,
    };
    let mut counters = Phase2Counters::default();
    let a2 = value.c0.square(config.base, &mut counters);
    let b2 = value.c1.square(config.base, &mut counters);
    if a2.add(b2, &mut counters).as_u32() == 0 {
        value.c1 = value.c1.add(M31::ONE, &mut counters);
    }
    value
}

fn seeded_qm31(seed: u64) -> Qm31 {
    let mut value = Qm31::new(seeded_cm31(seed), seeded_cm31(seed.rotate_left(29)));
    let config = Phase2ExtensionConfig {
        base: Phase2ArithmeticConfig::new(
            ArithmeticKernelId::DirectM31,
            ReductionMode::DirectM31,
            LazyReductionMode::None,
        ),
        extension_kernel_id: ExtensionKernelId::Schoolbook,
    };
    let mut counters = Phase2Counters::default();
    let a2 = value.c0.square(config, &mut counters);
    let b2 = value.c1.square(config, &mut counters);
    let denom = a2.sub(
        b2.mul(non_residue_cm31(), config, &mut counters),
        &mut counters,
    );
    if denom.c0.as_u32() == 0 && denom.c1.as_u32() == 0 {
        value.c1 = value.c1.add(Cm31::from_base(M31::ONE), &mut counters);
    }
    value
}

fn sample_m31(seed: u64) -> M31 {
    M31::new_lossy(mix64(seed) & 0x7fff_ffff)
}

fn sample_nonzero_m31(seed: u64) -> M31 {
    let value = sample_m31(seed);
    if value.as_u32() == 0 {
        M31::ONE
    } else {
        value
    }
}

fn fold_qm31(value: Qm31) -> u32 {
    value.c0.c0.as_u32()
        ^ value.c0.c1.as_u32().rotate_left(3)
        ^ value.c1.c0.as_u32().rotate_left(9)
        ^ value.c1.c1.as_u32().rotate_left(17)
}

fn checked_m31(value: u32) -> Result<M31, &'static str> {
    M31::new(value).ok_or("non-canonical m31 encoding")
}

fn read_cm31(bytes: &[u8], cursor: &mut usize) -> Result<Cm31, &'static str> {
    let c0 = checked_m31(read_u32(bytes, *cursor)?)?;
    *cursor += 4;
    let c1 = checked_m31(read_u32(bytes, *cursor)?)?;
    *cursor += 4;
    Ok(Cm31::new(c0, c1))
}

fn read_whir_query_record(
    bytes: &[u8],
    offset: usize,
    precompute_mode: WhirQueryPrecomputeMode,
) -> Result<WhirQueryRecord, &'static str> {
    let mut cursor = offset;
    let x = read_cm31(bytes, &mut cursor)?;
    let mut openings = [Cm31::from_base(M31::ZERO); PHASE2_WHIR_MAX_OPENING_TERMS];
    for slot in &mut openings {
        *slot = read_cm31(bytes, &mut cursor)?;
    }
    let mut selectors = [Cm31::from_base(M31::ZERO); PHASE2_WHIR_SELECTOR_TERMS];
    for slot in &mut selectors {
        *slot = read_cm31(bytes, &mut cursor)?;
    }
    let mut fold_payload = [M31::ZERO; PHASE2_WHIR_FOLD_VALUES];
    for slot in &mut fold_payload {
        *slot = checked_m31(read_u32(bytes, cursor)?)?;
        cursor += 4;
    }
    let mut numerator_coeffs = [M31::ZERO; PHASE2_WHIR_NUMERATOR_COEFFS];
    for slot in &mut numerator_coeffs {
        *slot = checked_m31(read_u32(bytes, cursor)?)?;
        cursor += 4;
    }
    let mut selector_weights = [M31::ZERO; PHASE2_WHIR_SELECTOR_TERMS];
    for slot in &mut selector_weights {
        *slot = checked_m31(read_u32(bytes, cursor)?)?;
        cursor += 4;
    }
    let precomputed = if matches!(
        precompute_mode,
        WhirQueryPrecomputeMode::ProofCarriedRoundLocal
    ) {
        let numerator_eval = checked_m31(read_u32(bytes, cursor)?)?;
        cursor += 4;
        let selector_affine_term = checked_m31(read_u32(bytes, cursor)?)?;
        cursor += 4;
        let selector_weight_sum = checked_m31(read_u32(bytes, cursor)?)?;
        cursor += 4;
        let opening_denom = read_cm31(bytes, &mut cursor)?;
        let selector_denom = read_cm31(bytes, &mut cursor)?;
        WhirQueryPrecomputed {
            numerator_eval,
            selector_affine_term,
            selector_weight_sum,
            opening_denom,
            selector_denom,
        }
    } else {
        whir_zero_query_precomputed()
    };
    Ok(WhirQueryRecord {
        x,
        openings,
        selectors,
        fold_payload,
        numerator_coeffs,
        selector_weights,
        precomputed,
    })
}

fn read_whir_sumcheck_record(
    bytes: &[u8],
    offset: usize,
) -> Result<WhirSumcheckRecord, &'static str> {
    Ok(WhirSumcheckRecord {
        c0: checked_m31(read_u32(bytes, offset)?)?,
        c_inf: checked_m31(read_u32(bytes, offset + 4)?)?,
        nonce: read_u64(bytes, offset + 8)?,
    })
}

fn digest_word_to_m31(bytes: &[u8]) -> M31 {
    let mut raw = [0_u8; 4];
    raw.copy_from_slice(bytes);
    M31::new_lossy(u32::from_le_bytes(raw) as u64)
}

fn read_u16(bytes: &[u8], offset: usize) -> Result<u16, &'static str> {
    if offset + 2 > bytes.len() {
        return Err("phase2 proof read overflow");
    }
    let mut raw = [0_u8; 2];
    raw.copy_from_slice(&bytes[offset..offset + 2]);
    Ok(u16::from_le_bytes(raw))
}

fn read_u32(bytes: &[u8], offset: usize) -> Result<u32, &'static str> {
    if offset + 4 > bytes.len() {
        return Err("phase2 proof read overflow");
    }
    let mut raw = [0_u8; 4];
    raw.copy_from_slice(&bytes[offset..offset + 4]);
    Ok(u32::from_le_bytes(raw))
}

fn read_u64(bytes: &[u8], offset: usize) -> Result<u64, &'static str> {
    if offset + 8 > bytes.len() {
        return Err("phase2 proof read overflow");
    }
    let mut raw = [0_u8; 8];
    raw.copy_from_slice(&bytes[offset..offset + 8]);
    Ok(u64::from_le_bytes(raw))
}

fn mix64(mut value: u64) -> u64 {
    value ^= value >> 30;
    value = value.wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value ^= value >> 27;
    value = value.wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

fn m31_reduce_reference(value: u64) -> u32 {
    (value % M31_MODULUS_U64) as u32
}

// p = 2^31 - 1, so x mod p = (x_lo + x_hi) mod p with x = x_lo + 2^31 * x_hi.
// For a raw multiplication x < p^2 < 2^62, two folds are sufficient; for batched lazy sums
// we keep folding until the accumulator is below 2p and then normalize once.
fn m31_reduce_direct(value: u64) -> u32 {
    let mut folded = value;
    while folded > (M31_MODULUS_U64 << 1) {
        folded = (folded & M31_MODULUS_U64) + (folded >> 31);
    }
    if folded >= M31_MODULUS_U64 {
        folded -= M31_MODULUS_U64;
    }
    if folded >= M31_MODULUS_U64 {
        folded -= M31_MODULUS_U64;
    }
    folded as u32
}

fn m31_reduce_barrett(value: u64) -> u32 {
    let q = ((value as u128 * M31_BARRETT_MU as u128) >> 64) as u64;
    let mut r = value.saturating_sub(q.saturating_mul(M31_MODULUS_U64));
    while r >= M31_MODULUS_U64 {
        r -= M31_MODULUS_U64;
    }
    r as u32
}

fn m31_to_montgomery(value: u32) -> u32 {
    let doubled = (value as u64) << 1;
    if doubled >= M31_MODULUS_U64 {
        (doubled - M31_MODULUS_U64) as u32
    } else {
        doubled as u32
    }
}

fn m31_from_montgomery(value: u32) -> u32 {
    montgomery_reduce(value as u64)
}

fn montgomery_reduce(value: u64) -> u32 {
    let m = (value as u32).wrapping_mul(M31_MONT_N_INV) as u64;
    let t = (value + m * M31_MODULUS_U64) >> 32;
    let mut out = t as u32;
    if out >= M31_MODULUS {
        out -= M31_MODULUS;
    }
    out
}

fn m31_mul_montgomery(lhs: u32, rhs: u32) -> u32 {
    let lhs_m = m31_to_montgomery(lhs);
    let rhs_m = m31_to_montgomery(rhs);
    let product_m = montgomery_reduce(lhs_m as u64 * rhs_m as u64);
    m31_from_montgomery(product_m)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn random_word(mut state: u64) -> u64 {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        state
    }

    #[test]
    fn direct_reduction_matches_reference() {
        let mut state = 1_u64;
        for _ in 0..10_000 {
            state = random_word(state);
            let a = state & ((1_u64 << 31) - 1);
            state = random_word(state);
            let b = state & ((1_u64 << 31) - 1);
            let product = a * b;
            assert_eq!(m31_reduce_direct(product), m31_reduce_reference(product));
            assert_eq!(m31_reduce_barrett(product), m31_reduce_reference(product));
        }
    }

    #[test]
    fn montgomery_matches_reference() {
        let mut state = 7_u64;
        for _ in 0..10_000 {
            state = random_word(state);
            let a = (state & ((1_u64 << 31) - 2)) as u32;
            state = random_word(state);
            let b = (state & ((1_u64 << 31) - 2)) as u32;
            assert_eq!(
                m31_mul_montgomery(a, b),
                m31_reduce_reference(a as u64 * b as u64)
            );
        }
    }

    #[test]
    fn batch4_bounds_hold() {
        let max_term = (M31_MODULUS_U64 - 1) * (M31_MODULUS_U64 - 1);
        let sum = max_term * 4;
        assert!(sum < u64::MAX);
    }

    #[test]
    fn proof_round_trip_for_fold_modes() {
        let plan = Phase2ProofPlan {
            query_count: 4,
            fold_arity: 4,
            merkle_depth: 16,
            merkle_paths: 8,
            target_proof_bytes: 5120,
            query_schedule_seed: 17,
            statement_seed: 29,
        };
        for mode in [WhirFoldMode::RawFibers, WhirFoldMode::LocalInterpolant] {
            let proof = build_phase2_proof_bytes(plan, mode);
            let view = Phase2ProofView::parse(&proof).unwrap();
            assert_eq!(view.fold_mode, mode);
            assert_eq!(view.query_count, 4);
            assert_eq!(view.merkle_depth, 16);
            assert_eq!(view.merkle_paths, 8);
            assert_eq!(proof.len(), 5120);
            assert!(view.query_record(3).is_ok());
        }
    }

    #[test]
    fn proof_rejects_noncanonical_values() {
        let plan = Phase2ProofPlan {
            query_count: 1,
            fold_arity: 4,
            merkle_depth: 8,
            merkle_paths: 4,
            target_proof_bytes: 512,
            query_schedule_seed: 3,
            statement_seed: 5,
        };
        let mut proof = build_phase2_proof_bytes(plan, WhirFoldMode::RawFibers);
        let offset = 68;
        proof[offset..offset + 4].copy_from_slice(&M31_MODULUS.to_le_bytes());
        let view = Phase2ProofView::parse(&proof).unwrap();
        assert!(view.query_record(0).is_err());
    }

    #[test]
    fn skeleton_modes_agree_on_local_eval() {
        let plan = Phase2ProofPlan {
            query_count: 4,
            fold_arity: 4,
            merkle_depth: 16,
            merkle_paths: 8,
            target_proof_bytes: 4096,
            query_schedule_seed: 11,
            statement_seed: 13,
        };
        let raw = build_phase2_proof_bytes(plan, WhirFoldMode::RawFibers);
        let local = build_phase2_proof_bytes(plan, WhirFoldMode::LocalInterpolant);
        let raw_view = Phase2ProofView::parse(&raw).unwrap();
        let local_view = Phase2ProofView::parse(&local).unwrap();
        let mut counters = Phase2Counters::default();
        let challenges = TranscriptChallenges {
            fold_r0: M31::new_lossy(7),
            fold_r1: M31::new_lossy(19),
            gamma: seeded_qm31(31),
        };
        for index in 0..plan.query_count as usize {
            let raw_eval = evaluate_fold(
                raw_view.query_record(index).unwrap().fold_payload,
                challenges.fold_r0,
                challenges.fold_r1,
                Phase2ArithmeticConfig::new(
                    ArithmeticKernelId::DirectM31,
                    ReductionMode::DirectM31,
                    LazyReductionMode::None,
                ),
                WhirFoldMode::RawFibers,
                &mut counters,
            );
            let local_eval = evaluate_fold(
                local_view.query_record(index).unwrap().fold_payload,
                challenges.fold_r0,
                challenges.fold_r1,
                Phase2ArithmeticConfig::new(
                    ArithmeticKernelId::DirectM31,
                    ReductionMode::DirectM31,
                    LazyReductionMode::None,
                ),
                WhirFoldMode::LocalInterpolant,
                &mut counters,
            );
            assert_eq!(raw_eval.as_u32(), local_eval.as_u32());
        }
    }

    #[test]
    fn whir_query_proof_round_trip_for_fold_modes() {
        let plan = Phase2WhirQueryPlan {
            round_count: 2,
            rounds: [
                Phase2WhirRoundPlan {
                    query_count: 7,
                    merkle_depth: 8,
                    ood_samples: 1,
                    opening_count: 2,
                    selector_count: 1,
                },
                Phase2WhirRoundPlan {
                    query_count: 5,
                    merkle_depth: 9,
                    ood_samples: 1,
                    opening_count: 3,
                    selector_count: 2,
                },
                Phase2WhirRoundPlan::default(),
                Phase2WhirRoundPlan::default(),
            ],
            statement_shape: Phase2WhirStatementShape {
                spends: 2,
                outputs: 2,
                note_tree_depth: 32,
                note_openings_per_spend: 1,
                nullifier_hashes_per_spend: 1,
                note_commitments_per_output: 1,
                amount_range_checks_64: 4,
                ownership_checks: 2,
                balance_constraints: 8,
                lookup_arguments: 3,
                boundary_constraint_groups: 4,
                application_merkle_paths: 2,
                application_hash_gadgets: 4,
                evaluation_domain_log2: 13,
                merkle_rows_per_level: 12,
                nullifier_hash_rows: 512,
                note_commitment_rows: 512,
                range_check_rows: 256,
                ownership_rows: 384,
                balance_rows: 48,
                lookup_rows: 320,
                misc_rows: 768,
                total_rows: 6720,
                row_breakdown: [768, 1024, 1024, 1024, 768, 384, 960, 768],
            },
            target_proof_bytes: 4096,
            query_schedule_seed: 17,
            statement_seed: 23,
        };
        for mode in [WhirFoldMode::RawFibers, WhirFoldMode::LocalInterpolant] {
            let proof = build_phase2_whir_query_proof_bytes(plan, mode);
            let view = Phase2WhirQueryView::parse(&proof).unwrap();
            assert_eq!(view.fold_mode, mode);
            assert_eq!(view.round_count, 2);
            assert_eq!(view.total_query_count(), 12);
            assert_eq!(view.round_plan(1).merkle_depth, 9);
            assert!(view.query_record(1, 4).is_ok());
            assert_eq!(proof.len(), 4096);
        }
    }

    #[test]
    fn whir_local_interpolant_matches_raw_multilinear_eval() {
        let raw = [
            M31::new_lossy(3),
            M31::new_lossy(5),
            M31::new_lossy(7),
            M31::new_lossy(11),
            M31::new_lossy(13),
            M31::new_lossy(17),
            M31::new_lossy(19),
            M31::new_lossy(23),
        ];
        let local = multilinear_to_local_interpolant(raw);
        let arithmetic = Phase2ArithmeticConfig::new(
            ArithmeticKernelId::DirectM31,
            ReductionMode::DirectM31,
            LazyReductionMode::None,
        );
        let mut counters = Phase2Counters::default();
        let challenges = [M31::new_lossy(29), M31::new_lossy(31), M31::new_lossy(37)];
        let raw_eval = evaluate_fold8(
            raw,
            challenges,
            arithmetic,
            WhirFoldMode::RawFibers,
            &mut counters,
        );
        let local_eval = evaluate_fold8(
            local,
            challenges,
            arithmetic,
            WhirFoldMode::LocalInterpolant,
            &mut counters,
        );
        assert_eq!(raw_eval.as_u32(), local_eval.as_u32());
    }

    fn transcript_test_plan() -> Phase2WhirTranscriptPlan {
        Phase2WhirTranscriptPlan {
            round_count: 1,
            rounds: [
                Phase2WhirTranscriptRoundPlan {
                    query_count: 11,
                    merkle_depth: 8,
                    ood_samples: 2,
                    opening_count: 3,
                    selector_count: 1,
                    pow_bits: 10,
                    sumcheck_rounds: 4,
                    folding_pow_bits: 9,
                },
                Phase2WhirTranscriptRoundPlan::default(),
                Phase2WhirTranscriptRoundPlan::default(),
                Phase2WhirTranscriptRoundPlan::default(),
            ],
            statement_shape: Phase2WhirStatementShape {
                spends: 2,
                outputs: 2,
                note_tree_depth: 32,
                note_openings_per_spend: 1,
                nullifier_hashes_per_spend: 1,
                note_commitments_per_output: 1,
                amount_range_checks_64: 4,
                ownership_checks: 2,
                balance_constraints: 8,
                lookup_arguments: 3,
                boundary_constraint_groups: 4,
                application_merkle_paths: 2,
                application_hash_gadgets: 4,
                evaluation_domain_log2: 13,
                merkle_rows_per_level: 12,
                nullifier_hash_rows: 512,
                note_commitment_rows: 512,
                range_check_rows: 256,
                ownership_rows: 384,
                balance_rows: 48,
                lookup_rows: 320,
                misc_rows: 768,
                total_rows: 6720,
                row_breakdown: [768, 1024, 1024, 1024, 768, 384, 960, 768],
            },
            target_proof_bytes: 8192,
            query_schedule_seed: 0x0f11_dbee_7bad_c0de,
            statement_seed: 0x52ee_d123_9abc_7711,
            commitment_ood_samples: 2,
            initial_sumcheck_rounds: 4,
            initial_folding_pow_bits: 8,
            final_query_count: 7,
            final_merkle_depth: 9,
            final_pow_bits: 11,
            final_sumcheck_rounds: 5,
            final_folding_pow_bits: 10,
        }
    }

    #[test]
    fn whir_transcript_proof_round_trip_for_fold_modes() {
        let config = Phase2VerifierConfig {
            arithmetic_kernel_id: ArithmeticKernelId::ReferenceCanonical,
            reduction_mode: ReductionMode::Canonical,
            lazy_reduction_mode: LazyReductionMode::None,
            extension_kernel_id: ExtensionKernelId::Karatsuba,
            lift_policy: LiftPolicy::LateLiftQm31,
            whir_fold_mode: WhirFoldMode::LocalInterpolant,
            merkle_proof_mode: MerkleProofMode::SeparatePaths,
            query_reuse_mode: WhirQueryReuseMode::PerQueryInversion,
            query_precompute_mode: WhirQueryPrecomputeMode::None,
        };
        for merkle_mode in [
            MerkleProofMode::SeparatePaths,
            MerkleProofMode::MinimalSubtree,
        ] {
            for mode in [WhirFoldMode::RawFibers, WhirFoldMode::LocalInterpolant] {
                let mut mode_config = config;
                mode_config.whir_fold_mode = mode;
                mode_config.merkle_proof_mode = merkle_mode;
                let proof = build_phase2_whir_transcript_proof_bytes(
                    transcript_test_plan(),
                    mode,
                    merkle_mode,
                );
                let view =
                    Phase2WhirTranscriptView::parse(&proof, config.query_precompute_mode).unwrap();
                assert_eq!(view.fold_mode, mode);
                assert_eq!(view.round_count, 1);
                assert_eq!(view.commitment_ood_count(), 2);
                assert_eq!(view.final_query_count(), 7);
                assert_eq!(proof.len(), 8192);
                let outcome = run_phase2_whir_transcript_verify(
                    mode_config,
                    &proof,
                    1,
                    WhirTranscriptTraceMode::Disabled,
                );
                assert!(outcome.is_ok(), "{outcome:?}");
            }
        }
    }

    #[test]
    fn whir_merkle_payload_round_trip_for_formats() {
        let base_config = Phase2VerifierConfig {
            arithmetic_kernel_id: ArithmeticKernelId::ReferenceCanonical,
            reduction_mode: ReductionMode::Canonical,
            lazy_reduction_mode: LazyReductionMode::None,
            extension_kernel_id: ExtensionKernelId::Karatsuba,
            lift_policy: LiftPolicy::LateLiftQm31,
            whir_fold_mode: WhirFoldMode::LocalInterpolant,
            merkle_proof_mode: MerkleProofMode::SeparatePaths,
            query_reuse_mode: WhirQueryReuseMode::PerQueryInversion,
            query_precompute_mode: WhirQueryPrecomputeMode::None,
        };
        for merkle_mode in [
            MerkleProofMode::SeparatePaths,
            MerkleProofMode::MinimalSubtree,
        ] {
            for payload_format in [
                WhirMerklePayloadFormat::FlatNodes,
                WhirMerklePayloadFormat::CanonicalPayload,
            ] {
                let mut config = base_config;
                config.merkle_proof_mode = merkle_mode;
                let payload = build_phase2_whir_merkle_payload_bytes(
                    transcript_test_plan(),
                    merkle_mode,
                    payload_format,
                );
                let outcome = run_phase2_whir_merkle_payload_parse(
                    config,
                    transcript_test_plan(),
                    &payload,
                    payload_format,
                    1,
                );
                assert!(outcome.is_ok(), "{outcome:?}");

                let mut truncated = payload.clone();
                truncated.truncate(truncated.len().saturating_sub(1));
                let truncated_outcome = run_phase2_whir_merkle_payload_parse(
                    config,
                    transcript_test_plan(),
                    &truncated,
                    payload_format,
                    1,
                );
                assert!(truncated_outcome.is_err(), "{truncated_outcome:?}");
            }
        }
    }
}
